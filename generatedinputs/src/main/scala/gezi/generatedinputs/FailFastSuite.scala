package gezi.generatedinputs

import java.util.concurrent.Executors
import java.util.concurrent.ScheduledThreadPoolExecutor
import java.util.concurrent.ThreadFactory
import java.util.concurrent.TimeUnit
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.concurrent.duration.MILLISECONDS
import scala.concurrent.duration.SECONDS

/** The base of every test suite of this build: munit's `FunSuite` whose test
  * bodies run on a daemon thread of their own, so that the timeout of a test
  * is enforced, a stop is requested on a signal the body can read when the
  * deadline passes, and the next test starts.
  *
  * Why: munit 1.3.6 neither stops nor interrupts a body. On a timeout
  * `munit.internal.PlatformCompat.waitAtMost` only fails the test's promise,
  * and under munit's default parasitic execution context a synchronous body
  * runs on the thread that waits for it, so it is not even reported until it
  * returns (https://github.com/scalameta/munit/issues/730). A body that did
  * not return held the suite, and ParallelSetLawTest ran two hours under
  * munit's 30 s default on 2026-11-13. So every test has a default deadline
  * of a few seconds, and a slow test fails fast unless there is a good
  * reason (`CONTRIBUTING.md`, "Tests fail fast"). The suites handle munit's
  * timeout themselves, by portable cooperative cancellation that the
  * CPU-intensive computations check at chosen points, never by
  * `Thread.interrupt`, and nothing goes around munit: nothing here kills the
  * test process, halts its JVM or interrupts a thread.
  *
  * How: a test transform runs each body through `FailFastSuite.bounded`, on a
  * pooled platform daemon thread, with a fresh write-once `Promise[Unit]`.
  * At the deadline the runner completes the promise (a stop request) and
  * fails the test with a `TestDeadlineExceeded`. A test written with
  * `stoppableTest` receives that promise's read-only future and hands
  * `gezi.saturation.StopSignal.completedWith(stopped)` to the computations it
  * runs, which stop at their next check and give what they have
  * (`StopSignal`'s meaning is unchanged). `generatedinputs` depends on no
  * module (sbt rejects the cycle), so it names the future and not
  * `StopSignal`. A computation that reads no signal keeps running on its
  * daemon thread until the forked test JVM exits: the JVM cannot stop a
  * thread that does not cooperate.
  *
  * The threads are platform threads, not virtual ones: a virtual thread
  * yields its carrier only at blocking points, so a leaked CPU bound body
  * (evaluation, saturation, extraction) holds its carrier indefinitely; and
  * the carrier pool's parallelism equals the available processors, which is 2
  * under the build's `taskset` pinning, so two leaked bodies would starve the
  * body of every later test. Platform daemon threads are time sliced by the
  * operating system, so later tests still run, only slower. Daemon threads
  * so that a leaked body does not keep the forked test JVM from exiting. A
  * body's thread has the JVM's default stack size, as the framework's own
  * test thread had.
  *
  * Tests are timed without their shared fixtures. A fixture is a value
  * several tests of a suite share, usually a lazy value that compiles or
  * loads something (the compiled natives of NativeInstructionsLawTest took about
  * 6.2 s, the preset of FixedWidthTypingLawTest about 13.5 s, measured on
  * 2026-11-14). Within one JVM per project such a lazy value is
  * shared across suites, so whichever test touched it first would overrun the
  * per-test deadline, depending on run order. A suite lists its shared
  * fixtures in `sharedFixtures`; `beforeAll` forces them, outside the
  * per-test timeout, so that each suite forces what it uses before its first
  * test and the run order does not matter. The forcing has its own bound,
  * `fixtureTimeout`, enforced the same way (a fresh promise per fixture,
  * completed at the deadline, the suite failing when it overruns). A fixture
  * is not made shorter by this: it is only not charged to a test.
  *
  * The default timeout is 3 seconds. Measured on 2026-11-16 over the 1191
  * tests of every project, with every body running and every deadline
  * (the default, the fixtures' and each suite's) raised to 600 s, on 2 CPUs
  * (contest-lean.slice, CPUs 10 and 11) at nice 10, the 1-minute load 9 to
  * 22: the median test takes 0.16 s, the 90th percentile 3.17 s, the 95th
  * 7.5 s and the 99th 38 s; 165 tests took more than 2 s, 127 more than 3 s,
  * 47 more than 10 s and 6 more than 60 s. A test that needs longer
  * overrides `munitTimeout` at its site with its measured time and the
  * reason (CONTRIBUTING.md, "Tests fail fast").
  *
  * THE RUN BUDGET. A server for short tasks bounds a whole test command, not
  * only each test: a run on such a server is for debugging, about 15 s, and
  * never the whole build's tests. When the test JVM has `-Dgezi.test.runBudget`
  * (a duration, such as `15s`) and `-Dgezi.test.runStarted` (the epoch
  * milliseconds at which the command's tests started), which the build passes
  * only when the server itself was started with `-Dgezi.testRunBudget`
  * (project/TestHeap.scala; the test JVM's names differ from the server's, so
  * that a JVM given the server's property alone has no budget), each test and
  * each fixture is bounded by the
  * smaller of its own deadline and what is left of the budget: one that
  * starts after the budget is spent fails at once with a
  * `TestRunBudgetSpent`, and one still running when it is spent is stopped
  * through its stop promise like any overrun. The start is the command's,
  * one for every project it runs, not the JVM's, since one test worker may
  * serve several commands; compiling in the same command counts against the
  * budget. Without the property there is no budget.
  */
abstract class FailFastSuite extends munit.FunSuite:

  override val munitTimeout: Duration = Duration(3, SECONDS)

  /** The suite's shared fixtures, each a thunk that forces one (for a lazy
    * value `fixture`, `_ => fixture`). They are forced in `beforeAll`, so
    * that no test is charged for them.
    */
  def sharedFixtures: Vector[Future[Unit] => Any] = Vector.empty

  /** The bound of forcing one shared fixture. Measured on
    * 2026-11-14: the slowest fixture, the fixed width preset of
    * FixedWidthTypingLawTest with its round options, takes about 13.5 s;
    * the compiled natives of NativeInstructionsLawTest 6.2 s and its native route
    * schedule 5.3 s. 13.5 s rounded up to 15 s.
    */
  val fixtureTimeout: Duration = Duration(15, SECONDS)

  override def beforeAll(): Unit =
    super.beforeAll()
    sharedFixtures.foreach(fixture =>
      Await.result(
        FailFastSuite.boundedInRun(fixtureTimeout, Promise[Unit]())(() => FailFastSuite.Stoppable(fixture)),
        Duration.Inf
      )
    )

  override def munitTestTransforms: List[TestTransform] =
    super.munitTestTransforms :+ new TestTransform(
      "fail fast",
      test => test.withBody(() => FailFastSuite.boundedInRun(munitTimeout, Promise[Unit]())(test.body))
    )

  /** A test whose body receives the stop request of its deadline: a read-only future
    * that the runner completes when the test overruns, for
    * `StopSignal.completedWith`; the body cannot complete it itself.
    */
  def stoppableTest(name: String)(body: Future[Unit] => Any)(using munit.Location): Unit =
    test(name)(FailFastSuite.Stoppable(body))

/** The failure of a test whose body did not return within its deadline. */
final class TestDeadlineExceeded(message: String) extends RuntimeException(message)

/** The failure of a test that started after its command's run budget was spent. */
final class TestRunBudgetSpent(message: String) extends RuntimeException(message)

/** A command's run budget: its tests' start in epoch milliseconds and the
  * time they may take together.
  */
final case class RunBudget(startedMillis: Long, budget: Duration):

  /** The milliseconds left of the budget at `nowMillis`, negative once spent. */
  def remainingMillis(nowMillis: Long): Long = startedMillis + budget.toMillis - nowMillis

object RunBudget:

  /** The budget the two properties give: none when `gezi.test.runBudget` is
    * absent. Throws `IllegalArgumentException` when the budget is given
    * without its start, or is no finite positive duration.
    */
  def fromProperties(budget: Option[String], started: Option[String]): Option[RunBudget] =
    budget.map { text =>
      val duration = Duration(text)
      if !duration.isFinite || duration.toMillis <= 0 then
        throw IllegalArgumentException(s"gezi.test.runBudget is $text, not a finite positive duration")
      val startedMillis = started
        .flatMap(_.toLongOption)
        .getOrElse(throw IllegalArgumentException(s"gezi.test.runBudget is $text but gezi.test.runStarted is $started"))
      RunBudget(startedMillis, duration)
    }

object FailFastSuite:

  /** The run budget of this test JVM, from its system properties. */
  val runBudget: Option[RunBudget] =
    RunBudget.fromProperties(sys.props.get("gezi.test.runBudget"), sys.props.get("gezi.test.runStarted"))

  /** `bounded` under the run budget: the timeout is the smaller of the given
    * one and what is left of the budget; when nothing is left the outcome
    * fails at once with a `TestRunBudgetSpent` and the body does not run.
    */
  def boundedInRun(timeout: Duration, stop: Promise[Unit])(body: () => Any): Future[Any] =
    boundedUnder(runBudget, System.currentTimeMillis, timeout, stop)(body)

  /** `boundedInRun` under the given budget, at the given time. */
  def boundedUnder(budget: Option[RunBudget], nowMillis: Long, timeout: Duration, stop: Promise[Unit])(
      body: () => Any
  ): Future[Any] =
    budget match
      case None => bounded(timeout, stop)(body)
      case Some(run) =>
        val remaining = run.remainingMillis(nowMillis)
        if remaining <= 0 then
          Future.failed(
            TestRunBudgetSpent(
              s"the run budget of ${run.budget} (-Dgezi.testRunBudget, the short-task server) is spent; run this test on the long-task server"
            )
          )
        else if remaining < timeout.toMillis then bounded(Duration(remaining, MILLISECONDS), stop)(body)
        else bounded(timeout, stop)(body)

  /** The value a `stoppableTest` body evaluates to: the runner, which owns
    * the test's promise, applies it on the body's thread.
    */
  final case class Stoppable(body: Future[Unit] => Any)

  /** Runs the body on a pooled platform daemon thread and gives its outcome
    * as a future; when the deadline passes before the body has returned, the
    * stop promise is completed, the future fails with a `TestDeadlineExceeded`,
    * and nothing else is done to the thread (no interrupt). A body that
    * evaluates to a `Stoppable`, or to a future of one, as munit's `test`
    * gives it, is applied to the stop promise; a future the body returns is
    * awaited on the body's thread, and a future the `Stoppable` returns is
    * not, the outcome completing with that one.
    *
    * The pool and the scheduler are mutable runtime objects, an exception to
    * the immutability rule (`CONTRIBUTING.md`, "Tests fail fast"), its
    * justification quoted at each `@SuppressWarnings` site below, with
    * scalameta/munit#730 as its ground.
    */
  @SuppressWarnings(Array("gezi.warts.NoJavaUtilConcurrent")) // "好的，用这个办法修，Scaladoc中cite #730作为依据" (the user, 2026-11-14)
  def bounded(timeout: Duration, stop: Promise[Unit])(body: () => Any): Future[Any] =
    val outcome = Promise[Any]()
    bodyPool.execute(new Runnable:
      def run(): Unit =
        try
          // munit's `test` gives every body as a future of its value
          // (`FunSuite.test`: `() => waitForCompletion(() =>
          // munitValueTransform(body))`), so a `stoppableTest`'s `Stoppable`
          // arrives inside a future: it is awaited here, on the body's thread,
          // the deadline still kept by the scheduler below
          // (FailFastSuiteLawTest, through munit's own path).
          val produced = body() match
            case later: Future[?] => Await.result(later, Duration.Inf)
            case value            => value
          (produced match
            case Stoppable(stoppable) => stoppable(stop.future)
            case value                => value
          ) match
            case later: Future[?] => outcome.tryCompleteWith(later)
            case value            => outcome.trySuccess(value)
        catch case failure: Throwable => outcome.tryFailure(failure)
    )
    val deadline = deadlineScheduler.schedule(
      new Runnable:
        def run(): Unit =
          // The failure first: a body that stops at the request and returns a partial result must not pass the test.
          outcome.tryFailure(TestDeadlineExceeded(s"the test body did not return within $timeout"))
          stop.trySuccess(())
      ,
      timeout.toMillis,
      TimeUnit.MILLISECONDS
    )
    outcome.future.onComplete(_ => deadline.cancel(false))(ExecutionContext.parasitic)
    outcome.future

  @SuppressWarnings(Array("gezi.warts.NoJavaUtilConcurrent")) // "好的，用这个办法修，Scaladoc中cite #730作为依据" (the user, 2026-11-14)
  private lazy val bodyPool =
    Executors.newCachedThreadPool(daemonThreads("fail-fast-test-body"))

  @SuppressWarnings(Array("gezi.warts.NoJavaUtilConcurrent")) // "好的，用这个办法修，Scaladoc中cite #730作为依据" (the user, 2026-11-14)
  private lazy val deadlineScheduler =
    val scheduler = ScheduledThreadPoolExecutor(1, daemonThreads("fail-fast-test-deadline"))
    scheduler.setRemoveOnCancelPolicy(true)
    scheduler

  @SuppressWarnings(Array("gezi.warts.NoJavaUtilConcurrent")) // "好的，用这个办法修，Scaladoc中cite #730作为依据" (the user, 2026-11-14)
  private def daemonThreads(name: String): ThreadFactory = runnable =>
    val thread = Thread(runnable, name)
    thread.setDaemon(true)
    thread
