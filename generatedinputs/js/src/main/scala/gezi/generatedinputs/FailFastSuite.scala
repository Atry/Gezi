package gezi.generatedinputs

import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.concurrent.duration.SECONDS

/** The base suite under Scala.js, in place of
  * `generatedinputs/jvm/src/main/scala/gezi/generatedinputs/FailFastSuite.scala`,
  * whose deadline runs a test's body on a pool of threads, blocks on its
  * future (`Await.result`) and stops it from a scheduler: Node.js has one
  * thread and Scala.js's Java library none of those. The same interface:
  * `stoppableTest` hands its body a stop request, which never completes here,
  * since nothing can interrupt a body on the one thread; `sharedFixtures` are
  * forced in `beforeAll`, before any test, without a bound of their own; and
  * `munitTimeout` is the JVM suite's 3 seconds, which munit under Scala.js
  * keeps for a body that returns a future only. So a synchronous body that
  * runs long is not stopped on Node.js; its JVM project's suite bounds it.
  */
abstract class FailFastSuite extends munit.FunSuite:

  override val munitTimeout: Duration = Duration(3, SECONDS)

  /** The fixtures the suite's tests share, each given a stop request that
    * never completes, forced in `beforeAll`.
    */
  def sharedFixtures: Vector[Future[Unit] => Any] = Vector.empty

  override def beforeAll(): Unit =
    super.beforeAll()
    sharedFixtures.foreach(fixture => fixture(Promise[Unit]().future))

  /** A test whose body receives the stop request, which never completes
    * under Scala.js.
    */
  def stoppableTest(options: munit.TestOptions)(body: Future[Unit] => Any)(using munit.Location): Unit =
    test(options)(body(Promise[Unit]().future))

/** A test body that did not return within its deadline: the JVM suite's
  * failure, which no test under Scala.js raises.
  */
final class TestDeadlineExceeded(message: String) extends RuntimeException(message)
