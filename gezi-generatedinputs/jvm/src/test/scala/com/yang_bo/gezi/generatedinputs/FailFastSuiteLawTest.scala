package com.yang_bo.gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import scala.annotation.tailrec
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.concurrent.duration.MILLISECONDS
import scala.concurrent.duration.SECONDS
import scala.util.Failure

/** Purpose: a timeout whose stop request reaches no check leaves the thread
  * spinning (the defect of munit 1.3.6, scalameta/munit#730). For every
  * deadline, a body that spins until the stop promise is completed, run by
  * `FailFastSuite.bounded` under that deadline, fails with a
  * `TestDeadlineExceeded`, sees the stop request and returns (its thread is
  * released), and the executor then runs a next task. The law is concise: the
  * three observations are the whole law, so a property on generated deadlines.
  * The check is a read of the promise, as a computation reads a
  * `StopSignal.promised` signal.
  */
class FailFastSuiteLawTest extends GeneratedProperties:

  @tailrec private def spinningUntilStopped(
      stop: scala.concurrent.Future[Unit]
  ): Unit =
    if !stop.isCompleted then spinningUntilStopped(stop)

  property(
    "a body that spins until its stop request is released at its deadline",
    _.copy(testLimit = 5)
  ) {
    for deadlineMillis <- Gen.int(Range.linear(20, 60)).forAll
    yield
      val stop = Promise[Unit]()
      val released = Promise[Unit]()
      val outcome = FailFastSuite.bounded(
        Duration(deadlineMillis.toLong, MILLISECONDS),
        stop
      )(() =>
        FailFastSuite.Stoppable { requested =>
          spinningUntilStopped(requested)
          released.trySuccess(())
        }
      )
      Await.ready(outcome, Duration(5, SECONDS))
      Await.ready(released.future, Duration(5, SECONDS))
      val next = Await.result(
        FailFastSuite.bounded(Duration(5, SECONDS), Promise[Unit]())(() =>
          deadlineMillis
        ),
        Duration(5, SECONDS)
      )
      Result.all(
        List(
          Result
            .assert(outcome.value.exists {
              case Failure(_: TestDeadlineExceeded) => true
              case _                                => false
            })
            .log(s"outcome ${outcome.value}"),
          Result
            .assert(released.isCompleted)
            .log("the body did not see the stop request"),
          Result.diff(next, deadlineMillis: Any)(_ == _)
        )
      )
  }

  /** Purpose: a run budget that does not bound a test (FailFastSuite, "THE RUN
    * BUDGET"). For a budget and a time already spent of it, a body that spins
    * until stopped, run under a deadline far beyond the budget: when the budget
    * is spent the outcome is a `TestRunBudgetSpent` and the body never ran;
    * otherwise the body is stopped and the test fails with a
    * `TestDeadlineExceeded` well before its own deadline.
    */
  property(
    "a test under a run budget fails at once when it is spent and is stopped when it runs out",
    _.copy(testLimit = 5)
  ) {
    for
      budgetMillis <- Gen.int(Range.linear(30, 80)).forAll
      spentMillis <- Gen.int(Range.linear(0, 120)).forAll
    yield
      val now = System.currentTimeMillis
      val budget = RunBudget(
        now - spentMillis,
        Duration(budgetMillis.toLong, MILLISECONDS)
      )
      val ran = Promise[Unit]()
      val released = Promise[Unit]()
      val outcome = FailFastSuite.boundedUnder(
        Some(budget),
        now,
        Duration(60, SECONDS),
        Promise[Unit]()
      )(() =>
        FailFastSuite.Stoppable { requested =>
          ran.trySuccess(())
          spinningUntilStopped(requested)
          released.trySuccess(())
        }
      )
      Await.ready(outcome, Duration(5, SECONDS))
      if spentMillis >= budgetMillis then
        Result.all(
          List(
            Result
              .assert(outcome.value.exists {
                case Failure(_: TestRunBudgetSpent) => true
                case _                              => false
              })
              .log(s"outcome ${outcome.value}"),
            Result
              .assert(!ran.isCompleted)
              .log("the body ran after the budget was spent")
          )
        )
      else
        Await.ready(released.future, Duration(5, SECONDS))
        Result.all(
          List(
            Result
              .assert(outcome.value.exists {
                case Failure(_: TestDeadlineExceeded) => true
                case _                                => false
              })
              .log(s"outcome ${outcome.value}"),
            Result
              .assert(released.isCompleted)
              .log("the body did not see the stop request")
          )
        )
  }

  /** The outcome of each test of the suite, run as munit runs it: its body as
    * munit's `test` built it, through the suite's test transforms.
    */
  private def outcomes(
      suite: FailFastSuite
  ): Vector[Option[scala.util.Try[Any]]] =
    suite
      .munitTests()
      .toVector
      .map(registered =>
        Await.ready(registered.body(), Duration(10, SECONDS)).value
      )

  /** Purpose: a runner that drops a `stoppableTest`'s body. munit's `test`
    * gives every body as a future of its value, and `FailFastSuite.bounded`
    * once matched the `Stoppable` bare, so from 90b1b784e no stoppable body ran
    * and every such test passed (found 2026-11-16). A body built through
    * munit's own path, a suite's registered test, must run and receive a stop
    * future its deadline has not completed.
    */
  test(
    "a stoppable test's body registered through munit's test runs and receives an uncompleted stop future"
  ) {
    val seen = Promise[Boolean]()
    val suite = new FailFastSuite:
      stoppableTest("records whether its stop future is completed") { stopped =>
        seen.trySuccess(stopped.isCompleted)
      }
    val Vector(outcome) = outcomes(suite): @unchecked
    assert(outcome.exists(_.isSuccess), s"outcome $outcome")
    assertEquals(seen.future.value, Some(scala.util.Success(false)))
  }

  /** Purpose: an overrunning property that keeps drawing inputs after its
    * deadline. The deadline fails the test and stops no thread, so a property
    * that does not read its stop request runs all its inputs on the daemon
    * thread and takes the processors of the later tests of the JVM (found
    * 2026-11-16: eight plain tests failed only after stoppable bodies ran). The
    * property, registered through munit's own path, has 200 inputs of 20 ms
    * each and a deadline of 300 ms; no input may start after the stop request
    * but the one whose check preceded it, so a second input started after the
    * request is the defect.
    */
  test(
    "a property whose deadline passed starts no input after the stop request but the one in progress"
  ) {
    val firstAfterStop = Promise[Unit]()
    val secondAfterStop = Promise[Unit]()
    val suite = new GeneratedProperties:
      override val munitTimeout: Duration = Duration(300, MILLISECONDS)
      stoppableProperty(
        "many short inputs",
        _.copy(testLimit = SuccessCount(200))
      ) { stopped =>
        for drawn <- Gen.int(Range.linear(0, 1)).forAll
        yield
          if stopped.isCompleted && !firstAfterStop.trySuccess(()) then
            secondAfterStop.trySuccess(())
          Thread.sleep(20)
          Result.success.log(s"input $drawn")
      }
    val Vector(outcome) = outcomes(suite): @unchecked
    assert(
      outcome.exists(_.isFailure),
      s"the property was to overrun its deadline, outcome $outcome"
    )
    Thread.sleep(1000)
    assert(
      !secondAfterStop.isCompleted,
      "a second input started after the stop request"
    )
  }

  /** Purpose: a canary for every way a test's body may be dropped: a stoppable
    * test and a property whose bodies fail, registered through munit's own
    * path, are reported failed. A runner that completes a test without running
    * its body, as the `Stoppable` matched bare did, reports them passed.
    */
  test(
    "a stoppable test and a property whose bodies fail are reported failed"
  ) {
    val suite = new GeneratedProperties:
      stoppableTest("fails in its body") { _ =>
        fail("the canary's stoppable body fails")
      }
      property("fails on every input") {
        for drawn <- Gen.int(Range.linear(0, 1)).forAll
        yield Result.failure.log(s"the canary's property fails on $drawn")
      }
    val reported = outcomes(suite)
    assertEquals(reported.size, 2)
    assert(reported.forall(_.exists(_.isFailure)), s"outcomes $reported")
  }
