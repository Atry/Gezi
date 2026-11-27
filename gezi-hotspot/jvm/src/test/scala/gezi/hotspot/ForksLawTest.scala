package gezi.hotspot

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.saturation.StopSignal
import scala.annotation.tailrec

/** The laws of the fork and join primitive (`Forks`).
  *
  * The first: joining all the tasks gives each task's outcome in the order of
  * the tasks, as running the bodies one after another gives them, with the
  * steps summed. Its purpose is to catch a join that loses, reorders or
  * duplicates an outcome, or sums the costs wrongly. The inputs are generated
  * lists of numbers, one for each task, whose body sums its list and spends a
  * step for each number.
  *
  * The second is on the first success.
  */
class ForksLawTest extends GeneratedProperties:

  private val budget = Budget(1000, countedUnits = false, NeverStop)

  property(
    "joining all gives the outcomes of the bodies run one after another"
  ) {
    for listsOfTasks <- Gen
        .int(Range.constant(-50, 50))
        .list(Range.linear(0, 10))
        .list(Range.linear(0, 12))
        .forAll
    yield
      val tasks = listsOfTasks.toVector.map(numbers =>
        ForkedTask[Int](
          budget,
          (_, _) =>
            TaskOutcome(numbers.sum, Spent(numbers.size.toLong, Map.empty))
        )
      )
      val sequential = tasks.map(task => task.body(task.budget, NeverStop))
      val joined = Forks.joinedAll(tasks)
      Result.all(
        List(
          Result.diff(joined.outcomes, sequential)(_ == _),
          Result.diff(joined.spent.steps, listsOfTasks.map(_.size.toLong).sum)(
            _ == _
          )
        )
      )
  }

  /** A signal that never asks to stop, for the sequential run. */
  private object NeverStop extends StopSignal:
    def stopRequested: Boolean = false

  /** Waits until a stop is requested; the waiting is the stand-in for an
    * executor that checks its budget at every step. It yields at each check, so
    * that waiting tasks never hold every carrier thread while a succeeding task
    * waits for one (a virtual thread is not preempted).
    */
  @tailrec
  private def waitedForStop(signal: StopSignal): Unit =
    if !signal.stopRequested then
      Thread.`yield`()
      waitedForStop(signal)

  /** The second law: when some tasks succeed and the others run until a stop is
    * requested, the join on the first success returns, its success is the
    * result of one of the succeeding tasks, and every other task stopped. Its
    * purpose is to catch a join that never asks the others to stop (the test
    * then does not end), or that answers a result no task gave as a success.
    * The inputs are generated lists of tasks, each succeeding with a number or
    * waiting, with at least one succeeding.
    */
  property(
    "joining on the first success stops the others and answers a success"
  ) {
    for
      kinds <- Gen
        .choice1(
          Gen.int(Range.constant(1, 100)).map(Some(_)),
          Gen.constant(None)
        )
        .list(Range.linear(0, 8))
        .forAll
      succeeding <- Gen.int(Range.constant(1, 100)).forAll
    yield
      val drawn = (Some(succeeding) :: kinds).toVector
      val tasks = drawn.map {
        case Some(number) =>
          ForkedTask[Int](
            budget,
            (_, _) => TaskOutcome(number, Spent(1, Map.empty))
          )
        case None =>
          ForkedTask[Int](
            budget,
            (_, signal) =>
              waitedForStop(signal)
              TaskOutcome(0, Spent.none)
          )
      }
      val joined = Forks.joinedFirstSuccess(tasks, _ > 0)
      Result.all(
        List(
          Result
            .assert(joined.success.exists(drawn.flatten.contains))
            .log(s"success ${joined.success} of ${drawn}"),
          Result.diff(joined.outcomes.size, drawn.size)(_ == _),
          Result.assert(drawn.zip(joined.outcomes).forall {
            case (None, outcome)         => outcome.result == 0
            case (Some(number), outcome) => outcome.result == number
          })
        )
      )
  }
