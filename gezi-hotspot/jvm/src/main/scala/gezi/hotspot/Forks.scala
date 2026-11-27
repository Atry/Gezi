package gezi.hotspot

import gezi.saturation.StopSignal
import scala.concurrent.Promise
import scala.util.Try
import scala.util.Using

/** A task of a fork: its own budget and its body, which runs within the budget,
  * reads the signal at each check of the budget, and gives its result with what
  * it spent.
  */
final case class ForkedTask[Result](
    budget: Budget,
    body: (Budget, StopSignal) => TaskOutcome[Result]
)

/** What a task gave: its result and its costs. */
final case class TaskOutcome[Result](result: Result, spent: Spent)

/** What a join of all the tasks gives: each task's outcome, in the order of the
  * tasks; their costs summed (`Forks.summed`); and the wall time of the longest
  * task, in nanoseconds.
  */
final case class JoinedAll[Result](
    outcomes: Vector[TaskOutcome[Result]],
    spent: Spent,
    wallNanoseconds: Long
)

/** What a join on the first success gives: the result of the task that
  * succeeded first, if any did; each task's outcome, in the order of the tasks,
  * the others' as they stopped; their costs summed; and the wall time of the
  * longest task, in nanoseconds.
  */
final case class JoinedFirstSuccess[Result](
    success: Option[Result],
    outcomes: Vector[TaskOutcome[Result]],
    spent: Spent,
    wallNanoseconds: Long
)

/** The structured fork and join of the multithreading framework (the convention
  * every mutable structure of the framework follows is in the package's
  * documentation, [[gezi.hotspot]]). The framework provides this and no search
  * algorithm: an entry's multithreaded search gives the tasks.
  *
  * Each task runs on a virtual thread of its own; a join returns only after
  * every task has ended, so no thread outlives the call. The parallelism of the
  * processor is the virtual thread scheduler's number of carrier threads, set
  * by the JDK's system property `jdk.virtualThreadScheduler.parallelism` (in
  * the contest, by the judge to the cores an entry is given); a task waiting on
  * IO is unmounted and holds no carrier. A virtual thread is not preempted:
  * with more tasks than carriers, a task that computes without blocking or
  * yielding holds its carrier until it ends, and a task not yet started waits
  * for a carrier, so a join on the first success waits for that success until a
  * carrier is free. The costs of a fork are summed in steps and applications;
  * its wall time is the longest task's, read by `System.nanoTime` around each
  * body (a cost, not a benchmark).
  *
  * A task that throws requests a stop of the others, and the join throws the
  * `java.util.concurrent.ExecutionException` that carries the task's exception
  * once every task has ended.
  *
  * Not `StructuredTaskScope`, which is a preview feature of JDK 25.
  */
object Forks:

  /** Every task run to its end, and each one's outcome. */
  def joinedAll[Result](tasks: Vector[ForkedTask[Result]]): JoinedAll[Result] =
    val stop = Promise[Unit]()
    val timed = ran(tasks, stop, _ => ())
    JoinedAll(timed.map(_._1), summed(timed.map(_._1.spent)), longest(timed))

  /** The tasks run until one gives a result that `succeeded` accepts; then a
    * stop is requested, and the others stop at their next check of their
    * budgets. The first such result, and every task's outcome.
    */
  def joinedFirstSuccess[Result](
      tasks: Vector[ForkedTask[Result]],
      succeeded: Result => Boolean
  ): JoinedFirstSuccess[Result] =
    val stop = Promise[Unit]()
    val firstSuccess = Promise[Result]()
    val timed = ran(
      tasks,
      stop,
      outcome =>
        if succeeded(outcome.result) then
          firstSuccess.trySuccess(outcome.result)
          stop.trySuccess(())
    )
    JoinedFirstSuccess(
      firstSuccess.future.value.map(_.get),
      timed.map(_._1),
      summed(timed.map(_._1.spent)),
      longest(timed)
    )

  /** The costs of several tasks as one: steps summed, and the applications of
    * each unit summed.
    */
  def summed(spents: Vector[Spent]): Spent =
    Spent(
      spents.map(_.steps).sum,
      spents.flatMap(_.applications).groupMapReduce(_._1)(_._2)(_ + _)
    )

  private def longest[Result](
      timed: Vector[(TaskOutcome[Result], Long)]
  ): Long =
    timed.map(_._2).maxOption.getOrElse(0L)

  /** Each task run on a virtual thread of its own, with its wall time; the
    * outcome handed to `finished` on the task's thread as it ends. Returns
    * after every task has ended: closing the executor waits for them.
    *
    * A local mutable exception of the multithreading framework: the executor is
    * the JDK's, thread safe on its own, confined to this call and closed before
    * it returns. The user, 2026-11-01: "我觉得从设计的角度看，局部的可变例外可以接受". The two
    * promises of a join are write-once cells completed by `trySuccess`, thread
    * safe on their own; nothing else is shared between the tasks.
    */
  @SuppressWarnings(
    Array("gezi.warts.NoJavaUtilConcurrent")
  ) // "我觉得从设计的角度看，局部的可变例外可以接受" (the user, 2026-11-01)
  private def ran[Result](
      tasks: Vector[ForkedTask[Result]],
      stop: Promise[Unit],
      finished: TaskOutcome[Result] => Unit
  ): Vector[(TaskOutcome[Result], Long)] =
    val signal = StopSignal.completedWith(stop.future)
    // "我觉得从设计的角度看，局部的可变例外可以接受" (the user, 2026-11-01): the executor of the multithreading framework, confined to this call.
    Using.resource(
      java.util.concurrent.Executors.newVirtualThreadPerTaskExecutor()
    ) { executor =>
      val futures = tasks.map(task =>
        executor.submit[(TaskOutcome[Result], Long)](() =>
          timedRun(task, signal, stop, finished)
        )
      )
      futures.map(_.get())
    }

  /** The task's body run and timed. A body that throws requests a stop of the
    * other tasks and throws on.
    */
  private def timedRun[Result](
      task: ForkedTask[Result],
      signal: StopSignal,
      stop: Promise[Unit],
      finished: TaskOutcome[Result] => Unit
  ): (TaskOutcome[Result], Long) =
    val start = System.nanoTime
    val outcome = Try(task.body(task.budget, signal))
    if outcome.isFailure then stop.trySuccess(())
    val ended = outcome.get
    finished(ended)
    (ended, System.nanoTime - start)
