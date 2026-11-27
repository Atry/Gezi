package gezi.saturation

/** What a computation reads at each of its checks (the judge's cancel, a
  * cell's interrupt, a fork's tasks in `gezi.hotspot.Forks`, a test's
  * deadline): when a stop
  * is requested, the computation stops at that check and gives what it has.
  * Stopping is cooperative: nothing interrupts the computation's thread. A
  * signal may be shared by several threads and is thread safe. The
  * saturation reads it at every delta it takes (`Saturation.saturated`); a
  * reading reads it every `gezi.weakhead.Budget.stopCheckSteps` steps.
  */
trait StopSignal:
  def stopRequested: Boolean

/** The signal that never asks for a stop. */
object StopSignal:

  /** The signal of a computation outside any fork and any cancel. */
  object NeverStopped extends StopSignal:
    def stopRequested: Boolean = false

  /** The signal of a stop that is requested once the future is completed.
    * A future is write-once, plain Scala and thread safe, so the signal is
    * portable, as the cancellation must be: cooperative, never
    * `Thread.interrupt`; a fork's join and a test's deadline complete its promise.
    */
  def completedWith(stop: scala.concurrent.Future[Unit]): StopSignal =
    CompletedFuture(stop)

  private final class CompletedFuture(stop: scala.concurrent.Future[Unit]) extends StopSignal:
    def stopRequested: Boolean = stop.isCompleted
