package gezi.jupyter.kernel

import almond.interpreter.api.ExecuteResult
import gezi.ir.Configured
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.contest.entry.Entry
import gezi.contest.entry.Interaction
import gezi.contest.entry.OutputDisplay
import gezi.ir.NoFacts
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.saturation.StopSignal
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.Future
import scala.concurrent.duration.DurationInt

private given cellInterruptLawTestNoFacts: NoFacts.type = NoFacts

/** Jupyter's interrupt reaches the entry that runs a cell: a cell whose key the entry would run until it is stopped is
  * answered with an `Interrupted` error soon after an interrupt, within the
  * suite's deadline. Its purpose is to catch an interrupt that the kernel
  * does not hand to its entry's stop; that an entry checks its stop is the
  * entry's own law (`CancelGraceLawTest` of the generic entry).
  */
class CellInterruptLawTest extends GeneratedProperties:

  /** An entry that runs until it is stopped, and throws when it is not
    * stopped within a second.
    */
  private object UntilStopped extends Entry[NoFacts.type]:
    def run(cell: gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[NoFacts.type] =
      val deadline = System.nanoTime + 1000000000L
      @annotation.tailrec
      def waited(): Unit =
        if !stop.stopRequested then
          if System.nanoTime - deadline >= 0 then throw IllegalStateException("the entry ran a second without being stopped")
          Thread.sleep(1)
          waited()
      waited()
      Interaction.Finished(OutputDisplay.noScottADTValue[NoFacts.type], Vector.empty, this)

  // Five inputs, not the default twenty: each waits for its interrupt, and
  // the suite's deadline of 3 s bounds them all.
  property("an interrupt ends a cell whose entry would run until it is stopped", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    for
      key <- Gen.string(Gen.lower, Range.linear(1, 4)).forAll
      value <- HoasGenerators.normalForm.forAll
    yield
      val interpreter = CellInterpreter.started(
        Files.createTempDirectory("cell-interrupt"),
        NotebookLocation(Vector("file", "n", "interrupt")),
        UntilStopped,
        None
      )
      val cell = s"λ\"$key\". (${LambdalatticeText.text(value)})"
      val interrupting = Future {
        Thread.sleep(50)
        interpreter.interrupt()
      }(using ExecutionContext.global)
      val answer = interpreter.execute(cell, storeHistory = true, None, None, None)
      Await.result(interrupting, 1.second)
      answer match
        case ExecuteResult.Error(name, _, _) => Result.diff(name, "Interrupted")(_ == _)
        case other                          => Result.failure.log(s"the interrupted cell was answered with $other")
  }
