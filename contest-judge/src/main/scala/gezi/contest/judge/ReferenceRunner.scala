package gezi.contest.judge

import gezi.contest.entry.Cells
import gezi.contest.entry.Entry
import gezi.contest.entry.Interaction
import gezi.contest.entry.OutputDisplay
import gezi.contest.runner.EntryRunner
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.Reading
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.saturation.StopSignal

/** A reference reader as an entry: the weak-head evaluator under the mode
  * (`tabling(weak_head)`), each cell's Output
  * (`Cells.outputInstruction`) read as the reduction judge reads a program
  * (`Reduction.answeredNormalForms`): every normal form read from an empty
  * store within the limit and read back, and displayed (`Cells.displayed`);
  * a stopped reading displays the Output not evaluated, which asserts
  * nothing. A judgment cell's Output `N ∥ T` reads as the normal forms of T
  * that are N (the weak-head reading of a parallel). The state is kept as a
  * term (`Cells.nextState`); nothing else passes from one cell to the next,
  * and it keeps no cache. It reports no phases. It ignores the stop signal:
  * the judge's wall-clock limit ends its reading.
  */
final case class ReferenceEntry(mode: Mode, state: DeBruijnTerm) extends Entry:

  def run(cell: DeBruijnTerm, source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction =
    val output = Cells.outputInstruction(cell, state)
    val display = NormalForms.normalForms(mode, output).result(ReadingState.knowingTop(ReferenceEntry.limit)) match
      case Computed.Done(normalForms, _) => Cells.displayed(normalForms.map(Defunctionalization.instructionTerm).toSet)
      case Computed.Stopped(_)           => OutputDisplay.shown(Cells.output(cell, state))
    Interaction.Finished(display, Vector.empty, copy(state = Cells.nextState(cell, state)))

/** The reference readers by their names in the judge's table. */
object ReferenceEntry:

  /** The steps a reference reading may take: the steps that stand for 60
    * seconds, the largest limit a reduction family states, as the generic
    * entry's reading (`GenericEntry.readingLimit`); the judge's wall-clock
    * limit is what ends a point.
    */
  val limit: Long = Reading.budgetSteps(60)

  /** The reader of the name, `tabling(weak_head)`. Throws
    * `IllegalArgumentException` for another name.
    */
  def named(name: String): ReferenceEntry = name match
    case "tabling(weak_head)" => ReferenceEntry(Mode.TablingWeakHead, Cells.initialState)
    case other                => throw IllegalArgumentException(s"$other names no reference reader")

/** The main of a reference reader's JVM: the reader of the name served on
  * the pipe by the runner that entries' JVMs run (`EntryRunner.served`). A
  * reference reader is judge-side: its JVM's classpath is the judge's,
  * problem corpora included, while an entry's JVM can load neither. The cache the runner
  * offers is not kept.
  */
@main def judgeReferenceRunner(name: String): Unit =
  EntryRunner.served(_ => ReferenceEntry.named(name), None)
