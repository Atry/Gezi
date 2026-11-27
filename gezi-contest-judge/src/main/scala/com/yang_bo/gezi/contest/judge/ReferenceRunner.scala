package com.yang_bo.gezi.contest.judge

import com.yang_bo.gezi.contest.entry.Cells
import com.yang_bo.gezi.contest.entry.Entry
import com.yang_bo.gezi.contest.entry.Interaction
import com.yang_bo.gezi.contest.entry.OutputDisplay
import com.yang_bo.gezi.contest.runner.EntryRunner
import com.yang_bo.gezi.frontend.DeBruijnTermOf
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.ir.{Closed, Configured, NoFacts, Value}
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.Reading
import com.yang_bo.gezi.weakhead.ReadingConfiguration
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.weakhead.ScottADTChoices
import com.yang_bo.gezi.saturation.StopSignal

/** A reference reader as an entry of no facts: the weak-head evaluator under
  * the mode (`tabling(weak_head)`), each cell's Output
  * (`Cells.outputInstruction`) read as its Scott ADT values
  * (`ScottADTChoices.of`) from an empty store within the limit, and displayed;
  * a stopped reading displays the Output not evaluated, which asserts nothing.
  * A judgment cell's Output `N ∥ T` reads as the Scott ADT values of T that are
  * N (the weak-head reading of a parallel). The state is kept as a term
  * (`Cells.nextState`); nothing else passes from one cell to the next, and it
  * keeps no cache. It reports no phases. It ignores the stop signal: the
  * judge's wall-clock limit ends its reading.
  */
final case class ReferenceEntry(
    mode: Mode,
    state: DeBruijnTermOf[Configured[NoFacts.type]]
) extends Entry[NoFacts.type]:

  def specializer: NoFacts.type = NoFacts

  def run(
      cell: DeBruijnTermOf[Configured[NoFacts.type]],
      source: ExpansionSource,
      stop: StopSignal
  ): Interaction[NoFacts.type] =
    val output = Cells.outputInstruction[NoFacts.type](cell, state)
    val display = valuesDisplayed(
      Value.of(output),
      OutputDisplay.remainder[NoFacts.type](Cells.output(cell, state))
    )
    Interaction.Finished(
      display,
      Vector.empty,
      copy(state = Cells.nextState(cell, state))
    )

  /** The reference reads no FFI program. */
  def displayed(
      value: Closed[NoFacts.type],
      source: ExpansionSource,
      stop: StopSignal
  ): (Entry[NoFacts.type], OutputDisplay[NoFacts.type]) =
    (
      this,
      valuesDisplayed(
        Closed.value(value),
        OutputDisplay.noScottADTValue[NoFacts.type]
      )
    )

  /** The value's Scott ADT values within the limit, or `stopped` when the
    * reading ends first.
    */
  private def valuesDisplayed(
      value: Value[NoFacts.type],
      stopped: OutputDisplay[NoFacts.type]
  ): OutputDisplay[NoFacts.type] =
    ScottADTChoices
      .of(mode, value)
      .result(
        ReadingState
          .knowingTop(ReferenceEntry.limit, ReadingConfiguration.withoutFacts)
      ) match
      case Computed.Done(read, _) => OutputDisplay.Values(read.choices)
      case Computed.Stopped(_)    => stopped

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
    case "tabling(weak_head)" =>
      ReferenceEntry(Mode.TablingWeakHead, Cells.initialState)
    case other =>
      throw IllegalArgumentException(s"$other names no reference reader")

/** The main of a reference reader's JVM: the reader of the name served on the
  * pipe by the runner that entries' JVMs run (`EntryRunner.served`). A
  * reference reader is judge-side: its JVM's classpath is the judge's, problem
  * corpora included, while an entry's JVM can load neither. The cache the
  * runner offers is not kept.
  */
@main def judgeReferenceRunner(name: String): Unit =
  EntryRunner.served(_ => ReferenceEntry.named(name), None)
