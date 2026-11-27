package gezi.contest.entry

import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.ProgramPurity
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.ir.{
  ChoiceSpine,
  Configured,
  NativeSpecializer,
  StorageAccess,
  Value
}
import gezi.saturation.StopSignal
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ReadingConfiguration
import gezi.weakhead.ReadingState
import gezi.weakhead.ScottADTChoices

/** What a judgment `N ∥ T` comes to: T ⊑_O N proved (N a Scott ADT value of T),
  * T ⊑_O N refuted, or neither.
  */
enum Judgment:
  case Proved
  case Refuted
  case Undecided

/** A reading's result: what `ScottADTChoices.of` read of the program (its Scott
  * ADT values and the flags of the reading), none when the reading stopped; the
  * executor the reading left (`Judgments.read`); its reports, the phases it
  * went through and the evaluator steps it spent.
  */
final case class ProgramReading[C <: NativeSpecializer & Singleton, Suspension](
    read: Option[ScottADTChoices.Read[C]],
    executor: Executor[C, Suspension],
    reports: Vector[Report]
)

/** A judgment's result: the judgment, its display, the executor its readings
  * left, the reports of its readings.
  */
final case class JudgmentReading[
    C <: NativeSpecializer & Singleton,
    Suspension
](
    judgment: Judgment,
    display: OutputDisplay[C],
    executor: Executor[C, Suspension],
    reports: Vector[Report]
)

/** The framework's reading of a cell's Output, the one place where an entry's
  * general reading and its judgment of a parallel Output `N ∥ T` are made, so
  * that every entry judges by the same rule with no Scala of its own (an
  * entry's Scala is its natives only).
  */
object Judgments:

  /** The executor's reading of the program within the limit of steps, stopped
    * also by the judge's cancel (`gezi.hotspot.Budget`), from what the executor
    * carries: the program's Scott ADT values (`ScottADTChoices.of`) with the
    * flags of the reading, or none when it stopped. Its reports are the phase
    * `run`, then `read_back` when it finished, then the count `reading_steps`,
    * the evaluator steps the reading spent (`gezi.hotspot.Spent`), whether it
    * finished or its budget stopped it (a reading the judge's cancel ends
    * reports no count): a reading whose loops run as narrow blocks spends few
    * steps however much the blocks compute, since a block's run charges none
    * (it shows as the phase `block_run`), so the count tells a compiled reading
    * from one whose steps grow with the work.
    */
  def read[C <: NativeSpecializer & Singleton, Suspension](
      executor: Executor[C, Suspension],
      dependencies: ExecutionDependencies,
      program: Configured[C],
      limit: Long,
      stop: StopSignal,
      configuration: ReadingConfiguration[C]
  )(using C, StorageAccess): ProgramReading[C, Suspension] =
    counted(
      executor,
      dependencies,
      program,
      limit,
      stop,
      configuration,
      "reading_steps"
    )

  /** `read`'s reading, its steps reported under the count's name given: one
    * execution of the executor given, from the start, within the limit and
    * under the cancel (`gezi.hotspot.Budget`). The executor returned is the one
    * the execution left, whether it finished or its budget stopped it, and the
    * one given when the judge's cancel ended it. A reading starts from the
    * tables the executor kept, as its table retention says, the entry data's
    * `table_retention` (`Defaults.executor`).
    *
    * The executor gives the program's normal forms, which the entry reads once
    * more for the Scott ADT values among them (`scottADTRead`): the generic
    * executor interface offers no other reading.
    */
  private def counted[C <: NativeSpecializer & Singleton, Suspension](
      executor: Executor[C, Suspension],
      dependencies: ExecutionDependencies,
      program: Configured[C],
      limit: Long,
      stop: StopSignal,
      configuration: ReadingConfiguration[C],
      stepsName: String
  )(using C, StorageAccess): ProgramReading[C, Suspension] =
    // On the judge's cancel the reading hands back the executor it was
    // given. That is required, not a shortcut: the JIT state an executor
    // carries marks the tabled instances whose reading is in progress (the
    // cycle check), between two normal forms of one reading as much as
    // within one, and a next reading on a state with those keys still
    // marked would take the cycle exit on them and answer wrongly.
    // What the cancelled reading compiled or
    // tabled is not kept, which costs the next reading time only; nor are
    // the steps it spent, so a cancelled reading reports no count of steps.
    val ((after, _, progress), run) = Phase.timed("run")(
      executor.executed(
        program,
        dependencies,
        gezi.hotspot.Budget(limit, countedUnits = false, stop)
      )
    )
    progress.suspension match
      case None =>
        val (scottADTRead, readBack) = Phase.timed("read_back")(
          scottADTValues(progress.found, limit, stop, configuration)
        )
        ProgramReading(
          scottADTRead,
          after,
          Vector(run, readBack, Count(stepsName, progress.spent.steps))
        )
      case Some(_) if stop.stopRequested =>
        ProgramReading(None, executor, Vector(run))
      case Some(_) =>
        ProgramReading(
          None,
          after,
          Vector(run, Count(stepsName, progress.spent.steps))
        )

  /** The Scott ADT values among the normal forms an execution found
    * (`ScottADTChoices.ofNormalForms`), with no reading again: the forms are
    * the execution's, its storages handed over whole left in them.
    */
  def scottADTValues[C <: NativeSpecializer & Singleton](
      found: Vector[Configured[C]],
      limit: Long,
      stop: StopSignal,
      configuration: ReadingConfiguration[C]
  )(using specializer: C): Option[ScottADTChoices.Read[C]] =
    Some(
      ScottADTChoices.ofNormalForms(found)(using
        specializer,
        configuration.storageAccess
      )
    )

  /** What `ScottADTChoices.of` reads of the value under a fresh reading state
    * of the configuration, within the limit and under the stop; none when the
    * reading is stopped by either. For a value no execution gave, such as the
    * output field an FFI program left unread (`Entry.displayed`).
    */
  def scottADTValuesOf[C <: NativeSpecializer & Singleton](
      mode: Mode,
      value: Value[C],
      limit: Long,
      stop: StopSignal,
      configuration: ReadingConfiguration[C]
  )(using C): Option[ScottADTChoices.Read[C]] =
    ScottADTChoices
      .of(mode, value)
      .resultUnless(ReadingState.knowingTop(limit, configuration), stop)
      .collect { case Computed.Done(read, _) => read }

  /** The judgment of the candidate N on the program T, each reading within the
    * limit and under the cancel, with its display:
    *
    *   - Proved when N is a member of T's Scott ADT values
    *     (`ScottADTChoices.same` with one of `ScottADTChoices.members` of the
    *     reading), displayed as N (N ∥ T = N then, by absorption).
    *   - Refuted when all of these hold: N is a Scott ADT value, a closed βη
    *     normal form (`ScottADTChoices.ofNormalForm` gives it); T is pure
    *     (`ProgramPurity.pureInstruction`); T's reading finished, with exactly
    *     one Scott ADT value N0 and no normal form dropped for being none
    *     (`ScottADTChoices.Read.nothingDropped`, `noChoiceSplit`), so that N0
    *     is the one normal form T reads to; and N is not N0, compared as Scott
    *     ADT values (`ScottADTChoices.same`). Sound: T read to its one normal
    *     form N0 gives T =βη N0, so NF◇(T) = {N0} (a term βη-equal to one
    *     closed normal form has that normal form alone); N is a closed βη
    *     normal form, so NF◇(N) = {N} by the same section; and NF◇(N ∥ T) ⊆
    *     NF◇(N) ∩ NF◇(T) = {N} ∩ {N0} = ∅: T ⊑_O N fails, and N is no Scott ADT
    *     value of T. A reading of a program with a choice or a parallel proves
    *     only that T ⊑_O N for each N it read, never that nothing else is, so
    *     such a program is never refuted. Displayed as the Scott ADT values of
    *     no member.
    *   - Undecided otherwise, a stopped reading and a candidate that is no
    *     Scott ADT value (`ScottADTChoices.ofNormalForm` gives none) included,
    *     displayed as the Output itself, unevaluated.
    *
    * That two Scott ADT values `same` fails to equate are different terms holds
    * because `same` reads the (k, i, fields) of both from their layers, a layer
    * of one of those a reading or `ofNormalForm` gives being the canonical
    * layer of its (k, i, fields) (`ScottADTChoices`), whatever its spelling was
    * written as; so α-equivalent normal forms are one member.
    *
    * A judgment cell gives N and T as constants (the runner's
    * `PipeLines.cellTerm` keeps each side of a filling that is a parallel
    * unread, so that a large program is not read back into a tree): both are
    * made instructions of the configuration
    * (`Defunctionalization.thunkInstruction`), and T's purity is decided on its
    * instruction.
    *
    * The reports are the program's `defunctionalization` and reading
    * (`reading_steps` among them).
    */
  def judged[C <: NativeSpecializer & Singleton, Suspension](
      executor: Executor[C, Suspension],
      dependencies: ExecutionDependencies,
      candidate: DeBruijnTermOf[Configured[C]],
      point: DeBruijnTermOf[Configured[C]],
      limit: Long,
      stop: StopSignal,
      configuration: ReadingConfiguration[C]
  )(using C, StorageAccess): JudgmentReading[C, Suspension] =
    val (program, defunctionalization) = Phase.timed("defunctionalization")(
      Defunctionalization.thunkInstruction[C](point)
    )
    val programReading =
      read(executor, dependencies, program, limit, stop, configuration)
    val reports = defunctionalization +: programReading.reports
    def undecided: JudgmentReading[C, Suspension] =
      JudgmentReading(
        Judgment.Undecided,
        OutputDisplay.remainder[C](
          gezi.frontend.DeBruijnTerm.Parallel(candidate, point)
        ),
        programReading.executor,
        reports
      )
    ScottADTChoices.ofNormalForm(
      Defunctionalization.thunkInstruction[C](candidate)
    ) match
      case None                  => undecided
      case Some(candidateValues) =>
        programReading.read match
          case Some(found)
              if ScottADTChoices
                .members(found.choices)
                .exists(ScottADTChoices.same(_, candidateValues)) =>
            JudgmentReading(
              Judgment.Proved,
              OutputDisplay.Values(candidateValues),
              programReading.executor,
              reports
            )
          case Some(found)
              if found.nothingDropped && found.noChoiceSplit && ScottADTChoices
                .members(found.choices)
                .size == 1 &&
                !stop.stopRequested && ProgramPurity.pureInstruction(program) =>
            JudgmentReading(
              Judgment.Refuted,
              OutputDisplay.noScottADTValue[C],
              programReading.executor,
              reports
            )
          case _ => undecided
