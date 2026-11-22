package gezi.contest.entry

import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.ProgramPurity
import gezi.ir.Instruction
import gezi.saturation.StopSignal
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor

/** What a judgment `N ∥ T` comes to: T ⊑_O N proved (N an answer of T),
  * T ⊑_O N refuted, or neither.
  */
enum Judgment:
  case Proved
  case Refuted
  case Undecided

/** A reading's result: the normal forms read back, none when the reading
  * stopped; the executor the reading left (`Judgments.read`); its reports, the phases it went
  * through and the evaluator steps it spent.
  */
final case class ProgramReading[Suspension](normalForms: Option[Set[DeBruijnTerm]], executor: Executor[Suspension], reports: Vector[Report])

/** A judgment's result: the judgment, the executor its readings left, the
  * reports of its readings.
  */
final case class JudgmentReading[Suspension](judgment: Judgment, executor: Executor[Suspension], reports: Vector[Report])

/** The framework's reading of a cell's Output, the one place where an entry's general reading and its
  * judgment of a parallel Output `N ∥ T` are made, so that every entry
  * judges by the same rule with no Scala of its own (an entry's Scala is its
  * natives only).
  */
object Judgments:

  /** The executor's reading of the program within the limit of steps,
    * stopped also by the judge's cancel (`gezi.hotspot.Budget`), from what the
    * executor carries: its normal forms read back, or none when it stopped. Its
    * reports are the phase `run`, then `read_back` when it finished, then
    * the count `reading_steps`, the evaluator steps the reading spent
    * (`gezi.hotspot.Spent`), whether it finished or its budget stopped it (a
    * reading the judge's cancel ends reports no count): a reading whose loops
    * run as narrow blocks spends few steps however much the blocks compute,
    * since a block's run charges none (it shows as the phase `block_run`),
    * so the count tells a compiled reading from one whose steps grow with
    * the work.
    */
  def read[Suspension](
      executor: Executor[Suspension],
      dependencies: ExecutionDependencies,
      program: Instruction,
      limit: Long,
      stop: StopSignal
  ): ProgramReading[Suspension] =
    counted(executor, dependencies, program, limit, stop, "reading_steps")

  /** `read`'s reading, its steps reported under the count's name given: one
    * execution of the executor given, from the start, within the limit and
    * under the cancel (`gezi.hotspot.Budget`). The executor returned is the
    * one the execution left, whether it finished or its budget stopped it,
    * and the one given when the judge's cancel ended it. A reading starts from the tables the executor kept, as its
    * table retention says, the entry data's `table_retention` (`Defaults.executor`).
    */
  private def counted[Suspension](
      executor: Executor[Suspension],
      dependencies: ExecutionDependencies,
      program: Instruction,
      limit: Long,
      stop: StopSignal,
      stepsName: String
  ): ProgramReading[Suspension] =
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
      executor.executed(program, dependencies, gezi.hotspot.Budget(limit, countedUnits = false, stop))
    )
    progress.suspension match
      case None =>
        val (answer, readBack) = Phase.timed("read_back")(progress.found.map(Defunctionalization.instructionTerm).toSet)
        ProgramReading(Some(answer), after, Vector(run, readBack, Count(stepsName, progress.spent.steps)))
      case Some(_) if stop.stopRequested => ProgramReading(None, executor, Vector(run))
      case Some(_)                       => ProgramReading(None, after, Vector(run, Count(stepsName, progress.spent.steps)))

  /** The judgment of the candidate N on the program T, each reading within
    * the limit and under the cancel:
    *
    *   - Proved when N is among T's normal forms (N ∥ T = N then, by
    *     absorption).
    *   - Refuted when all of these hold: T is pure (`ProgramPurity.pure`);
    *     T's reading finished with
    *     exactly one normal form N0; N is not N0, compared as the terms the
    *     readings read back, never as instructions; and N's own reading finished
    *     with exactly one normal form, N itself. Sound: T read to its one
    *     normal form N0 gives T =βη N0, so
    *     NF◇(T) = {N0} (a term βη-equal to one closed normal form has that
    *     normal form alone); N read to itself is a closed βη normal
    *     form (the Output `N ∥ T` is closed), so NF◇(N) = {N} by the same
    *     section; and NF◇(N ∥ T) ⊆ NF◇(N) ∩ NF◇(T) = {N} ∩ {N0} = ∅:
    *     T ⊑_O N fails, and no closed βη normal form is
    *     above `N ∥ T` in ⊑_O. A reading of a program with a choice or a
    *     parallel proves only that T ⊑_O N for each N it read, never that
    *     nothing else is,
    *     so such a program is never refuted.
    *   - Undecided otherwise, a stopped reading included.
    *
    * FIXME: https://github.com/Atry/private-overlay/issues/2048
    * "N is not N0" is decided on the interned terms the readings read back,
    * and is sound only if two different such terms are never α-equivalent
    * λ-terms. The IR has more than one spelling of a λ-term (the trace's
    * `Respell` steps); the readback spells its normal forms by its own
    * construction (`NormalForms.abstracted`, `closedInstruction`), which is
    * meant to be canonical, but no test checks that α-equivalent normal forms
    * read back as one term. Wanted: a law on generated closed normal forms
    * spelled in different ways.
    *
    * The reports are the program's `defunctionalization` and reading
    * (`reading_steps` among them), then, when the refutation is tried, the
    * candidate's `candidate_defunctionalization` and reading, its steps
    * counted as `candidate_reading_steps`.
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/1788): a second reading of the candidate is spent whenever T
    * is pure and its reading finished with exactly one normal form; whether to spend it is fixed here, the only
    * implementation. It is to become an option of one interface chosen by configuration (entry data and `Defaults`)
    * once a second one exists.
    */
  def judged[Suspension](
      executor: Executor[Suspension],
      dependencies: ExecutionDependencies,
      candidate: DeBruijnTerm,
      point: DeBruijnTerm,
      limit: Long,
      stop: StopSignal
  ): JudgmentReading[Suspension] =
    val (program, defunctionalization) = Phase.timed("defunctionalization")(Defunctionalization.thunkInstruction(point))
    val programReading = read(executor, dependencies, program, limit, stop)
    val reports = defunctionalization +: programReading.reports
    programReading.normalForms match
      case Some(found) if found.contains(candidate) => JudgmentReading(Judgment.Proved, programReading.executor, reports)
      case Some(found) if found.size == 1 && !stop.stopRequested && ProgramPurity.pure(point) =>
        val (candidateProgram, candidateDefunctionalization) =
          Phase.timed("candidate_defunctionalization")(Defunctionalization.thunkInstruction(candidate))
        val candidateReading =
          counted(programReading.executor, dependencies, candidateProgram, limit, stop, "candidate_reading_steps")
        val judgment = if candidateReading.normalForms.contains(Set(candidate)) then Judgment.Refuted else Judgment.Undecided
        JudgmentReading(judgment, candidateReading.executor, (reports :+ candidateDefunctionalization) ++ candidateReading.reports)
      case _ => JudgmentReading(Judgment.Undecided, programReading.executor, reports)

  /** The display of a judgment's Output `N ∥ T`: N when proved, no normal
    * form when refuted, the Output itself, not evaluated, otherwise.
    */
  def displayed(output: DeBruijnTerm, candidate: DeBruijnTerm, judgment: Judgment): OutputDisplay = judgment match
    case Judgment.Proved    => OutputDisplay.shown(candidate)
    case Judgment.Refuted   => OutputDisplay.NoNormalForm
    case Judgment.Undecided => OutputDisplay.shown(output)
