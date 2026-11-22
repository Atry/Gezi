package gezi.weakhead

import gezi.ir.Instruction
import gezi.hotspot.CompilationUnit
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ExpansionSource
import gezi.hotspot.NormalForm
import gezi.hotspot.Progress
import gezi.hotspot.Spent
import scala.annotation.tailrec

/** Where a reading of normal forms stopped: the stream of the normal forms
  * not yet read and the reading's state just before it was pulled, the last
  * point between two top-level normal forms the reading passed, the normal
  * forms read so far, which a later one equal to them repeats, and the
  * version of the contents the URI nodes expand to that the reading read
  * under, which its state's tables hold answers of; and the program the
  * reading was started on, which `exported` gives. Pulling the stream from
  * the state is a pure function of them, so a suspension may be resumed any
  * number of times.
  */
final case class ReadingSuspension(
    program: Instruction,
    rest: Answers[ReadingState, Instruction],
    state: ReadingState,
    seen: Set[Instruction],
    source: ExpansionSource
)

/** A reader of normal forms under a mode as an executor
  * (`gezi.hotspot.Executor`):
  * the weak-head reference under `Mode.TablingWeakHead` (or the untabled
  * `Mode.WeakHead` it is built on),
  * and the JIT under `Mode.Jit` (the module `jit` builds that one). It reads
  * what `NormalForms.normalForms` reads, in the same order, within a budget
  * of evaluator steps (`Budget`, the steps as `WeakHead` defines them).
  *
  * A stop suspends the reading at the last point between two top-level
  * normal forms it passed (the granularity the framework promises,
  * `gezi.hotspot.Executor`): the normal form being read when the budget ran out
  * is read again from its start when the suspension is resumed, so a
  * resumed reading spends again the steps the stopped pull had spent.
  * `Spent.steps` is the steps this call took, those included. The executor
  * keeps the JIT's state (its compiled codes) between calls, as the entries
  * keep it between points; the weak-head modes have none. It keeps the
  * readings' tables between calls as its table retention says. What it keeps
  * holds for the version of the contents the URI nodes expand to that the
  * call's dependencies gave (`ExecutionDependencies.source`): a call under another
  * version starts from no table and from the JIT state without its answers
  * (`JitState.withoutAnswers`), so that no reading answers from contents a
  * reading of that version would not read.
  *
  * A budget that asks for counted units (`countedUnits`) has the call count
  * the applications of each code (`gezi.hotspot.CompilationUnit.Code`) its
  * reading enters, the event `WeakHead` defines (APPLICATIONS COUNTED) and,
  * under `Mode.Jit`, the one the JIT's `JitRules` defines; `Spent.applications`
  * is what this call counted, as `Spent.steps` is what this call took, the
  * pull a stop suspended included and a pull a cancel dropped left out.
  * Counting changes nothing else: the normal forms, the steps and the tables
  * are those of a call that does not count. Closures
  * (`gezi.hotspot.CompilationUnit.Closure`) are not counted.
  *
  * A suspension is exported as the program the reading was started on
  * (`exported`), the coarsest residual the framework admits: the
  * residual law holds, the term being equal to the normal
  * forms found so far chosen with the term itself, since each normal form N
  * found is one of the term's, T ⊑_O N, and the choice is the meet of ⊑_O,
  * so N + T ≃_O T. The executor handed the residual reads again what this
  * one had read, and repeats the normal forms found, which a caller that
  * keeps them drops. FIXME
  * (https://github.com/Atry/private-overlay/issues/1549): the residual is to be the
  * choice of the root's members not yet unfolded, read back to the IR, with
  * a shared subterm written once as a β-redex, so that nothing read is read
  * again; the stream `rest` holds them only as a computation, not as terms.
  *
  * @param mode
  *   the mode the heads are taken under
  * @param jitState
  *   the JIT's part of the state the next execution starts from
  * @param sharedRetention
  *   whether the complete tables of `tabling(weak_head)` are kept in the
  *   cache service of the execution's dependencies, so that this executor's later
  *   executions and other executors read them, and how eagerly the service
  *   may drop them (`TableSharing`);
  *   none keeps them in the reading's state alone, as every reading did
  *   before
  * @param source
  *   the version of the contents the URI nodes expand to (`ExpansionSource`)
  *   under which the tables and the JIT state kept here were read: the
  *   dependencies of the call that left them, none before the first call
  * @param applications
  *   how the weak-head machines take an application apart
  *   (`ApplicationReading`), an option of the approximation that a reading
  *   keeps through its resumptions
  * @param tableRetention
  *   which tables a call leaves for the next call of this executor
  *   (`TableRetention`):
  *   none, as every call did before, all, or all until they reach a share of
  *   the table limit
  * @param tables
  *   the tables the next call starts from, those an earlier call left under
  *   the retention; none at first
  * @param unverified
  *   the heads marked unverified (`ReadingState.unverified`) that the next
  *   call starts from, kept and dropped with `tables` under the retention
  *   (`ReadingState.keptUnverified`); none at first
  * @param continuations
  *   how the tabled weak head applies a function to a continuation
  *   (`ContinuationReading`),
  *   an option of the approximation that a reading keeps through its
  *   resumptions
  * @param parallels
  *   how the tabled weak head reads a parallel (`ParallelReading`),
  *   an option of the
  *   approximation that a reading keeps through its resumptions
  * @param spinePrefixes
  *   the index of the keys' spines (`ReadingState.spinePrefixes`) that the
  *   next call starts from, kept and dropped with `tables` under the
  *   retention (`ReadingState.keptSpinePrefixes`); none at first
  */
final case class ReadingExecutor(
    mode: Mode,
    jitState: JitState,
    sharedRetention: Option[gezi.hotspot.Retention] = None,
    source: Option[ExpansionSource] = None,
    applications: ApplicationReading = ApplicationReading.ByLayer,
    tableRetention: TableRetention = TableRetention.NoneKept,
    tables: Tables[ReadingState, Value, ParallelSet] = Tables.empty,
    unverified: Set[Value] = Set.empty,
    continuations: ContinuationReading = ContinuationReading.Substituted,
    parallels: ParallelReading = ParallelReading.BothSides,
    spinePrefixes: Map[Value, Value] = Map.empty
) extends Executor[ReadingSuspension]:

  /** The normal forms of the closed term read from the tables an earlier
    * call left (`tables`) within the budget's steps, counting the
    * applications of codes when the budget asks. The reading stops under the
    * budget's stop signal as under its steps (`Budget.stoppedBy`).
    *
    * FIXME (https://github.com/Atry/private-overlay/issues/1788): the start state here (`ReadingState.knowingTop`) fixes
    * the known extremes to top alone, and `resumed` keeps them; whether an entry may know more is for the contest's
    * rules to say. The table limit it fixes is the reading's resource limit, which an entry does not set
    * (`gezi.contest.entry.EntryData`: an entry sets no limit of its own).
    */
  def executed(
      term: Instruction,
      dependencies: ExecutionDependencies,
      budget: gezi.hotspot.Budget
  ): (ReadingExecutor, ExecutionDependencies, Progress[ReadingSuspension]) =
    pulled(term, NormalForms.normalForm(mode, ReadOut.Whole, term), started(dependencies, budget), Set.empty, Vector.empty, dependencies)

  /** A computation of this executor's reading state run within the budget,
    * from the state a reading of a term starts from (`started`): this
    * executor after it, its result, none when the budget or its stop signal
    * ended it, and the steps it took. A computation the stop signal cancels
    * is dropped as a pull is (`pulled`). For a module that reads by its
    * evaluator something other than normal forms.
    *
    * THE CONTRACT: the computation reads only through the evaluator
    * (`gezi.jit.Jit.representedHeads` and the like) and never replaces or
    * modifies the state itself (`Computation.replaced`, `Computation.modified`):
    * this executor keeps the state it ends in, and table sharing hands its
    * tables to other readings, so a table a module wrote would answer them.
    *
    * FIXME (found in a review): the contract https://github.com/Atry/private-overlay/issues/1947
    * is kept by review and not by the type. This module cannot name the JIT's types,
    * so the signature is generic over any computation of the reading state.
    */
  def computed[Result](
      computation: Computation[ReadingState, Result],
      dependencies: ExecutionDependencies,
      budget: gezi.hotspot.Budget
  ): (ReadingExecutor, Option[Result], Long) =
    val state = started(dependencies, budget)
    computation.resultUnless(state, budget.stop) match
      case None                               => (left(state, dependencies), None, 0L)
      case Some(Computed.Done(result, after)) => (left(after, dependencies), Some(result), after.budget.spent)
      case Some(Computed.Stopped(after))      => (left(after, dependencies), None, after.budget.spent)

  /** The suspended reading pulled on from its state, with a fresh budget of
    * the budget's steps, stopped by the budget's stop signal and not by the
    * signal of the call that suspended it, which belongs to that call (a
    * cancelled call's signal stays requested), and with this executor's JIT
    * state, so that the codes compiled since the suspension are not compiled
    * again, and with no application counted yet, counting when the budget
    * asks. Throws `IllegalArgumentException` for dependencies whose source is
    * not the one the reading was read under: a reading is resumed under the
    * contents it started on. The JIT state is taken without its answers when
    * this executor's was read under another source.
    */
  def resumed(
      suspension: ReadingSuspension,
      dependencies: ExecutionDependencies,
      budget: gezi.hotspot.Budget
  ): (ReadingExecutor, ExecutionDependencies, Progress[ReadingSuspension]) =
    if suspension.source ne dependencies.source then
      throw IllegalArgumentException("a stopped reading is resumed under the expansion source it was read under")
    val start =
      suspension.state.copy(
        budget = Budget.stoppedBy(budget.steps, budget.stop),
        exhausted = None,
        jitState = if source.contains(dependencies.source) then jitState else jitState.withoutAnswers,
        sharing = sharing(dependencies),
        codeApplications = counting(budget)
      )
    pulled(suspension.program, suspension.rest, start, suspension.seen, Vector.empty, dependencies)

  /** The program the suspended reading was started on, the residual the
    * class's Scaladoc describes.
    */
  def exported(suspension: ReadingSuspension, dependencies: ExecutionDependencies): (ExecutionDependencies, Option[Instruction]) =
    (dependencies, Some(suspension.program))

  /** The state a reading of a term starts from: the tables this executor
    * keeps, the budget's steps, stopped by its stop signal, the counts of
    * applications when the budget asks for them, and this executor's JIT
    * state, sharing and readings of applications and continuations; no
    * table, no head marked unverified, and the JIT state
    * without its answers when the dependencies' source is not the one they were
    * read under.
    */
  private def started(dependencies: ExecutionDependencies, budget: gezi.hotspot.Budget): ReadingState =
    val sameContents = source.contains(dependencies.source)
    ReadingState
      .knowingTop(budget.steps)
      .copy(
        tables = if sameContents then tables else Tables.empty,
        budget = Budget.stoppedBy(budget.steps, budget.stop),
        jitState = if sameContents then jitState else jitState.withoutAnswers,
        sharing = sharing(dependencies),
        applications = applications,
        continuations = continuations,
        parallels = parallels,
        unverified = if sameContents then unverified else Set.empty,
        codeApplications = counting(budget),
        spinePrefixes = if sameContents then spinePrefixes else Map.empty
      )

  /** The progress of a call: the normal forms found, the suspension, and
    * what the call spent, read off the state it is reported from: its steps
    * and, when counted, its applications of codes.
    */
  private def progress(
      found: Vector[NormalForm],
      suspension: Option[ReadingSuspension],
      spentIn: ReadingState
  ): Progress[ReadingSuspension] =
    Progress(
      found,
      suspension,
      Spent(
        spentIn.budget.spent,
        spentIn.codeApplications.fold(Map.empty[CompilationUnit, Long])(_.map((code, count) => (CompilationUnit.Code(code), count)))
      )
    )

  /** The stream pulled from the state until it ends or the budget stops a
    * pull, each normal form not seen before added to those found. A pull
    * that the budget's stop signal cancels between two of its checks
    * (`Computation.resultUnless`) is dropped: the reading is suspended
    * before it, as a budget stop suspends it, and the executor keeps the JIT
    * state the pull started from, since the dropped pull's state marks the
    * instances it was reading (the cycle check of `Judgments`), which a
    * later reading would take the cycle exit on, and the tables of that
    * state. The dropped pull's steps and applications are not counted. The
    * executor returned keeps the JIT state and the tables its retention keeps
    * of the state the call ended in (`left`).
    */
  @tailrec
  private def pulled(
      program: Instruction,
      answers: Answers[ReadingState, Instruction],
      state: ReadingState,
      seen: Set[Instruction],
      found: Vector[NormalForm],
      dependencies: ExecutionDependencies
  ): (ReadingExecutor, ExecutionDependencies, Progress[ReadingSuspension]) =
    answers.pull.resultUnless(state, state.budget.stop) match
      case None =>
        (left(state, dependencies), dependencies, progress(found, Some(ReadingSuspension(program, answers, state, seen, dependencies.source)), state))
      case Some(Computed.Done(None, after)) =>
        (left(after, dependencies), dependencies, progress(found, None, after))
      case Some(Computed.Done(Some((normalForm, rest)), after)) =>
        if seen.contains(normalForm) then pulled(program, rest, after, seen, found, dependencies)
        else pulled(program, rest, after, seen + normalForm, found :+ normalForm, dependencies)
      case Some(Computed.Stopped(after)) =>
        (left(after, dependencies), dependencies, progress(found, Some(ReadingSuspension(program, answers, state, seen, dependencies.source)), after))

  /** This executor for the next call after a call under the dependencies that
    * ended in the state: its JIT state, the tables the retention keeps of it,
    * and the dependencies' source, which they were read under.
    */
  private def left(state: ReadingState, dependencies: ExecutionDependencies): ReadingExecutor =
    copy(
      jitState = state.jitState,
      tables = state.keptTables(tableRetention),
      unverified = state.keptUnverified(tableRetention),
      spinePrefixes = state.keptSpinePrefixes(tableRetention),
      source = Some(dependencies.source)
    )

  /** The sharing of the readings' complete tables in the dependencies' cache
    * service, or none.
    */
  private def sharing(dependencies: ExecutionDependencies): TableSharing =
    sharedRetention.fold(TableSharing.Local)(retention => TableSharing.Shared(dependencies.cache, retention, dependencies.source))

  /** The counts of applications a call under the budget starts from: none
    * counted yet when the budget asks for them, no counting otherwise.
    */
  private def counting(budget: gezi.hotspot.Budget): Option[Map[gezi.ir.Code, Long]] =
    Option.when(budget.countedUnits)(Map.empty)

/** The weak-head reference as an executor. */
object ReadingExecutor:

  /** The weak-head reference under `tabling(weak_head)`, with no JIT state. */
  val tablingWeakHead: ReadingExecutor = ReadingExecutor(Mode.TablingWeakHead, NoJitState)
