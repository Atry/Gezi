package gezi.weakhead

import gezi.ir.Code
import gezi.saturation.StopSignal
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure, Value}

/** The mode a reader takes heads under (evaluators.pl): the two modes of the
  * weak-head evaluator, and the JIT's.
  */
enum Mode:

  /** `weak_head`: no table; the heads in the term's own order, each
    * choice's members left to right, depth first; runs without end on a
    * term whose evaluation re-enters itself, Omega among them.
    */
  case WeakHead

  /** `tabling(weak_head)`: every evaluation tabled (`Tabling`), keyed by the
    * term, an interned value, so a term whose evaluation
    * only re-enters itself has no head and the evaluation ends; the heads as
    * a set.
    */
  case TablingWeakHead

  /** `jit`: the JIT evaluator of the later module `jit`, which
    * answers the heads weak_head answers, in the same order, and which a
    * reader treats as it treats weak_head. The evaluator is the reading
    * configuration's (`ReadingConfiguration.jit`), typed by the configuration as
    * the reading's state is, so that the JIT's terms and the reader's are one
    * configuration's by their types.
    */
  case Jit

/** What the JIT evaluator gives a reader (evaluators.pl's `jit` branch):
  * the module `jit` implements it. The JIT answers the heads the
  * reference answers under weak_head, in the same order, and builds the same
  * run-time values, so a reader treats it as it treats weak_head: untabled,
  * heads that are plain values.
  */
trait JitEvaluator[C <: NativeSpecializer & Singleton]:

  /** The parallel sets of the closed term in the order weak_head gives them,
    * each head as a reader observes it (`jit_observed_head/2`: a value of a
    * backend representation encoded one layer, as the head of the define its
    * codec encodes with), charging the reading's budget for the JIT's own
    * steps.
    */
  def heads(term: Value[C]): Answers[ReadingState[C], ParallelSet[C]]

  /** The configuration of the readings the JIT runs in: its facts' native specializer, its capability and itself. */
  def readingConfiguration: ReadingConfiguration[C]

/** The JIT's part of a reading's state, which the module `jit`
  * defines: what the Prolog JIT kept in the process (its cache of compiled
  * codes, its counts of native calls, decodings and encodings, the numbers
  * of its decodings) and in backtrackable global variables (the path of the
  * readings of its fallback points), here a value the reading threads, kept
  * from one reading of a suite to the next as the Prolog process kept them.
  * A reading that has not met the JIT holds `NoJitState`. Covariant in the configuration `C` of the reading, so that
  * `NoJitState`, which holds nothing of any configuration, is every reading's; the JIT's own state of `C` is the one
  * the JIT reads back (`gezi.jit.JitRunState.of`, a registered conversion of issue 2261, section 8).
  */
trait JitState[+C <: NativeSpecializer & Singleton]:

  /** This state without what it read through the expansions of URI nodes
    * (the answers of its tables), for a reading under another version of the
    * contents those nodes locate (`gezi.hotspot.ExpansionSource`):
    * what it holds of
    * the term's syntax alone, its compiled codes, is kept.
    */
  def withoutAnswers: JitState[C]

  /** This state for a reading that starts now, under a fresh budget: what it
    * keeps of the readings before (tables, compiled codes) kept, and what it
    * counts against one reading's budget (the steps its group blocks wasted,
    * the thunks it gave up) cleared.
    */
  def readingStarted: JitState[C]

/** The JIT's part of a reading that has not met the JIT. */
case object NoJitState extends JitState[Nothing]:
  def withoutAnswers: JitState[Nothing] = this
  def readingStarted: JitState[Nothing] = this

/** A budget of evaluator steps (a Scala reading is
  * bounded by a deterministic count of evaluator steps where the Prolog one
  * was bounded by SWI-Prolog's inference count). What a step is,
  * `WeakHead`'s comment defines.
  *
  * @param spent
  *   the steps taken so far
  * @param limit
  *   the steps allowed
  * @param stop
  *   the stop signal of the fork the reading runs in
  *   (`gezi.hotspot.Forks`), read every
  *   `Budget.stopCheckSteps` steps: a requested stop ends the reading as the
  *   limit does. `StopSignal.NeverStopped` outside a fork, so that a reading
  *   outside one is bounded by its steps alone and stays deterministic. A
  *   reading a stop ended is a stopped reading like one its limit ended;
  *   in a join on the first success its result is discarded, so only the
  *   loser of the race sees the stop, and the winner's reading is the one
  *   it would be alone.
  */
final case class Budget(spent: Long, limit: Long, stop: StopSignal = StopSignal.NeverStopped, ceiling: Long = Long.MaxValue):
  require(limit >= 0, s"a budget's limit is not negative: $limit")

  /** The bound of the steps that is reached first: the limit, or the
    * ceiling (`Long.MaxValue` unless set), the bound a part of the reading is
    * tried under (`ReadingState.attempted`), which every charge reads; the
    * share of the limit a group block may waste is reckoned from `limit`,
    * which stays the reading's own.
    */
  def bound: Long = math.min(limit, ceiling)

  /** The budget after one more step, or nothing when the limit or the
    * ceiling is reached or, at a check, a stop is requested.
    */
  def charged: Option[Budget] =
    if spent >= bound then None
    else if spent % Budget.stopCheckSteps == 0 && stop.stopRequested then None
    else Some(copy(spent = spent + 1))

  /** The budget after `count` more steps, or nothing when they would pass
    * the bound or a stop is requested: the steps of work whose size is known
    * before it is done, charged whole so that work the budget cannot pay for
    * is not started.
    */
  def chargedTimes(count: Long): Option[Budget] =
    require(count >= 0, s"a count of steps is not negative: $count")
    if count > bound - spent then None
    else if stop.stopRequested then None
    else Some(copy(spent = spent + count))

/** A fresh budget. */
object Budget:

  /** No step taken, the limit given. */
  def of(limit: Long): Budget = Budget(0, limit)

  /** No step taken, the limit given, stopped also when the signal asks. */
  def stoppedBy(limit: Long, stop: StopSignal): Budget = Budget(0, limit, stop)

  /** The steps between two reads of the stop signal: a read of a volatile
    * flag at every step would cost more than the step on the JIT's fast
    * path, and 1,024 steps take well under a millisecond
    * (`Reading.stepsPerSecond`).
    */
  val stopCheckSteps: Long = 1024

/** A resource a reading may run out of before its budget of steps (the
  * Prolog reading's `exhausted(Resource)`, there a stack or the table
  * space).
  */
enum Resource:

  /** The tables of the tabled mode: more keys than the reading's table limit
    * would have a table (`ReadingState.tableLimit`).
    */
  case Tables

/** How `tabling(weak_head)` applies a function to a continuation.
  * Both are sound
  * approximations of Definition 14; they differ in the work they share and
  * so in the steps and tables they spend.
  */
enum ContinuationReading:

  /** The β rule as it is: `(λc. S) k` reduces `S` with `k` in place of `c`.
    * Each continuation is a new key, so the work `S` does before it uses `c`
    * is done again for each continuation, once per path of calls.
    * The reference
    * reading, and the default.
    */
  case Substituted

  /** A head `λc. S` whose code uses `c` in tail position only, through at
    * least one step (`gezi.ir.TailPlan`), applied to a continuation `k`, is
    * read as `(λc. S) pack k`, `pack = λm1 … mn. λt. t m1 … mn`, equal by the
    * β rule and equations (8) and (9) when every step's function calls its
    * own continuation in tail position too. `(λc. S) pack` is one closed key
    * for every continuation, so the work before the continuation is shared.
    * The table of that key is read by walking the code's tail plan, each
    * step's function checked as it is reached; a branch whose step does not
    * pass the check is dropped and the head marked unverified
    * (`ReadingState.unverified`), and a consumer that finds its head so
    * marked once it has taken the shared answers reads `S` with `k` in place
    * of `c` as well. Every answer comes from a path whose steps were checked,
    * so none is added; a consumer inside a cycle that takes the shared
    * answers before the mark is made does not read the fallback, and loses
    * answers only. The marks are kept and dropped with the tables
    * (`ReadingState.keptUnverified`), and a table shared through the cache
    * service is kept and found with the mark of its head
    * (`SharedReadingTables`), so that no table is read without its mark.
    */
  case Packed

/** How the weak-head machines take an application apart: an option of the
  * weak-head approximation, not a part of what a program means
  * (`CONTRIBUTING.md`, "What Gezi is": an approximation's order of
  * evaluation and its caching are its behaviour, which another configuration
  * may do otherwise).
  * A reading that finishes gives the same parallel sets under both; the
  * options differ in the steps they charge and, under tabling, in the tables
  * they make.
  */
enum ApplicationReading:

  /** One application at a time, its function first, as the term spells it:
    * a step for each application taken apart, and under tabling a table for
    * each prefix of a spine, so that the variable arguments of keys with a
    * common prefix share that prefix's tables.
    * The
    * simplest option, and the default.
    */
  case ByLayer

  /** A whole spine at once, its arguments read from the flat copy an
    * application keeps (`gezi.ir.Spine`): one step for the spine, and under
    * tabling no table for a prefix shorter than the spine. A known extreme
    * that is a prefix of the spine is found by comparing the extreme's own
    * head and arguments with the spine's head and first arguments, the
    * longest such prefix first, the order in which `ByLayer` meets them.
    *
    * MEASURED 2026-11-20 on the knowledge reading of jmh-pipeline, one copy:
    * untabled, fewer
    * steps (5,629 to 5,239) and less allocation (2.5% to 5.4%); tabled, 23%
    * to 33% less allocation, from fewer tables (488 to 326). A tabled reading
    * that reads successive prefixes of one spine, as `OneSlotEach` reads its
    * slots, finds no table of the longer prefixes it read before (`ByLayer`
    * hits tables of spines of 3 to 12 arguments there), so it applies each
    * prefix again from the head: 2,827 steps against 2,122, a cost that grows
    * with the square of the number of prefixes read.
    *
    * An entry chooses it by its data's reading options (`application`),
    * which `ReadingExecutor` passes.
    */
  case BySpine

  /** A whole spine at once from its longest shared prefix: under tabling, a
    * spine `h a1 … an` is read as its prefix `h a1 … ak` called through that
    * prefix's table, then applied to `ak+1 … an` one at a time with no table
    * between, k the length of its longest proper prefix that either holds a
    * table already or is a divergence point, a prefix that an earlier spine
    * of the reading went on from with another argument than `ak+1`; the head
    * alone, k = 0, when no prefix is either. So a table is made at a spine's
    * end, the key read, and at each prefix where two spines part, the nodes
    * where the binary trie of variable arguments keys branches,
    * and at
    * none of the prefixes between; and a reading of successive prefixes of
    * one spine, which costs `BySpine` the square of their number, reads each
    * from the table of the one before. The prefixes a spine went on from are
    * the state's `spinePrefixes`, an index of the spines read as keys, kept
    * and dropped with the tables. Untabled, it reads as `BySpine`. Known
    * extremes are found as under `BySpine`.
    *
    * A choice of where to table, from the term's structure and the tables the
    * reading holds, decided by no profile, no type and no name: the general
    * deterministic optimisation. A reading that finishes gives the parallel sets of `ByLayer`: every
    * prefix's parallel sets are those of its table or those its function's
    * parallel sets give applied to its argument, which the table holds.
    */
  case BySharedPrefix

/** How `tabling(weak_head)` reads a parallel `M ∥ N`:
  * an option of the
  * weak-head approximation, as `ApplicationReading` is. Both are sound
  * approximations of Definition 14; the second may lose answers the first
  * reads, never add one.
  */
enum ParallelReading:

  /** Both sides read, each parallel set of the left side in parallel with
    * each of the right side's, the right side called again for each. A
    * parallel set of several heads applied to arguments applies each head,
    * so a filter `l ∥ T` applied to a fold's cases applies the fold to the
    * type T itself: for `T = list_type e`, a fold over every list of the
    * type, whose table never completes when the fold's answers are infinitely
    * many (the sum of a list of `binary_set true`: every natural). The
    * reference reading, and the default.
    */
  case BothSides

  /** Each parallel set the tabled body makes of two parallel sets
    * (`WeakHead`'s frame `Paralleled`) met head by head before it is given
    * on: the lambda heads of one code and one list of holes merged into one
    * head of that code, whose fillings are the parallels of theirs, f ∥ g (f
    * where the two share it); and the set dropped, no parallel set given,
    * when two of its lambda heads have as many holes and their codes' bodies
    * are applications of two different of their binders, λx̄. xᵢ M̄ beside
    * λx̄. xⱼ N̄ with i ≠ j. Neutral heads are kept as they are.
    *
    * A filter `l ∥ list_type e` applied to a fold's cases is then one head,
    * `λn c. c (h ∥ e) (t ∥ LT)` for a cons cell l = `cons h t` and the type's
    * `λn c. c e LT`, its nil case dropped, and the fold recurses on the tail
    * met with the type, `t ∥ LT`, one cell at a time, where `BothSides`
    * applies the fold to the type itself. Each meet is a step, with no
    * reading of a normal form and no binder opened.
    *
    * It adds no answer, by a paper proof with no machine check: N ∈ NF◇(T) iff
    * ⟦T⟧ ⊑ ⟦N⟧ for closed T (the theorem), NF◇(T) depends only on ⟦T⟧
    * (corollary 4), and ⟦A ∥ B⟧ = ⟦A⟧ ⊔ ⟦B⟧ (the proof of corollary 3),
    * ⟦ ⟧ being compositional and monotone in DdLP96's model. A code's body
    * is monotone in each of its fillings, so ⟦code[f]⟧ and ⟦code[g]⟧ are
    * both below ⟦code[f ∥ g]⟧, and ⟦code[f] ∥ code[g]⟧ ⊑ ⟦code[f ∥ g]⟧;
    * and every ⟦P⟧ is below ⟦`top`⟧, so a dropped set, read as `top`, is
    * above the set. So for every context C, ⟦C[the set]⟧ ⊑ ⟦C[what is
    * given]⟧, and NF◇(C[what is given]) ⊆ NF◇(C[the set]): the option loses
    * answers in some contexts and adds none in any.
    *
    * What it loses: a merge loses the answers of a context that uses a
    * filling where the two heads' fillings would meet other parts than their
    * own (a code that does not use each filling once in a place of its own);
    * a drop loses the answers of a context that applies the two heads to
    * arguments that make them agree. A witness: (K* ∥ K) Ω Ω = Ω, whose answers are every closed βη normal
    * form, where the set {K*, K} is dropped and gives none.
    *
    * FIXME: only the https://github.com/Atry/private-overlay/issues/2038
    * tabled weak head meets its heads. Under `Mode.Jit`, `WeakHead.heads`
    * hands a term to the JIT, whose parallel (`Jit`'s `JitValue.Parallel`,
    * applied as `JitHead.Parallel`) reads both sides as `BothSides` does, so
    * an entry's executor, which reads under `Mode.Jit`, is not changed by
    * the option. Candidate: the same meet where the JIT applies a parallel
    * head, with the laws read under `Mode.Jit`.
    */
  case HeadsMet

/** The closed terms an evaluation knows to be a greatest or a least term of
  * the contextual preorder ⊑_O (Definition 14, `CONTRIBUTING.md`, "Terms"),
  * each in the spellings the caller lists: the variant of the weak-head
  * evaluator that executes the rules of the two, recognising known spellings
  * of top and bottom. With none listed the evaluator
  * is the plain one.
  *
  * A term is recognised by its spelling and nothing else: it is one of the
  * listed terms, the same interned object (`WeakHead`, KNOWN EXTREMES). The
  * evaluator computes nothing
  * about a term to decide that it is one; a spelling that is not listed is
  * evaluated as any term.
  *
  * WHO LISTS A TERM answers for it: a top T must have M ⊑_O T for every
  * term M, and a bottom B must have B ⊑_O M. A term wrongly listed as a top
  * loses answers; a term wrongly listed as a bottom makes the evaluator
  * answer the empty parallel set, of which every answer is an answer, a
  * false answer. The listing site names the theorem.
  *
  * FIXME (2026-11-11): only the two modes of `WeakHead` read them. The JIT's https://github.com/Atry/private-overlay/issues/1948
  * evaluator (`Mode.Jit`, the module `jit`) evaluates a listed term as any
  * term, so a reading under it with terms listed loses nothing and gains
  * nothing. Candidate fix: the same comparison where `JitRules` takes the
  * heads of a term.
  *
  * @param tops
  *   the spellings of greatest terms, such as top
  * @param bottoms
  *   the spellings of least terms, such as Ω
  */
final case class KnownExtremes(tops: Vector[Pure], bottoms: Vector[Pure]):

  /** Whether no term is listed: the plain evaluator. */
  def isEmpty: Boolean = tops.isEmpty && bottoms.isEmpty

  /** Whether the value spells a listed greatest term: one object, the pure term being one under every configuration. */
  def top[C <: NativeSpecializer & Singleton](term: Value[C]): Boolean =
    tops.exists(listed => listed.representation eq term.representation)

  /** Whether the value spells a listed least term. */
  def bottom[C <: NativeSpecializer & Singleton](term: Value[C]): Boolean =
    bottoms.exists(listed => listed.representation eq term.representation)

/** The known extremes of the plain evaluator. */
object KnownExtremes:

  /** No term listed. */
  val none: KnownExtremes = KnownExtremes(Vector.empty, Vector.empty)

  /** top alone, as a greatest term, and no least term: top in the spelling of
    * the front end's `Literals.top`, pinned equal to the library file
    * `corpora/library/top` (`LiteralConstructorsTest`), a greatest term of ⊑_O
    * by Lean's `contextualTop` (`lean/LambdaJit/ContextualPreorderTop.lean`,
    * stated of `top`, which is this term). Ω is not listed: the contest's
    * reference reading knows `top` alone.
    *
    * A value that callers pass in a state (`ReadingState.knowingTop`), and
    * nothing else: the evaluator reads only `ReadingState.extremes` and
    * compares terms with them by spelling (KNOWN EXTREMES above); it never
    * refers to this value nor to `Literals.top` itself.
    */
  val onlyTop: KnownExtremes = KnownExtremes(
    Vector(gezi.frontend.Defunctionalization.pure(gezi.frontend.Literals.top)),
    Vector.empty
  )

/** The configuration a reading builds and reads its terms under: the native specializer every term it builds goes through,
  * its facts' or `NoFacts`, and the capability to read a storage's view.
  */
final case class ReadingConfiguration[C <: NativeSpecializer & Singleton](
    specializer: C,
    storageAccess: gezi.ir.StorageAccess,
    jit: Option[JitEvaluator[C]] = None
)

object ReadingConfiguration:

  /** The configuration of no facts: terms as written, which is canonical only because `NoFacts` declares no storage, so
    * that a reading under it meets no storage and the capability it holds reads none. The library, an entry's data,
    * the problem corpora and the judge's reference reading are read under it.
    */
  val withoutFacts: ReadingConfiguration[NoFacts.type] = ReadingConfiguration(NoFacts, gezi.ir.StorageAccess.granted())

  // TODO: deleted: `under(mode, weakHead)`, which picked the JIT's configuration out of `Mode.Jit(evaluator)`. Wrong
  // because the mode held an evaluator of no configuration's type; the evaluator is now the configuration's own
  // (`ReadingConfiguration.jit`); issue https://github.com/Atry/private-overlay/issues/2261, design v38, section 4. Read
  // it back with `git show 7669694cc:gezi/weakhead-core/src/main/scala/gezi/weakhead/ReadingState.scala`.

/** The state a reading threads: the evaluator's tables (used under
  * `tabling(weak_head)` only), and the budget.
  *
  * @param tables
  *   the tables of the tabled evaluation, keyed by interned values
  * @param budget
  *   the steps taken and allowed
  * @param tableLimit
  *   the number of tables the tabled mode may hold, complete or not
  * @param exhausted
  *   the resource whose limit stopped the reading, if one did
  * @param configuration
  *   the native specializer the reading builds its terms through and the capability to read a storage's view
  * @param jitState
  *   the JIT's part of the state (`JitState`), `NoJitState` until the JIT
  *   is met
  * @param extremes
  *   the terms the evaluation knows to be a top or a bottom
  *   (`KnownExtremes`). A table holds what the evaluation answered under
  *   them, so they are set on a state that holds no table yet
  *   (`ReadingState.knowing`) and stay for as long as its tables do.
  * @param expansions
  *   the expansion of each URI node the evaluation has expanded
  *   (`gezi.directorysugar.DirectoryTree.expansion`), keyed by the
  *   node, which holds every input of the expansion (how a URI maps to a
  *   path of mixins is its scheme's, and a `file:` URI counts from the root
  *   of the file system) (`Expansions`), kept by the suite's readings
  *   (`nextReading`) and, alone of the state, carried by an owner from one
  *   reading to the next.
  * @param applications
  *   how the weak-head machines take an application apart
  *   (`ApplicationReading`)
  * @param sharing
  *   whether the complete tables of `tabling(weak_head)` are also kept in the
  *   cache service for other readings, and how (`TableSharing`)
  * @param continuations
  *   how `tabling(weak_head)` applies a function to a continuation
  *   (`ContinuationReading`)
  * @param unverified
  *   the heads read under `ContinuationReading.Packed` whose shared table
  *   dropped a branch because a step's function did not pass the check,
  *   which only grows
  * @param codeApplications
  *   the applications of each code the reading has entered so far
  *   (`entered`), when the reading was asked to count them
  *   (`gezi.hotspot.Budget.countedUnits`); none otherwise, so that a
  *   reading that does not count pays one test of the option at each
  *   application. Costs only, never a type
  *   (`gezi.hotspot.Budget`): the count of a
  *   code says how often its instances were entered and nothing about what
  *   they were applied to.
  * @param spinePrefixes
  *   under `ApplicationReading.BySharedPrefix`, for each proper prefix of a
  *   spine the reading read as a key, the argument the first such spine went
  *   on with after it: an index of the keys' spines, from which a later spine
  *   finds the prefix where it parts from them. It holds terms the keys hold
  *   and no judgment; emptying it changes which prefixes are tabled, never an
  *   answer (`CONTRIBUTING.md`, "Tables"). Kept and dropped with the tables
  *   (`keptSpinePrefixes`)
  * @param parallels
  *   how `tabling(weak_head)` reads a parallel (`ParallelReading`)
  * @param storages
  *   how the reading reads the native storages it meets and builds the
  *   parallels it makes (`StorageReading`); none by default, the storages
  *   read by their views and every parallel built as written
  * @param nativeCalls
  *   the natives the storage option called whose results the reading read
  *   (`StorageReading.called`), each also a step of the budget. Costs only,
  *   never a type
  */
final case class ReadingState[C <: NativeSpecializer & Singleton](
    tables: Tables[ReadingState[C], Value[C], ParallelSet[C]],
    budget: Budget,
    tableLimit: Int,
    exhausted: Option[Resource],
    // No default, so that no reading under facts builds its terms as written by omission.
    configuration: ReadingConfiguration[C],
    jitState: JitState[C] = NoJitState,
    extremes: KnownExtremes = KnownExtremes.none,
    expansions: Expansions[C] = Expansions.none[C],
    applications: ApplicationReading = ApplicationReading.ByLayer,
    sharing: TableSharing = TableSharing.Local,
    continuations: ContinuationReading = ContinuationReading.Substituted,
    unverified: Set[Value[C]] = Set.empty[Value[C]],
    spinePrefixes: Map[Value[C], Value[C]] = Map.empty[Value[C], Value[C]],
    codeApplications: Option[Map[Code, Long]] = None,
    parallels: ParallelReading = ParallelReading.BothSides,
    storages: Option[StorageReading[C]] = None,
    nativeCalls: Long = 0
):

  /** The native specializer every term the reading builds goes through. */
  def specializer: C = configuration.specializer

  /** The capability to read a storage's view, which the reading needs to read a storage at a head. */
  def storageAccess: gezi.ir.StorageAccess = configuration.storageAccess

  /** This state with one more application of the code counted, when the
    * reading counts them (`codeApplications`); this state itself otherwise.
    * The machines call it where they enter an instance of a code, a thunk of
    * the code whose holes are all filled replaced by the code's body under
    * the fillings (`WeakHead`, APPLICATIONS COUNTED; the JIT's `JitRules`).
    */
  def entered(code: Code): ReadingState[C] =
    codeApplications match
      case None         => this
      case Some(counts) => copy(codeApplications = Some(counts.updated(code, counts.getOrElse(code, 0L) + 1)))

  /** The state of the next reading of a suite (reading.pl, THE SUITE): the
    * complete tables and the JIT's part kept, the incomplete tables a stop
    * left with their answers found and their producers kept
    * (`Tables.stopped`), and a fresh budget under the same stop signal, so that a suite read in
    * one fork stays stoppable: `next` under `TableRetention.KeptAll`.
    */
  def nextReading(limit: Long): ReadingState[C] =
    copy(tables = tables.stopped, budget = Budget.stoppedBy(limit, budget.stop), exhausted = None, jitState = jitState.readingStarted)

  /** The state of the next reading of the same owner, its tables kept as the
    * retention says:
    * `nextReading`, with no table under `NoneKept`, and with none under
    * `DroppedAtPercent` once the tables held reach that share of the table
    * limit. A table is the memo of a deterministic function (`Tabling`), so
    * dropping one changes no answer, only what a later reading computes
    * again.
    */
  def next(retention: TableRetention, limit: Long): ReadingState[C] =
    nextReading(limit).copy(
      tables = keptTables(retention),
      unverified = keptUnverified(retention),
      spinePrefixes = keptSpinePrefixes(retention)
    )

  /** The tables the next reading of the same owner starts from under the
    * retention (`next`).
    */
  def keptTables(retention: TableRetention): Tables[ReadingState[C], Value[C], ParallelSet[C]] =
    if keeps(retention) then tables.stopped else Tables.empty

  /** The heads marked unverified that the next reading of the same owner
    * starts from under the retention: kept and dropped with the tables
    * (`keptTables`), since a mark qualifies the table of its head applied to
    * the pack, and a table kept without its mark would let a later consumer
    * skip the fallback the mark asks for, so that its answers would depend on
    * what was read before (the review of
    * https://github.com/Atry/private-overlay/pull/1798).
    */
  def keptUnverified(retention: TableRetention): Set[Value[C]] =
    if keeps(retention) then unverified else Set.empty

  /** The index of the keys' spines that the next reading of the same owner
    * starts from under the retention: kept and dropped with the tables
    * (`keptTables`), whose keys it indexes, so that it does not outgrow
    * them.
    */
  def keptSpinePrefixes(retention: TableRetention): Map[Value[C], Value[C]] =
    if keeps(retention) then spinePrefixes else Map.empty

  /** Whether the retention keeps the complete tables for the next reading. */
  private def keeps(retention: TableRetention): Boolean =
    retention match
      case TableRetention.KeptAll  => true
      case TableRetention.NoneKept => false
      case TableRetention.DroppedAtPercent(percent) =>
        require(percent >= 1 && percent <= 100, s"a share of the table limit not between 1 and 100 percent: $percent")
        tables.stopped.held.toLong * 100 < tableLimit.toLong * percent

/** How the tables a reading's state holds are kept for the next reading of
  * the same owner (`ReadingState.next`):
  * implementations of one choice, which an entry's data makes
  * (`table_retention`). The tables' caching policy is configurable: keeping
  * them all in memory and never clearing them is one option, and clearing
  * them at each round replaces none of the others.
  */
enum TableRetention:

  /** Every table kept, never dropped. */
  case KeptAll

  /** No table kept: the next reading starts from none. */
  case NoneKept

  /** Every table kept until the tables held reach `percent` percent of the
    * table limit, then none, so that a long run whose readings each make new
    * keys goes on instead of stopping at the limit; `percent` is 1 to 100.
    */
  case DroppedAtPercent(percent: Int)

/** How a computation tried within a bound of its own ended
  * (`ReadingState.attempted`).
  */
enum Attempt[C <: NativeSpecializer & Singleton, +Result]:
  /** It ended within the bound, with its value. */
  case Finished(value: Result)

  /** It reached its own bound, below the reading's, with no stop requested
    * (or, tried speculatively, exhausted a resource): the state it stopped in,
    * which the caller may keep or drop.
    */
  case OutOfSteps(stopped: ReadingState[C])

/** The state of a fresh reading. */
object ReadingState:

  /** The computation within at most `steps` more steps, under a ceiling of
    * its own (`Budget.ceiling`, the reading's limit left as it is, every charge
    * reading `Budget.bound`): its value and state, the ceiling it found
    * restored; or, when it reached that ceiling below the bound it was tried
    * under, with no stop requested and no resource exhausted, the state before
    * it with its steps spent, and the state it stopped in
    * (`Attempt.OutOfSteps`); any other stop is the reading's, propagated. A
    * `speculative` computation, work the reading would not otherwise ask
    * for, that exhausts a resource is out of steps as well, its state, and so
    * the tables it made, dropped: the reading goes on as if it had not been
    * tried. The one way a part of a reading is given a bound below the
    * reading's own: a parallel set's heads tried in turn (`NormalForms`, not
    * speculative: the reading needs one of them), and, speculative, a
    * lookahead, a group block's entry and the search for a self filling (the
    * JIT's).
    */
  def attempted[C <: NativeSpecializer & Singleton, Result](
      computation: Computation[ReadingState[C], Result],
      steps: Long,
      speculative: Boolean
  ): Computation[ReadingState[C], Attempt[C, Result]] =
    require(steps >= 0, s"a count of steps is not negative: $steps")
    Computation(state =>
      val outer = state.budget
      // The remainder compared first, so that a count near Long.MaxValue does not overflow the sum.
      val ceiling = if steps >= outer.bound - outer.spent then outer.bound else outer.spent + steps
      Trampoline.tailcall(computation.run(state.copy(budget = outer.copy(ceiling = ceiling)))).flatMap {
        case Computed.Done(value, after) =>
          Trampoline.done(Computed.Done(Attempt.Finished(value), after.copy(budget = after.budget.copy(ceiling = outer.ceiling))))
        case Computed.Stopped(after) if ceiling < outer.bound && (speculative || after.exhausted.isEmpty) && !after.budget.stop.stopRequested =>
          Trampoline.done(
            Computed.Done(
              Attempt.OutOfSteps(after.copy(budget = after.budget.copy(ceiling = outer.ceiling))),
              state.copy(budget = outer.copy(spent = after.budget.spent))
            )
          )
        case Computed.Stopped(after) => Trampoline.done(Computed.Stopped(after.copy(budget = after.budget.copy(ceiling = outer.ceiling))))
      }
    )

  /** No table, the budget of the limit, the table limit
    * `defaultTableLimit`, under the configuration.
    */
  def fresh[C <: NativeSpecializer & Singleton](limit: Long, configuration: ReadingConfiguration[C]): ReadingState[C] =
    ReadingState(Tables.empty, Budget.of(limit), defaultTableLimit, None, configuration)

  /** A fresh state of the variant that knows the extremes. */
  def knowing[C <: NativeSpecializer & Singleton](
      limit: Long,
      extremes: KnownExtremes,
      configuration: ReadingConfiguration[C]
  ): ReadingState[C] =
    fresh(limit, configuration).copy(extremes = extremes)

  /** The state every reading of the contest starts from: a fresh state that
    * knows top alone as a greatest term (`KnownExtremes.onlyTop`), no least term
    * (the contest's reference reading knows `top` alone, and each reference
    * answer has its proof). The problem readers of
    * contest-corpora, the judge's executor and reference readers and the
    * generic entry read from it, so that the references and the judge's
    * readings agree. A value its callers pass: the evaluator reads only the
    * state's `extremes`, by spelling, and never refers to `onlyTop`.
    */
  def knowingTop[C <: NativeSpecializer & Singleton](limit: Long, configuration: ReadingConfiguration[C]): ReadingState[C] =
    knowing(limit, KnownExtremes.onlyTop, configuration)

  /** The tables a reading may hold, the counterpart of SWI-Prolog's table
    * space, which the Prolog readings ran under at 32 MB: a tabled reading
    * that makes a new table at nearly every step holds the pending frames of
    * every evaluation in progress, about 1.5 KB of heap per table besides
    * the tables themselves. MEASURED 2026-10-31 in a test JVM of -Xmx256m
    * (the build's small limit) on the random term of `WeakHeadTest` drawn
    * second from seed 20261010, whose evaluation makes a new key at every
    * step: stopped by its budget at 150,000 steps it held 58,696 tables and
    * 143,478 store layers, and run to 200,000 steps it ran out of heap before
    * 78,262 tables; once stopped, 27 MB stayed live. 50,000 leaves the room
    * that a test's other data needs. The legitimately tabled readings of the
    * tests take far fewer: the program of reduction_fibonacci_twenty 1,632
    * tables in Prolog.
    */
  val defaultTableLimit: Int = 50000
