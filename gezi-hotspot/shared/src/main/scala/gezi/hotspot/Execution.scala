package gezi.hotspot

import gezi.saturation.StopSignal
import gezi.ir.{Code, Configured, NativeSpecializer}

/** One way of running a term of the configuration `C`. An executor is
  * a value; what it keeps between calls (compiled codes, its own tables,
  * counts) is in the executor it returns.
  *
  * `Suspension` is the executor's own opaque value: only the executor that
  * made it resumes it, which the type parameter enforces, since a
  * suspension of one executor handed to another does not compile. A
  * suspension may be kept and resumed later, more than once, unless the
  * executor's documentation says otherwise.
  */
trait Executor[C <: NativeSpecializer & Singleton, Suspension]:

  /** The term run within the budget, from the start. */
  def executed(term: Configured[C], dependencies: ExecutionDependencies, budget: Budget): (Executor[C, Suspension], ExecutionDependencies, Progress[C, Suspension])

  /** The suspension run on within the budget. */
  def resumed(suspension: Suspension, dependencies: ExecutionDependencies, budget: Budget): (Executor[C, Suspension], ExecutionDependencies, Progress[C, Suspension])

  /** The suspension exported as a residual term,
    * or nothing. Nothing is always allowed: the suspension is not at a safe
    * point, its heap has a cycle, or the executor does not export at all.
    * A residual r satisfies the residual law: the
    * term equals the normal forms found so far chosen with r.
    *
    * The reading executors (`gezi.weakhead.ReadingExecutor`, the JIT's
    * included) export the program they were started on, the coarsest residual
    * the law admits, which `ExecutorLaws.residualLaw` checks. The framework
    * promises safe points only between two top-level normal forms; a finer
    * granularity waits for an executor that shows its state is written back to
    * the IR, with a sharing β-redex for a shared thunk. Deoptimization is a
    * handover by this method.
    */
  def exported(suspension: Suspension, dependencies: ExecutionDependencies): (ExecutionDependencies, Option[Configured[C]])

  /** The program this executor runs for a Moore machine state
    * (`corpora/library/java_ffi/moore`), the state under the filter it reads
    * it by, or none for an executor that runs no FFI program.
    */
  def foreignProgram(state: Configured[C]): Option[Configured[C]] = None

  /** The program of `foreignProgram`, or a compilation of it, run within the
    * budget, calling the dependencies' service (`ExecutionDependencies.foreign`).
    * How it is run is this executor's: it may lose answers, and adds none. An
    * executor that runs no FFI program has no answer, a false negative.
    */
  def interacted(
      program: Configured[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[C, Suspension], ExecutionDependencies, ForeignProgress[C]) =
    (this, dependencies, ForeignProgress(Vector.empty, finished = true, Spent.none))

/** What an execution may spend, and which counts it is asked to keep.
  *
  * @param steps
  *   the evaluator steps the execution may take
  * @param countedUnits
  *   whether the execution counts the applications of each unit
  *   (`Spent.applications`); counting costs time, so it is done only when
  *   asked, and it changes nothing an execution
  *   finds or spends but the counts
  * @param stop
  *   the caller's cancel (the judge's, a fork's): once it is requested the
  *   execution stops at its next check and suspends where a budget run out
  *   would suspend it, so that the executor it returns holds no state of a
  *   computation the cancel dropped
  */
final case class Budget(steps: Long, countedUnits: Boolean, stop: StopSignal):
  require(steps >= 0, s"a budget's steps are not negative: $steps")

/** The values every executor takes and returns across executors and across
  * points: the cache service ([[Cache]]) and the
  * version of the contents the URI nodes an execution meets expand to. The
  * cache is a service, not a value: an execution reads and writes it in
  * place through `Cache.locked`, and the dependencies it returns hold the same
  * cache and source.
  *
  * @param cache
  *   the cache service the executions share
  * @param source
  *   the version of what the URI nodes expand to (`ExpansionSource`), which
  *   the adapter gives for each run of a cell, since only it knows whether
  *   its files change
  * @param foreign
  *   the external service an FFI program calls, which the adapter gives; none for an
  *   execution that runs no FFI program
  */
final case class ExecutionDependencies(cache: Cache, source: ExpansionSource, foreign: ForeignService = ForeignService.Absent)

/** The version of the contents the URI nodes an execution meets expand to
  * (`gezi.directorysugar.DirectoryTree.expansion`), compared by identity.
  * Whoever runs an execution gives one under which the content a URI locates
  * does not change, so that a table read under it, kept by an executor or in
  * the cache service, never answers from an older content than a reading of
  * the same version would read: the judge one for
  * its run, whose files do not change while it runs; the kernel one for each
  * cell, since its files may change between cells.
  */
final class ExpansionSource private ()

/** The versions of expanded contents. */
object ExpansionSource:

  /** A version nothing was yet read under. */
  def fresh(): ExpansionSource = new ExpansionSource()

/** What one execution gives: the normal forms found in this call, each the
  * closed thunk of the IR that the weak-head reader gives at depth 0
  * (`gezi.weakhead.NormalForms.normalForm`), a term of the configuration the
  * execution read under; the suspended state if it did not finish, and what
  * it cost.
  *
  * @param found
  *   the normal forms found in this call
  * @param suspension
  *   what `Executor.resumed` runs on, when the execution did not finish
  */
final case class Progress[C <: NativeSpecializer & Singleton, Suspension](found: Vector[Configured[C]], suspension: Option[Suspension], spent: Spent)

/** What an execution cost: costs only, never a type and never a term, so that one record serves every
  * configuration. `applications` has entries only when the budget asked for counted units, and only for codes
  * (the units `CompilationUnit.Code`): each entry of an instance of the code as the executor's machine defines it
  * (`gezi.weakhead.WeakHead`, APPLICATIONS COUNTED, and `gezi.jit.Jit`, the same section). A code an execution did
  * not apply has no entry, so every count is positive.
  *
  * @param steps
  *   the evaluator steps the execution took
  * @param applications
  *   the applications of each code in the execution, when counted
  */
final case class Spent(steps: Long, applications: Map[Code, Long]):
  require(steps >= 0, s"spent steps are not negative: $steps")

/** The costs of nothing done. */
object Spent:
  val none: Spent = Spent(0, Map.empty)
