package gezi.contest.modules.solo

import gezi.hotspot.ArtifactKey
import gezi.hotspot.Budget
import gezi.hotspot.CompilationUnit
import gezi.hotspot.Compiler
import gezi.hotspot.Decision
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.Progress
import gezi.hotspot.Spent
import gezi.hotspot.TieringPolicy
import gezi.narrowblocks.ProgramArtifacts
import gezi.weakhead.ReadingSuspension
import scala.annotation.tailrec
import gezi.ir.{Configured, NativeSpecializer}

/** Which reading of the program a tiered execution has suspended. */
enum Tier[C <: NativeSpecializer & Singleton]:

  /** No reading is suspended: the next decision starts one. */
  case Undecided()

  /** The reading of the program itself. */
  case Interpreting(reading: ReadingSuspension[C])

  /** The reading of the program's compiled artifact. */
  case Compiled(reading: ReadingSuspension[C])

/** Where a tiered execution stopped: the program, what was spent on it and
  * found in it by every call so far, and the reading suspended.
  *
  * @param program
  *   the program unit, whose root is the term the execution was started on
  * @param spent
  *   the steps and applications of every call on the program so far
  * @param seen
  *   the normal forms found so far, which a reading of the compiled program,
  *   reading again what the interpretation read, repeats
  * @param tier
  *   the reading suspended
  */
final case class TieredSuspension[C <: NativeSpecializer & Singleton](
    program: CompilationUnit.Program[C],
    spent: Spent,
    seen: Set[Configured[C]],
    tier: Tier[C]
)

/** The tiered executor:
  * a program read by a reading executor, at each step as the policy decides
  * from what was spent (`TieringPolicy.decided`): the program itself
  * (`Decision.Interpret`), the program compiled into the cache service
  * (`Decision.Compile`), or the compiled program read (`Decision.RunCompiled`),
  * the compiler's artifact looked up under `ArtifactKey(program, configuration)`.
  * Every reading takes the caller's stop, and the steps of all of them
  * together are within the caller's budget. The framework gives the
  * interfaces (`gezi.hotspot.Executor`, the cache service) and leaves the
  * tiered executor to an entry.
  *
  * A compiled program equals the program (the compiler's lemma rounds are
  * sound by Definition 14), so its normal forms are the program's, and the
  * reading of it, started from its root, reads again what the
  * interpretation had read: the normal forms already found are dropped
  * (`TieredSuspension.seen`). The residual of a suspension is the program
  * itself, the coarsest the residual law admits (`exported`).
  *
  * @param specializer
  *   the native specializer of the configuration, which names the compiler's artifacts in the cache service
  *   (`ProgramArtifacts`)
  * @param reading
  *   the reading executor of both tiers, which carries the JIT's state and
  *   the readings' tables from one reading to the next
  * @param compiler
  *   the compiler of program units, whose artifact is the program to read
  * @param policy
  *   the decision at each step
  */
final case class TieredExecutor[C <: NativeSpecializer & Singleton](
    specializer: C,
    reading: Executor[C, ReadingSuspension[C]],
    compiler: Compiler[C, Configured[C]],
    policy: TieringPolicy[C]
) extends Executor[C, TieredSuspension[C]]:

  private given C = specializer

  def executed(term: Configured[C], dependencies: ExecutionDependencies, budget: Budget): (Executor[C, TieredSuspension[C]], ExecutionDependencies, Progress[C, TieredSuspension[C]]) =
    advanced(TieredSuspension[C](CompilationUnit.Program(term), Spent.none, Set.empty, Tier.Undecided()), dependencies, budget)

  def resumed(
      suspension: TieredSuspension[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[C, TieredSuspension[C]], ExecutionDependencies, Progress[C, TieredSuspension[C]]) =
    advanced(suspension, dependencies, budget)

  /** The program the suspension was started on, a residual by the law the
    * reading executors' own export rests on: each normal form N found is one
    * of the program T's, T ⊑_O N, and the choice is the meet of ⊑_O, so
    * N + T ≃_O T.
    */
  def exported(suspension: TieredSuspension[C], dependencies: ExecutionDependencies): (ExecutionDependencies, Option[Configured[C]]) =
    (dependencies, Some(suspension.program.root))

  /** The suspension advanced by the policy's decisions until the program is
    * read to its end, the caller's steps or stop end it, or the policy gives
    * up: the executor after it, with the reading executor the last reading
    * left, and the normal forms this call found.
    */
  private def advanced(
      start: TieredSuspension[C],
      dependencies: ExecutionDependencies,
      budget: Budget
  ): (Executor[C, TieredSuspension[C]], ExecutionDependencies, Progress[C, TieredSuspension[C]]) =
    val artifacts = ProgramArtifacts[C](specializer)
    @tailrec
    def loop(
        executor: TieredExecutor[C],
        dependencies: ExecutionDependencies,
        suspension: TieredSuspension[C],
        spentInCall: Spent,
        found: Vector[Configured[C]]
    ): (Executor[C, TieredSuspension[C]], ExecutionDependencies, Progress[C, TieredSuspension[C]]) =
      def suspended = (executor, dependencies, Progress(found, Some(suspension), spentInCall))
      val stepsLeft = budget.steps - spentInCall.steps
      if stepsLeft <= 0 || budget.stop.stopRequested then suspended
      else
        executor.policy.decided(suspension.program, suspension.spent, dependencies.cache) match
          case Decision.GiveUp() => suspended
          case Decision.Compile(units) =>
            val (compiler, compiled) = units.foldLeft((executor.compiler, dependencies)) { case ((compiler, before), unit) =>
              val (next, after, _) = compiler.compiled(TieredExecutor.root(unit), unit, before, budget.stop)
              (next, after)
            }
            // A compilation the caller's stop ended wrote nothing, and a provider may drop an artifact at once
            // (`gezi.hotspot.Retention`): the call ends there rather than compile again in a loop, and the next
            // call decides afresh.
            val written = units.forall(unit =>
              compiled.cache.locked(artifacts)(_.tryGet(ArtifactKey[C, Configured[C]](unit, compiler.configuration))).isDefined
            )
            if budget.stop.stopRequested || !written then (executor.copy(compiler = compiler), compiled, Progress(found, Some(suspension), spentInCall))
            else loop(executor.copy(compiler = compiler), compiled, suspension.copy(tier = Tier.Undecided()), spentInCall, found)
          case Decision.Interpret(allowed) =>
            val started = suspension.tier match
              case Tier.Interpreting(reading) => executor.reading.resumed(reading, dependencies, executor.capped(allowed, stepsLeft, budget))
              case Tier.Undecided() | Tier.Compiled(_) =>
                executor.reading.executed(suspension.program.root, dependencies, executor.capped(allowed, stepsLeft, budget))
            stepped(executor, suspension, spentInCall, found, started, Tier.Interpreting(_))
          case Decision.RunCompiled(allowed) =>
            val started = suspension.tier match
              case Tier.Compiled(reading) => executor.reading.resumed(reading, dependencies, executor.capped(allowed, stepsLeft, budget))
              case Tier.Undecided() | Tier.Interpreting(_) =>
                val artifact = dependencies.cache
                  .locked(artifacts)(_.tryGet(ArtifactKey[C, Configured[C]](suspension.program, executor.compiler.configuration)))
                  .getOrElse(throw AssertionError(s"the policy ran a compiled program whose artifact is not in the cache service: ${executor.policy}"))
                executor.reading.executed(artifact, dependencies, executor.capped(allowed, stepsLeft, budget))
            stepped(executor, suspension, spentInCall, found, started, Tier.Compiled(_))

    /** The loop after one reading: finished when the reading finished, else
      * on with its suspension in the tier it ran in.
      */
    def stepped(
        executor: TieredExecutor[C],
        suspension: TieredSuspension[C],
        spentInCall: Spent,
        found: Vector[Configured[C]],
        result: (Executor[C, ReadingSuspension[C]], ExecutionDependencies, Progress[C, ReadingSuspension[C]]),
        tier: ReadingSuspension[C] => Tier[C]
    ): (Executor[C, TieredSuspension[C]], ExecutionDependencies, Progress[C, TieredSuspension[C]]) =
      val (reading, dependencies, progress) = result
      val fresh = progress.found.filterNot(suspension.seen).distinct
      val next = executor.copy(reading = reading)
      val advancedSuspension = suspension.copy(
        spent = TieredExecutor.added(suspension.spent, progress.spent),
        seen = suspension.seen ++ fresh,
        tier = progress.suspension.fold(Tier.Undecided[C]())(tier)
      )
      val nowSpent = TieredExecutor.added(spentInCall, progress.spent)
      progress.suspension match
        case None    => (next, dependencies, Progress(found ++ fresh, None, nowSpent))
        case Some(_) => loop(next, dependencies, advancedSuspension, nowSpent, found ++ fresh)

    loop(this, dependencies, start, Spent.none, Vector.empty)

  /** A decision's budget with the caller's stop, and its steps capped by
    * the caller's steps left.
    */
  private def capped(allowed: Budget, stepsLeft: Long, budget: Budget): Budget =
    Budget(allowed.steps.min(stepsLeft), allowed.countedUnits || budget.countedUnits, budget.stop)

object TieredExecutor:

  /** The term a unit is compiled from: a program unit's root. Throws
    * `IllegalArgumentException` for a code or a closure unit, which the
    * compiler of program units refuses.
    */
  def root[C <: NativeSpecializer & Singleton](unit: CompilationUnit[C]): Configured[C] = unit match
    case CompilationUnit.Program(root) => root
    case other                         => throw IllegalArgumentException(s"solo's tiered executor compiles program units, not $other")

  /** Two costs added: the steps, and the applications of each unit. */
  def added(first: Spent, second: Spent): Spent =
    Spent(
      first.steps + second.steps,
      second.applications.foldLeft(first.applications) { case (sum, (unit, count)) => sum.updated(unit, sum.getOrElse(unit, 0L) + count) }
    )
