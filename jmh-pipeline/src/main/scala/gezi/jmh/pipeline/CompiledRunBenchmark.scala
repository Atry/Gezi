package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.entry.Defaults
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.EntryData
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.programfamilies.FixedPointLines
import gezi.programfamilies.ProgramFamilies
import gezi.saturation.StopSignal
import gezi.weakhead.Computed
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.NormalForms
import gezi.weakhead.ParallelSet
import gezi.weakhead.ReadingState
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode as BenchmarkModeKind
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import gezi.ir.{Configured, NativeSpecializer, Value}

/** The recursive count of `NativeRouteCompilationTest`
  * (`aRecursiveFunctionsRunCostsALevelDoNotGrow`), a function the program
  * defines by fixpoint that counts the successors of its argument, applied to
  * successor^size zero, at the sizes 8 and 32, compiled by the framework's
  * fixture entry (`contest-entries-fixture/entry.lambdalattice`, read by the
  * framework's generic entry), whose library's naturals the Prolog backend's
  * knowledge represents as big integers. The fixture, not a contributed entry,
  * so that a change of such an entry never moves the benchmark. Each is
  * compiled once, outside the timed calls, as the generic entry compiles a
  * cell's Output (`GenericEntry.run`: the program defunctionalized, the entry's
  * lemma rounds on one e-graph, the last round's
  * `NarrowBlockRoute.compiledRounds`, and the program with its blocks computed,
  * else the extraction, else the program, by the program compiler's
  * `ProgramCompiler.compiledProgram`), and read once by the JIT so that the
  * codes the reading compiles are in the JIT state the timed readings start
  * from. The fields are lazy vals, so no line here is exempt.
  */
@State(Scope.Benchmark)
class CompiledRunInputs:

  private lazy val entry: GenericEntry[?] =
    val (data, afterEntry) =
      EntryData.read(
        FixedPointLines.buildRoot.resolve(CompiledRunInputs.entryDirectory),
        Defaults.entryDataState
      )
    GenericEntryProvider.initialized(
      data,
      gezi.contest.entry.ExecutorModules.registeredFor(
        FixedPointLines.buildRoot.resolve(CompiledRunInputs.entryDirectory)
      ),
      gezi.contest.entry.ExtractorModules.registeredFor(
        FixedPointLines.buildRoot.resolve(CompiledRunInputs.entryDirectory)
      ),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      gezi.contest.entry.Defaults.caches()
    )

  lazy val small: CompiledRun[?] =
    CompiledRunInputs.compiled(entry, CompiledRunInputs.smallSize)

  lazy val large: CompiledRun[?] =
    CompiledRunInputs.compiled(entry, CompiledRunInputs.largeSize)

  // TODO: the compiled runs with a native block mechanism stand here again
  // once a mechanism chooses a block's strategy only from a property proved
  // on the e-graph and written in the term, never from syntax
  // (https://github.com/Atry/private-overlay/issues/1563, section 4.7). The runs with the
  // deleted `BaselineNativeBlocks`, which entered by syntax, read back with
  // `git show 169baa469:lambda_jit/jmh-pipeline/src/main/scala/lambdajit/jmh/pipeline/CompiledRunBenchmark.scala`.

/** A program compiled by the fixture entry's lemma rounds: its size, the term
  * the JIT runs, the JIT state after one reading of it and the entry.
  */
final case class CompiledRun[C <: NativeSpecializer & Singleton](
    size: Int,
    refined: Configured[C],
    warmed: JitState[C],
    entry: GenericEntry[C]
)

object CompiledRunInputs:

  /** The directory of the framework's fixture entry, relative to the build's
    * root.
    */
  val entryDirectory: String = "contest-entries-fixture"

  /** The sizes of `NativeRouteCompilationTest`'s small and middle runs, the
    * largest at which the type check round reached its fixed point within the
    * deleted baseline entry's budget on this program: MEASURED 2026-11-02 (a
    * scratch run of `Schedule.run` on the baseline's schedule), the round ended
    * at its fixed point after 492 instances at 8 (budget 696) and 1,428 at 32
    * (budget 1,464), and exhausted its budget at 64 (2,488) and 128 (4,536).
    * The fixture's rounds run under the generic entry's cap
    * (`GenericEntry.roundCap`), not that budget.
    */
  val smallSize: Int = 8

  val largeSize: Int = 32

  /** The library terms the benchmark's recursive count over successor^size zero
    * is written with, closed instructions read by projection off the program
    * families' fixture file (`TermTables.programFamilyLibraryTerms`).
    */
  private lazy val zero: Term = ProgramFamilies.zero

  private lazy val successor: Term = ProgramFamilies.successor

  private lazy val fixpoint: Term = ProgramFamilies.fixpoint

  /** successor^size zero. */
  def numeral(size: Int): Term =
    (1 to size).foldLeft(zero)((value, _) => successor(value))

  /** The count of the successors of successor^size zero, by fixpoint. */
  def recursiveCount(size: Int): Term =
    fixpoint(λ(self => λ(t => t(zero)(λ(u => successor(self(u)))))))(
      numeral(size)
    )

  /** The program at the size, compiled by the entry's lemma rounds and read
    * once.
    */
  def compiled[C <: NativeSpecializer & Singleton](
      entry: GenericEntry[C],
      size: Int
  ): CompiledRun[C] =
    given C = entry.specializer
    val program = Defunctionalization.thunkInstruction[C](
      recursiveCount(size).deBruijnTerm(Map.empty)
    )
    val (refined, _) =
      ProgramCompiler.compiledProgram(
        ProgramCompilation(
          entry.index,
          entry.rounds,
          entry.natives,
          entry.encoding
        ),
        program,
        explained = false,
        StopSignal.NeverStopped
      )
    val (_, afterFirst) = CompiledRunBenchmark.read(entry, refined, NoJitState)
    CompiledRun(size, refined, afterFirst.jitState, entry)

/** The JIT's run of a loop compiled onto native naturals, against hand-written
  * Scala of the same loop (a recursive count over `BigInt`): its purpose is to
  * tell whether the run phase of the framework's compiled code is within a
  * small factor of native, or whether the cost of a level lies in the framework
  * itself rather than in an entry. The run starts from the JIT state of a first
  * reading, so the codes it needs are compiled and only their run is timed; the
  * compilation (the lemma rounds) is outside the timed calls. The cost of one
  * level is the difference between the two sizes divided by the difference of
  * the sizes; `CompiledRunStepsLawTest` checks that a level costs no more steps
  * at the larger size.
  */
@BenchmarkMode(
  Array(BenchmarkModeKind.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(
  value = 3,
  jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 3, time = 5, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 5, timeUnit = TimeUnit.SECONDS)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
class CompiledRunBenchmark:

  /** The compiled run at size 8. */
  @Benchmark
  def compiledSmall(input: CompiledRunInputs): Vector[Configured[?]] =
    CompiledRunBenchmark.timed(input.small)

  /** The compiled run at size 32. */
  @Benchmark
  def compiledLarge(input: CompiledRunInputs): Vector[Configured[?]] =
    CompiledRunBenchmark.timed(input.large)

  /** The compiled run at size 8, read to its first head only. */
  @Benchmark
  def firstHeadSmall(input: CompiledRunInputs): ParallelSet[?] =
    CompiledRunBenchmark.firstHead(input.small)._1

  /** The compiled run at size 32, read to its first head only. */
  @Benchmark
  def firstHeadLarge(input: CompiledRunInputs): ParallelSet[?] =
    CompiledRunBenchmark.firstHead(input.large)._1

  // TODO: the benchmarks of the compiled runs with native blocks stand here
  // again with those runs (`CompiledRunInputs`, the TODO there).

  /** The hand-written Scala at size 8. */
  @Benchmark
  def handWrittenSmall(): BigInt =
    CompiledRunBenchmark.handWrittenCount(BigInt(CompiledRunInputs.smallSize))

  /** The hand-written Scala at size 32. */
  @Benchmark
  def handWrittenLarge(): BigInt =
    CompiledRunBenchmark.handWrittenCount(BigInt(CompiledRunInputs.largeSize))

object CompiledRunBenchmark:

  /** The normal forms of the compiled program, read from the warmed state. */
  def timed[C <: NativeSpecializer & Singleton](
      run: CompiledRun[C]
  ): Vector[Configured[C]] =
    given C = run.entry.specializer
    val (normalForms, _) = read(run.entry, run.refined, run.warmed)
    normalForms

  /** The first head of the compiled program and the reading state after it,
    * from the warmed state: the run of the program to its represented result,
    * encoded one layer as the JIT's observed head, without reading the rest of
    * the normal form back. Throws `IllegalStateException` when the reading
    * stops or gives no head.
    */
  def firstHead[C <: NativeSpecializer & Singleton](
      run: CompiledRun[C]
  ): (ParallelSet[C], ReadingState[C]) =
    given C = run.entry.specializer
    run.entry.jit
      .heads(Value.of(run.refined))
      .pull
      .result(
        ReadingState
          .fresh(run.entry.readingLimit, run.entry.jit.readingConfiguration)
          .copy(jitState = run.warmed.readingStarted)
      ) match
      case Computed.Done(Some((head, _)), after) => (head, after)
      case Computed.Done(None, after)            =>
        throw IllegalStateException(
          s"no head after ${after.budget.spent} steps"
        )
      case Computed.Stopped(after) =>
        throw IllegalStateException(
          s"the reading stopped after ${after.budget.spent} steps"
        )

  /** The recursive count written in Scala: one level per successor, as the
    * program's fixpoint takes one.
    */
  def handWrittenCount(natural: BigInt): BigInt =
    if natural == 0 then BigInt(0) else handWrittenCount(natural - 1) + 1

  /** The normal forms of the term and the reading state after them, by the
    * entry's JIT within the entry's reading limit; throws
    * `IllegalStateException` when the reading stops, since a stopped reading
    * times nothing the question needs.
    */
  def read[C <: NativeSpecializer & Singleton](
      entry: GenericEntry[C],
      refined: Configured[C],
      jitState: JitState[C]
  )(using C): (Vector[Configured[C]], ReadingState[C]) =
    NormalForms
      .normalForms(Mode.Jit(entry.jit), Value.of(refined))
      .result(
        ReadingState
          .fresh(entry.readingLimit, entry.jit.readingConfiguration)
          .copy(jitState = jitState.readingStarted)
      ) match
      case Computed.Done(normalForms, after) => (normalForms, after)
      case Computed.Stopped(after)           =>
        throw IllegalStateException(
          s"the reading stopped after ${after.budget.spent} steps"
        )
