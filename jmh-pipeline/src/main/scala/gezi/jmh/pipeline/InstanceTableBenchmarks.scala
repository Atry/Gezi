package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.corpora.claims.Spelling
import gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import gezi.contest.corpora.reductions.NominalParameter
import gezi.contest.corpora.reductions.NominalRanges
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.ReductionProblemsRepeated
import gezi.frontend.Defunctionalization
import gezi.ir.Instruction
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.ClosureBackend
import gezi.jit.DispatchMode
import gezi.jit.Jit
import gezi.jit.JitConfiguration
import gezi.jit.PredicatePerCode
import gezi.programfamilies.FixedPointLines
import gezi.strategies.DispatchStrategies
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.weakhead.Values
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup

/** Two programs drawn from the seed 20261031: the family
  * `repeated_reduction_problems_products` at R = 64, and one site of the
  * longest common subsequence's family (`LibraryLongestCommonSubsequences`,
  * direct) of two strings of `InstanceTableInputs.subsequenceLength`
  * characters, whose recursive instances have large fillings; and two JITs over the library modules
  * of `contest-entries-wren`, with the instance table on and off; built once, outside
  * the timed calls. The fields are lazy vals, so no line here is exempt.
  */
@State(Scope.Benchmark)
class InstanceTableInputs:

  lazy val group: ReductionGroup = ReductionGroup(FixedPointLines.buildRoot, Expansions.none, gezi.contest.entry.Defaults.caches())

  lazy val program: Value =
    val term = ReductionProblemsRepeated.Products.point(group, InstanceTableInputs.seed, InstanceTableInputs.repetitions).program
    Values.ofInstruction(Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty)), Set.empty)

  lazy val subsequences: Value =
    val nominal = NominalRanges(
      1 to 1,
      Vector(
        NominalParameter("length", InstanceTableInputs.subsequenceLength to InstanceTableInputs.subsequenceLength),
        NominalParameter("character", 0 to 25)
      )
    )
    val term = LibraryLongestCommonSubsequences(Spelling.Direct, nominal, LibraryLongestCommonSubsequences.name).point(group, InstanceTableInputs.seed, 1).program
    Values.ofInstruction(Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty)), Set.empty)

  private lazy val facts: BackendFacts =
    BackendFacts.of(KnowledgeReadings.compiled(KnowledgeReadings.knowledgeFile, Vector(BackendChecks)))

  private def configured(instanceTable: Boolean): Jit =
    Jit(
      JitConfiguration(
        facts,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.Dispatch(DispatchStrategies.fallback),
        instanceTable = instanceTable
      )
    )

  lazy val tabled: Jit = configured(instanceTable = true)

  lazy val untabled: Jit = configured(instanceTable = false)

object InstanceTableInputs:
  val seed: Long = 20261031
  val repetitions: Int = 64

  /** The length of each string of the longest common subsequence's site:
    * small, so that the reading of main at 5f4ec2a23, which runs an instance
    * whose fillings exceed 64 nodes untabled and so grows exponentially in
    * the length, can be measured beside the reading that tables it.
    */
  val subsequenceLength: Int = 8

  /** The steps a reading may take: the program reads in about a million. */
  val limit: Long = 20000000

/** The JIT's normal-form reading of each program from a fresh state,
  * compilation included, as a point is read, with the instance table on and
  * off (`JitConfiguration.instanceTable`): its purpose is to time the
  * table's own work per instance (the key's hash and comparison, the
  * table's updates), beyond the lookup's charge in steps, on small fillings
  * (products) and on large ones (the subsequence).
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(value = 3, jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 3, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 2, timeUnit = TimeUnit.SECONDS)
class InstanceTableBenchmarks:

  /** The normal forms read with the table on. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def productsTabled(input: InstanceTableInputs): Vector[Instruction] = InstanceTableBenchmarks.read(input.tabled, input.program)

  /** The normal forms read with the table off. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def productsUntabled(input: InstanceTableInputs): Vector[Instruction] = InstanceTableBenchmarks.read(input.untabled, input.program)

  /** The subsequence's normal forms read with the table on. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def subsequenceTabled(input: InstanceTableInputs): Vector[Instruction] = InstanceTableBenchmarks.read(input.tabled, input.subsequences)

object InstanceTableBenchmarks:

  /** The normal forms of the program; throws `IllegalStateException` when
    * the reading stops, since a benchmark of a stopped reading times
    * nothing the points need.
    */
  def read(jit: Jit, program: Value): Vector[Instruction] =
    NormalForms.normalForms(gezi.weakhead.Mode.Jit(jit), program).result(ReadingState.fresh(InstanceTableInputs.limit)) match
      case Computed.Done(normalForms, _) => normalForms
      case Computed.Stopped(after)       => throw IllegalStateException(s"the reading stopped after ${after.budget.spent} steps")
