package com.yang_bo.gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import com.yang_bo.gezi.contest.corpora.claims.Spelling
import com.yang_bo.gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import com.yang_bo.gezi.contest.corpora.reductions.NominalParameter
import com.yang_bo.gezi.contest.corpora.reductions.NominalRanges
import com.yang_bo.gezi.contest.corpora.reductions.ReductionGroup
import com.yang_bo.gezi.contest.corpora.reductions.ReductionProblemsRepeated
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.ClosureBackend
import com.yang_bo.gezi.jit.DispatchMode
import com.yang_bo.gezi.jit.Jit
import com.yang_bo.gezi.jit.StorageEncoding
import com.yang_bo.gezi.jit.JitConfiguration
import com.yang_bo.gezi.jit.PredicatePerCode
import com.yang_bo.gezi.programfamilies.FixedPointLines
import com.yang_bo.gezi.strategies.DispatchStrategies
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.NormalForms
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.Values
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** Two programs drawn from the seed 20261031: the family
  * `repeated_reduction_problems_products` at R = 64, and one site of the
  * longest common subsequence's family (`LibraryLongestCommonSubsequences`,
  * direct) of two strings of `InstanceTableInputs.subsequenceLength`
  * characters, whose recursive instances have large fillings; and two JITs over
  * the benchmarks' generated knowledge for an executor
  * (`KnowledgeReadings.executorKnowledgeTerm`), with the instance table on and
  * off; built once, outside the timed calls. The fields are lazy vals, so no
  * line here is exempt.
  */
@State(Scope.Benchmark)
class InstanceTableInputs:

  lazy val group: ReductionGroup = ReductionGroup(
    FixedPointLines.buildRoot,
    Expansions.none,
    com.yang_bo.gezi.contest.entry.Defaults.caches()
  )

  /** The two programs and the two JITs, in the configuration of the encoding of
    * the executor knowledge's facts, which the setup's type parameter names for
    * the benchmarks that open it.
    */
  lazy val setup: InstanceTableSetup[?] =
    val library = KnowledgeReadings.compiled(
      KnowledgeReadings.executorKnowledgeTerm,
      Vector(BackendChecks)
    )
    val encoding = BackendFacts.of(library).storageEncoding
    InstanceTableInputs.setupOf[encoding.type](encoding, group)

/** The programs read in the configuration `C` and the two JITs that read them,
  * the instance table on and off.
  */
final case class InstanceTableSetup[C <: NativeSpecializer & Singleton](
    program: Value[C],
    subsequences: Value[C],
    tabled: Jit[C],
    untabled: Jit[C]
):

  /** The specializer of the configuration, the one the JITs are built over. */
  def specializer: C = tabled.configuration.specializer

object InstanceTableInputs:
  val seed: Long = 20261031

  /** The programs and the two JITs over the encoding. */
  def setupOf[C <: NativeSpecializer & Singleton](
      encoding: StorageEncoding & C,
      group: ReductionGroup
  ): InstanceTableSetup[C] =
    given C = encoding
    val products =
      ReductionProblemsRepeated.Products.point(group, seed, repetitions).program
    val nominal = NominalRanges(
      1 to 1,
      Vector(
        NominalParameter("length", subsequenceLength to subsequenceLength),
        NominalParameter("character", 0 to 25)
      )
    )
    val subsequence = LibraryLongestCommonSubsequences(
      Spelling.Direct,
      nominal,
      LibraryLongestCommonSubsequences.name
    ).point(group, seed, 1).program
    InstanceTableSetup(
      Values.ofInstruction(
        Defunctionalization.thunkInstruction[C](
          products.deBruijnTerm(Map.empty)
        ),
        Set.empty
      ),
      Values.ofInstruction(
        Defunctionalization.thunkInstruction[C](
          subsequence.deBruijnTerm(Map.empty)
        ),
        Set.empty
      ),
      configured(encoding, instanceTable = true),
      configured(encoding, instanceTable = false)
    )

  private def configured[C <: NativeSpecializer & Singleton](
      encoding: StorageEncoding & C,
      instanceTable: Boolean
  ): Jit[C] =
    Jit(
      JitConfiguration[C](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.Dispatch(DispatchStrategies.fallback),
        instanceTable = instanceTable,
        storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )
  val repetitions: Int = 64

  /** The length of each string of the longest common subsequence's site: small,
    * so that the reading of main at 5f4ec2a23, which runs an instance whose
    * fillings exceed 64 nodes untabled and so grows exponentially in the
    * length, can be measured beside the reading that tables it.
    */
  val subsequenceLength: Int = 8

  /** The steps a reading may take: the program reads in about a million. */
  val limit: Long = 20000000

/** The JIT's normal-form reading of each program from a fresh state,
  * compilation included, as a point is read, with the instance table on and off
  * (`JitConfiguration.instanceTable`): its purpose is to time the table's own
  * work per instance (the key's hash and comparison, the table's updates),
  * beyond the lookup's charge in steps, on small fillings (products) and on
  * large ones (the subsequence).
  */
@BenchmarkMode(
  Array(Mode.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(
  value = 3,
  jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 3, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 2, timeUnit = TimeUnit.SECONDS)
class InstanceTableBenchmarks:

  /** The normal forms read with the table on. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def productsTabled(input: InstanceTableInputs): Vector[Configured[?]] =
    InstanceTableBenchmarks.productsTabled(input.setup)

  /** The normal forms read with the table off. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def productsUntabled(input: InstanceTableInputs): Vector[Configured[?]] =
    InstanceTableBenchmarks.productsUntabled(input.setup)

  /** The subsequence's normal forms read with the table on. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def subsequenceTabled(input: InstanceTableInputs): Vector[Configured[?]] =
    InstanceTableBenchmarks.subsequenceTabled(input.setup)

object InstanceTableBenchmarks:

  /** The setup's products read with the table on, in the setup's configuration,
    * which the method binds.
    */
  def productsTabled[C <: NativeSpecializer & Singleton](
      setup: InstanceTableSetup[C]
  ): Vector[Configured[C]] =
    read(setup.tabled, setup.program)(using setup.specializer)

  /** The setup's products read with the table off. */
  def productsUntabled[C <: NativeSpecializer & Singleton](
      setup: InstanceTableSetup[C]
  ): Vector[Configured[C]] =
    read(setup.untabled, setup.program)(using setup.specializer)

  /** The setup's subsequence read with the table on. */
  def subsequenceTabled[C <: NativeSpecializer & Singleton](
      setup: InstanceTableSetup[C]
  ): Vector[Configured[C]] =
    read(setup.tabled, setup.subsequences)(using setup.specializer)

  /** The normal forms of the program; throws `IllegalStateException` when the
    * reading stops, since a benchmark of a stopped reading times nothing the
    * points need.
    */
  def read[C <: NativeSpecializer & Singleton](jit: Jit[C], program: Value[C])(
      using C
  ): Vector[Configured[C]] =
    NormalForms
      .normalForms(com.yang_bo.gezi.weakhead.Mode.Jit(jit), program)
      .result(
        ReadingState.fresh(InstanceTableInputs.limit, jit.readingConfiguration)
      ) match
      case Computed.Done(normalForms, _) => normalForms
      case Computed.Stopped(after)       =>
        throw IllegalStateException(
          s"the reading stopped after ${after.budget.spent} steps"
        )
