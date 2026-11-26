package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.corpora.claims.Spelling
import gezi.contest.corpora.reductions.LibraryHotspots
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.frontend.Defunctionalization
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.ClosureBackend
import gezi.jit.DispatchMode
import gezi.jit.EveryStepsCheckpoints
import gezi.jit.InstanceCheckpoints
import gezi.jit.Jit
import gezi.jit.StorageEncoding
import gezi.jit.InstanceRetention
import gezi.jit.JitConfiguration
import gezi.jit.PredicatePerCode
import gezi.jit.ProfitableCheckpoints
import gezi.programfamilies.FixedPointLines
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.NormalForms
import gezi.weakhead.Reading
import gezi.weakhead.ReadingState
import gezi.ir.Value
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
import gezi.ir.{Configured, NativeSpecializer}

/** The point of the hot variant of the rung of 10,000 calls, direct, at
  * R = 1, drawn from the seed 20261031 (the family `calls_10000_hot` of the
  * contest), and three JITs as `contest-entries-solo` configures its direct reading,
  * with the instance table on under the default checkpoint policy and under
  * `EveryStepsCheckpoints` at two intervals; built once,
  * outside the timed calls. The fields are lazy vals, so no line here is
  * exempt.
  */
@State(Scope.Benchmark)
class InstanceCheckpointInputs:

  /** The point and the three JITs, in the configuration of the encoding of the knowledge file's facts, which the
    * setup's type parameter names for the benchmarks that open it.
    */
  lazy val setup: InstanceCheckpointSetup[?] =
    val library = KnowledgeReadings.compiled(InstanceCheckpointInputs.knowledgeFile, Vector(BackendChecks))
    val encoding = BackendFacts.of(library).storageEncoding
    InstanceCheckpointInputs.setupOf[encoding.type](encoding)

/** The point read in the configuration `C` and the three JITs that read it: under the default checkpoint policy and
  * under `EveryStepsCheckpoints` at two intervals.
  */
final case class InstanceCheckpointSetup[C <: NativeSpecializer & Singleton](
    program: Value[C],
    default: Jit[C],
    shortInterval: Jit[C],
    longInterval: Jit[C]
):

  /** The specializer of the configuration, the one the three JITs are built over. */
  def specializer: C = default.configuration.specializer

object InstanceCheckpointInputs:
  val calls: Int = 10000

  /** The point and the three JITs over the encoding. */
  def setupOf[C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C): InstanceCheckpointSetup[C] =
    given C = encoding
    val group = ReductionGroup(FixedPointLines.buildRoot, Expansions.none, gezi.contest.entry.Defaults.caches())
    val term = LibraryHotspots
      .calibrated(Spelling.Direct, calls, LibraryHotspots.Calibration.Hot)
      .point(group, InstanceTableInputs.seed, 1)
      .program
    val program = Values.ofInstruction(Defunctionalization.thunkInstruction[C](term.deBruijnTerm(Map.empty)), Set.empty)
    InstanceCheckpointSetup(
      program,
      configured(encoding, ProfitableCheckpoints),
      configured(encoding, EveryStepsCheckpoints(shortInterval)),
      configured(encoding, EveryStepsCheckpoints(longInterval))
    )

  private def configured[C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C, checkpoints: InstanceCheckpoints): Jit[C] =
    Jit(
      JitConfiguration[C](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.NoDispatch,
        instanceTable = true,
        instanceTableTrial = instanceTableTrial,
        instanceRetention = InstanceRetention.Generations(instanceTableGeneration),
        instanceCheckpoints = checkpoints,
        storageAccess = gezi.ir.StorageAccess.granted()
      )
    )

  /** The knowledge (the fixture whose one field is the choice of six
    * knowledge files: native_types, native_arithmetic, hindley_milner_unions,
    * prolog_backend, native_arithmetic_prolog_backend and
    * prolog_backend_shapes, relative to the build root), the instance
    * table's trial and its young generation of the entry `SoloEntry` at main
    * c983e0af7, whose direct reading
    * (`DispatchMode.NoDispatch`) answered this family in its practice passes
    * (`SoloEntry.instanceTableGeneration`): the point is read here as an
    * entry reads it. Under `InstanceTableInputs`' knowledge and the
    * framework's trial and generation, the default policy stopped at `limit`
    * too (measured 2026-11-03, `instanceCheckpointCounts`, with the same
    * modules written as a text the host assembled; read from the file since
    * the library became files reached by paths, so the readings before that
    * commit are not comparable without a rerun).
    */
  val knowledgeFile: String = "tests/benchmark_fixtures/instance_checkpoint_modules.lambdalattice"
  val instanceTableTrial: Long = 1024
  val instanceTableGeneration: Int = 1 << 19

  /** The steps a reading may take: the family's budget of 60 seconds in
    * steps (`Reading.budgetSteps`), as the judge reads the point, 120,000,000
    * steps.
    * MEASURED 2026-11-03 06:02 UTC (`instanceCheckpointCounts`, CPUs 0 to 3,
    * -Xmx2g): the default policy reads the point in 59,846,144 steps, so
    * `InstanceTableInputs`' 20,000,000 stop it; `EveryStepsCheckpoints(1000)`
    * and `EveryStepsCheckpoints(100000)` stop at this limit.
    */
  val limit: Long = Reading.budgetSteps(60)

  /** The hot point read under `jit` from a fresh state within `limit`
    * steps: its normal forms when the reading finishes, the steps it spent
    * when it stops. A stopped reading is a result of the policy, not a
    * failure of the benchmark, so it is returned and not thrown.
    */
  def read[C <: NativeSpecializer & Singleton](jit: Jit[C], program: Value[C])(using C): Either[Long, Vector[Configured[C]]] =
    NormalForms.normalForms(gezi.weakhead.Mode.Jit(jit), program).result(ReadingState.fresh(limit, jit.readingConfiguration)) match
      case Computed.Done(normalForms, _) => Right(normalForms)
      case Computed.Stopped(after)       => Left(after.budget.spent)

  /** The two intervals of steps between checkpoints: about one call's
    * steps, and about a hundred calls'. A choice, not a measurement.
    */
  val shortInterval: Long = 1000
  val longInterval: Long = 100000

/** The JIT's normal-form reading of the hot point from a fresh state,
  * compilation included, as a point is read, under the default checkpoint
  * policy: its purpose is the time against which a checkpoint policy is
  * judged on the hot loop, whose table held about 1.1 GB live under the
  * default, as measured. A policy whose
  * reading stops at `InstanceCheckpointInputs.limit` is reported by
  * `instanceCheckpointCounts` as a stop with its steps, not timed here; the
  * two `EveryStepsCheckpoints` policies stop (measured 2026-11-03). A
  * reading takes seconds, so each is timed once per iteration
  * (`Mode.SingleShotTime`); one warm-up iteration loads and compiles the
  * classes the reading uses.
  *
  * The reading of 2026-11-03 06:02 to 06:09 UTC (`jmh-pipeline/Jmh/run
  * .*InstanceCheckpointBenchmarks.*` under `taskset -c 0-3 nice -n 19`, JMH
  * 1.37, JDK 25.0.4.1, commit of this comment's parent ef3e99744 plus the
  * configuration above; single shot, 2 forks, 1 warm-up and 3 measurement
  * iterations, -Xmx2g, serial collector; load average 6.5 falling to 2.9):
  * `hotDefault` 43479.4 ± 5111.0 ms/op. The warm-up readings were 49870 and
  * 42959 ms, the second already within the measurements' 41710 to 45705
  * ms, so one warm-up iteration covers it.
  */
@BenchmarkMode(Array(Mode.SingleShotTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(value = 2, jvmArgsAppend = Array("-Xmx2g", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 1)
@Measurement(iterations = 3)
class InstanceCheckpointBenchmarks:

  /** The hot point read under the default policy. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def hotDefault(input: InstanceCheckpointInputs): Either[Long, Vector[Configured[?]]] = InstanceCheckpointBenchmarks.hotDefaultOf(input.setup)

object InstanceCheckpointBenchmarks:

  /** The hot point read under the default policy of the setup, whose configuration the method binds. */
  def hotDefaultOf[C <: NativeSpecializer & Singleton](setup: InstanceCheckpointSetup[C]): Either[Long, Vector[Configured[C]]] =
    InstanceCheckpointInputs.read(setup.default, setup.program)(using setup.specializer)
