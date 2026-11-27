package gezi.jmh.pipeline

import gezi.ir.{Configured, NativeSpecializer}
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.entry.BackendOption
import gezi.contest.entry.CheckpointOption
import gezi.contest.entry.LookaheadOption
import gezi.contest.entry.InstanceReuseOption
import gezi.contest.entry.GroupBlocksOption
import gezi.contest.entry.Defaults
import gezi.contest.entry.DispatchOption
import gezi.contest.entry.GranularityOption
import gezi.contest.entry.InstanceRetentionOption
import gezi.contest.entry.JitOptions
import gezi.contest.entry.NativeBlocksOption
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.JitConfiguration
import gezi.jit.StorageEncoding
import gezi.jit.TableCost
import gezi.programfamilies.FixedPointLines
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Budget
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.JitEvaluator
import gezi.weakhead.Mode as ReadingMode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup

/** The input of the trampoline's stop check benchmark: the evaluator of the
  * benchmarks' generated knowledge for an executor
  * (`KnowledgeReadings.executorKnowledgeTerm`) and one hot site
  * in the hot ladder's iterated shape, its library terms the members of the
  * cancel law's fixture read by projection, let bound as the hot ladder's
  * generator binds them, a count of `TrampolineStopInput.bits` binary digits
  * and a function adding three; read by the general reading (the JIT,
  * `Defaults.jit` of `TrampolineStopInput.jitOptions`), as written, with no
  * lemma round. The fields are
  * lazy vals, so no line here is exempt: each is built once per fork, in the
  * first invocation that reads it, which falls in the first warm-up
  * iteration; the five warm-up iterations absorb it.
  */
@State(Scope.Benchmark)
class TrampolineStopInput:

  /** The evaluator and the program, in the configuration of the encoding of the executor knowledge's facts, which the
    * setup's type parameter names for the benchmarks that open it.
    */
  lazy val setup: TrampolineStopSetup[?] =
    val library = KnowledgeReadings.compiled(KnowledgeReadings.executorKnowledgeTerm, Vector(BackendChecks))
    val encoding = BackendFacts.of(library).storageEncoding
    TrampolineStopInput.setupOf[encoding.type](encoding)

/** The JIT and the program it reads, in the configuration `C`. */
final case class TrampolineStopSetup[C <: NativeSpecializer & Singleton](evaluator: JitEvaluator[C], program: Configured[C]):

  /** The specializer of the configuration, the one the JIT is built over. */
  def specializer: C = evaluator.readingConfiguration.specializer

object TrampolineStopInput:

  /** The JIT of `jitOptions` over the encoding, and the site read by it, the library terms of the cancel law's
    * fixture crossed from no facts into the encoding's configuration.
    */
  def setupOf[C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C): TrampolineStopSetup[C] =
    given C = encoding
    val root = FixedPointLines.buildRoot
    val members = StandardLibrary
      .entryMembers(root, gezi.standardlibrary.TermTables.hotSiteTerms, Expansions.none)
      ._1
    val crossed = encoding.crossedAllFromNoFacts(members.values)
    val terms = members.map((key, instruction) => key -> Term.closed(crossed(instruction)))
    TrampolineStopSetup(
      Defaults.jit[C](encoding, jitOptions, GroupBlocksOption.None, gezi.ir.StorageAccess.granted()),
      Defunctionalization.thunkInstruction[C](site(keys.map(terms)).deBruijnTerm(Map.empty))
    )

  /** The JIT's options the benchmark reads with, named here rather than taken
    * from an entry: one predicate per code, the closure backend, the
    * dispatch strategy `fallback`, no instance table, the JIT's default
    * compilation budget, the profitable checkpoints and no native blocks.
    */
  val jitOptions: JitOptions =
    JitOptions(
      DispatchOption.Fallback,
      BackendOption.Closure,
      GranularityOption.PredicatePerCode,
      instanceTable = false,
      instanceTableTrial = TableCost.trial,
      instanceRetention = InstanceRetentionOption.Generations(JitConfiguration.defaultInstanceTableGeneration),
      budget = JitConfiguration.defaultBudget,
      checkpoints = CheckpointOption.Profitable,
      nativeBlocks = NativeBlocksOption.None,
      lookahead = LookaheadOption.Lazily,
      instanceReuse = InstanceReuseOption.WithinVersion
    )

  /** The names of the cancel law's library terms the site uses
    * (`TermTables.hotSiteTerms`), in the order `site` binds them.
    */
  val keys: Vector[String] = Vector("binary_zero", "binary_even", "binary_odd", "merge_binary_plus", "fixpoint")

  /** The binary digits of the site's count, all ones. The benchmarks'
    * knowledge binds no binary native, so the general reading reads
    * `merge_binary_plus` from its body and its steps grow far faster than
    * the count. MEASURED 2026-11-13 (CPUs 4,5, a limit of 2e7 steps): 1 to 4
    * digits read in 196, 567, 3,790 and 753,281 steps, the last in about
    * 0.3 s; 5 digits did not finish within the limit. Four digits make a
    * reading that is weak-head work throughout, which is what the stop check
    * is to be priced on.
    */
  val bits: Int = 4

  /** The site: `iterate count (λx. plus x three) one`, the library terms
    * given (`keys`' order) let bound, `iterate` the fixed point of the hot
    * ladder's iterated shape.
    */
  def site(library: Vector[Term]): Term =
    val Vector(zero, even, odd, plus, fixpoint) = library: @unchecked
    val iterate = fixpoint(λ(self => λ(n => λ(g => λ(s =>
      n(s)(λ(m => self(m)(g)(self(m)(g)(s))))(λ(m => g(self(m)(g)(self(m)(g)(s)))))
    )))))
    λ(boundZero => λ(boundEven => λ(boundOdd => λ(boundPlus => λ(boundIterate =>
      def numeral(value: BigInt): Term =
        if value == 0 then boundZero
        else if value.testBit(0) then boundOdd(numeral(value >> 1))
        else boundEven(numeral(value >> 1))
      boundIterate(numeral((BigInt(1) << bits) - 1))(λ(x => boundPlus(x)(numeral(BigInt(3)))))(numeral(BigInt(1)))
    )(iterate))(plus))(odd))(even))(zero)

/** The cost of the trampoline's read of the stop signal
  * (`Trampoline.resultUnless`) on the general reading's hot path: the same
  * reading run by the plain trampoline (`Computation.result`) and by the
  * trampoline that reads a signal every `Trampoline.stopCheckBounces`
  * bounces, the signal reading the clock against a deadline far away (the
  * judge's runner's signal reads a future's value instead,
  * `EntryRunner.CancelRead`). Each returns the reading's result, so
  * that JMH consumes it. Average time of a reading; three forks with the
  * serial collector and a 1 GB heap; five warm-up and five measurement
  * iterations of 1 s.
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 3, jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class TrampolineStopBenchmark:

  /** The reading on the plain trampoline. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def plain(input: TrampolineStopInput): Computed[?, Vector[Configured[?]]] = TrampolineStopBenchmark.plain(input.setup)

  /** The reading on the trampoline that reads the signal. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def stopChecked(input: TrampolineStopInput): Option[Computed[?, Vector[Configured[?]]]] = TrampolineStopBenchmark.stopChecked(input.setup)

object TrampolineStopBenchmark:

  /** A signal that reads the clock against a deadline an hour away, and the
    * reading's start under it: the budget reads the same signal in both
    * benchmarks, so that they differ in the trampoline's reads alone.
    */
  def started[C <: NativeSpecializer & Singleton](configuration: gezi.weakhead.ReadingConfiguration[C]): (StopSignal, ReadingState[C]) =
    val deadline = System.nanoTime + 3_600_000_000_000L
    val stop = new StopSignal:
      def stopRequested: Boolean = System.nanoTime > deadline
    (stop, ReadingState.knowingTop(0, configuration).copy(budget = Budget.stoppedBy(Long.MaxValue, stop)))

  /** The reading of the setup's program on the plain trampoline, in the setup's configuration, which the method binds. */
  def plain[C <: NativeSpecializer & Singleton](setup: TrampolineStopSetup[C]): Computed[ReadingState[C], Vector[Configured[C]]] =
    given C = setup.specializer
    val (_, state) = started(setup.evaluator.readingConfiguration)
    NormalForms.normalForms(ReadingMode.Jit(setup.evaluator), setup.program).result(state)

  /** The reading of the setup's program on the trampoline that reads the signal. */
  def stopChecked[C <: NativeSpecializer & Singleton](setup: TrampolineStopSetup[C]): Option[Computed[ReadingState[C], Vector[Configured[C]]]] =
    given C = setup.specializer
    val (stop, state) = started(setup.evaluator.readingConfiguration)
    NormalForms.normalForms(ReadingMode.Jit(setup.evaluator), setup.program).resultUnless(state, stop)
