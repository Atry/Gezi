package gezi.jmh.pipeline

import java.math.BigInteger
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.entry.Defaults
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.EntryData
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.jit.NativesProvider
import gezi.narrowblocks.LemmaRoute
import gezi.narrowblocks.DebugAttributes
import gezi.narrowblocks.NarrowBlockCompilation
import gezi.narrowblocks.NarrowBlockProgram
import gezi.programfamilies.FixedPointLines
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import scala.concurrent.Future
import scala.concurrent.Promise

/** The input of the narrow block stop check benchmark: the compiled narrow
  * blocks of one hot site, `iterate count (λx. plus x three) one` in the hot
  * ladder's iterated shape, with a count of `BlockStopInput.bits` binary
  * digits and the eight library terms of CancelGraceLawTest's fixture let
  * bound as its generator binds them, routed as the in-tree entry `contest-entries-solo` routes
  * a point: its lemma rounds saturated (`LemmaRoute.saturatedRounds`), the
  * last round's extraction, its narrow blocks compiled
  * (`NarrowBlockCompilation`). All eight are bound though the site uses five:
  * with only the five bound, that entry's rounds add no instance and the
  * site compiles to no block, while the same site with the eight bound
  * compiles to one (a probe at 8 binary digits through both the entry and
  * this route, 2026-11-14). The field is a lazy val, so no line here is
  * exempt: it is built once per fork, in the first invocation that reads
  * it, which falls in the first warm-up iteration; the warm-up iterations
  * absorb it.
  */
@State(Scope.Benchmark)
class BlockStopInput:

  lazy val programs: Vector[NarrowBlockProgram] = BlockStopInput.compiled()

object BlockStopInput:

  /** The binary digits of the site's count, all ones: the block's recursion
    * makes about 2^bits calls.
    */
  val bits: Int = 20

  /** The fixture's keys, in the order CancelGraceLawTest's generator binds
    * them.
    */
  private val keys: Vector[String] = Vector(
    "binary_zero", "binary_even", "binary_odd", "merge_binary_plus", "binary_maximum", "binary_minimum", "binary_bitwise_or", "fixpoint"
  )

  /** The compiled narrow blocks of the site under `contest-entries-solo`. Throws
    * `IllegalStateException` when the site compiles to no block.
    */
  def compiled(): Vector[NarrowBlockProgram] =
    val root = FixedPointLines.buildRoot
    val (data, afterEntry) = EntryData.read(root.resolve("contest-entries-solo"), Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(data, gezi.contest.entry.ExecutorModules.registeredFor(root.resolve("contest-entries-solo")), gezi.contest.entry.ExtractorModules.registeredFor(root.resolve("contest-entries-solo")), NativesProvider.loaded, ArticleDestination.Discarded, afterEntry, gezi.contest.entry.Defaults.caches())
    val terms = StandardLibrary
      .entryMembers(root, gezi.standardlibrary.TermTables.hotSiteTerms, Expansions.none)
      ._1
      .map((key, instruction) => key -> Term.closed(instruction))
    val program = Defunctionalization.thunkInstruction(site(keys.map(terms)).locallyNamelessTerm)(using gezi.ir.NoFacts)
    val (run, _, _) = LemmaRoute.saturatedRounds(entry.rounds, program, explained = false, StopSignal.NeverStopped)
    val blockCompilation = NarrowBlockCompilation(entry.index, entry.natives, gezi.narrowblocks.LemmaRoute.readingConfiguration(run))
    val blocks = blockCompilation.blocks(entry.rounds.last.extracted(program, run, StopSignal.NeverStopped))
    if blocks.isEmpty then throw IllegalStateException("the site compiles to no narrow block")
    blockCompilation.compiled(blocks, DebugAttributes.Omitted, StopSignal.NeverStopped) match
      case Right(programs) => programs
      case Left(reason)    => throw IllegalStateException(s"the site's blocks do not compile: $reason")

  /** The site over the library terms given in `keys`' order: the first
    * seven and the iterated shape's fixed point let bound, `(λx0. … (λx7.
    * body) v7 …) v0`, as CancelGraceLawTest's generator binds them; a count
    * of `bits` binary digits, all ones, and a function adding three.
    */
  private def site(library: Vector[Term]): Term =
    val fixpoint = library.last
    val iterate = fixpoint(λ(self => λ(n => λ(g => λ(s =>
      n(s)(λ(m => self(m)(g)(self(m)(g)(s))))(λ(m => g(self(m)(g)(self(m)(g)(s)))))
    )))))
    lets(library.dropRight(1) :+ iterate, Vector.empty, bound =>
      val Vector(boundZero, boundEven, boundOdd, boundPlus, _, _, _, boundIterate) = bound: @unchecked
      def numeral(value: BigInt): Term =
        if value == 0 then boundZero
        else if value.testBit(0) then boundOdd(numeral(value >> 1))
        else boundEven(numeral(value >> 1))
      boundIterate(numeral((BigInt(1) << bits) - 1))(λ(x => boundPlus(x)(numeral(BigInt(3)))))(numeral(BigInt(1)))
    )

  /** The values let bound in order, `(\x0. … (\xn. body) vn …) v0`, and
    * the body given the bound variables.
    */
  private def lets(values: Vector[Term], bound: Vector[Term], body: Vector[Term] => Term): Term =
    if bound.size == values.size then body(bound)
    else λ(variable => lets(values, bound :+ variable, body))(values(bound.size))

  /** A signal read as the judge's runner reads its cancel
    * (`EntryRunner.CancelRead`, private there): a stop once a future that
    * never completes here holds the cancel line.
    */
  final case class CancelLike(following: Future[Option[String]]) extends StopSignal:
    def stopRequested: Boolean = following.value.exists(_.toOption.flatten.contains("cancel"))

/** The cost of a compiled narrow block's read of the stop signal, once per
  * recursive call (`NarrowBlockProgram.run`): the site's blocks run under
  * the signal that never stops, and under a signal read as the judge's
  * cancel is, a future's value, whose future never completes. The same
  * benchmark on a build whose blocks read no signal (`run()`) is the
  * comparison. Each returns the blocks' values, so that JMH consumes them.
  * Average time; three forks with the serial collector and a 1 GB heap;
  * five warm-up and five measurement iterations of 1 s. The first warm-up
  * iteration of each fork holds the input's lazy build (about 9 s); the
  * second to fifth already read 14 to 15 ms, so five suffice.
  *
  * Reading (2026-11-14, contest-lean.slice, CPUs 10,11, `sbt --client
  * 'jmh-pipeline/Jmh/run -rf json -rff <file> -o <file>
  * .*BlockStopBenchmark.*'`): on block-stop 5644333e4, 06:39 to 06:42 UTC,
  * one-minute load 7.1 to 9.0, `neverStopped` 14.172 ± 0.397 ms/op and
  * `cancelLike` 14.781 ± 0.306 ms/op; on main 94c7e3604 with this benchmark
  * copied in and calling `run()` (a scratch build, not committed), 06:42 to
  * 06:47 UTC, load 8.8 to 6.3, `neverStopped` 14.553 ± 0.935 ms/op. The
  * poll's cost is within the error: no difference measured.
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 3, jvmArgsAppend = Array("-Xmx1g", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class BlockStopBenchmark:

  /** The blocks run under the signal that never stops. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def neverStopped(input: BlockStopInput): Vector[Option[BigInteger]] =
    input.programs.map(_.run(StopSignal.NeverStopped))

  /** The blocks run under a signal read as the judge's cancel is. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def cancelLike(input: BlockStopInput): Vector[Option[BigInteger]] =
    val stop = BlockStopInput.CancelLike(Promise[Option[String]]().future)
    input.programs.map(_.run(stop))
