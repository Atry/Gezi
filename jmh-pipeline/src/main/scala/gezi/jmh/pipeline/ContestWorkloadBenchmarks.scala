package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.corpora.reductions.ContestWorkloadSolutions
import gezi.contest.corpora.reductions.Draws
import gezi.contest.corpora.reductions.LibraryBillboards
import gezi.contest.corpora.reductions.LibraryEditDistances
import gezi.contest.corpora.reductions.LibraryHotspots
import gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import gezi.contest.corpora.reductions.LibrarySmallestTeams
import gezi.contest.corpora.reductions.NativeProblem
import gezi.contest.corpora.reductions.NativeValue
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.claims.Spelling
import gezi.programfamilies.FixedPointLines
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

/** The sites of one point of each workload family at its nominal ranges and its
  * largest R (4 sites of strings, 1 of rods), drawn from the seed 20261031;
  * built once, outside the timed calls. The fields are lazy vals, so no line
  * here is exempt.
  */
@State(Scope.Benchmark)
class ContestWorkloadInputs:

  /** The strings of the longest common subsequences' point. */
  lazy val strings: Vector[(IArray[Int], IArray[Int])] =
    LibraryLongestCommonSubsequences
      .drawn(
        LibraryLongestCommonSubsequences.nominal,
        Draws.fromSeed(ContestWorkloadInputs.seed),
        ContestWorkloadInputs.repetitions
      )
      .sites
      .map(site => (IArray.from(site.first), IArray.from(site.second)))

  /** The rods and the target of the billboards' point, at its one site. */
  lazy val billboardSites: Vector[(IArray[Int], Int)] =
    LibraryBillboards
      .drawn(
        LibraryBillboards.nominal,
        Draws.fromSeed(ContestWorkloadInputs.seed),
        LibraryBillboards.nominal.repetitions.end
      )
      .sites
      .map(site => (IArray.from(site.rods), site.target))

  /** The reduction group read from Gezi's directory, which the natively solved
    * families' draws take.
    */
  lazy val group: ReductionGroup = ReductionGroup(
    FixedPointLines.buildRoot,
    Expansions.none,
    gezi.contest.entry.Defaults.caches()
  )

  /** The edit distances' point of each spelling at its top rung, drawn as the
    * generator draws it, from the seed mixed with the variant's stem
    * (`NativeProblem.topRung`).
    */
  lazy val editDistancesDirect: NativeProblem[LibraryEditDistances.Drawn] =
    NativeProblem.topRung(
      LibraryEditDistances(
        Spelling.Direct,
        LibraryEditDistances.nominal,
        LibraryEditDistances.name
      ),
      group,
      ContestWorkloadInputs.seed
    )

  /** As `editDistancesDirect`, respelled. */
  lazy val editDistancesRespelled: NativeProblem[LibraryEditDistances.Drawn] =
    NativeProblem.topRung(
      LibraryEditDistances(
        Spelling.Respelled,
        LibraryEditDistances.nominal,
        LibraryEditDistances.name
      ),
      group,
      ContestWorkloadInputs.seed
    )

  /** The smallest teams' point of each spelling at its top rung, drawn as the
    * generator draws it.
    */
  lazy val smallestTeamsDirect: NativeProblem[LibrarySmallestTeams.Drawn] =
    NativeProblem.topRung(
      LibrarySmallestTeams(
        Spelling.Direct,
        LibrarySmallestTeams.nominal,
        LibrarySmallestTeams.name
      ),
      group,
      ContestWorkloadInputs.seed
    )

  /** As `smallestTeamsDirect`, respelled. */
  lazy val smallestTeamsRespelled: NativeProblem[LibrarySmallestTeams.Drawn] =
    NativeProblem.topRung(
      LibrarySmallestTeams(
        Spelling.Respelled,
        LibrarySmallestTeams.nominal,
        LibrarySmallestTeams.name
      ),
      group,
      ContestWorkloadInputs.seed
    )

  /** The hotspots' point of each spelling at the top rung of C (10^5) and its
    * largest R, drawn as the generator draws it.
    */
  lazy val hotspotsDirect: NativeProblem[LibraryHotspots.Drawn] =
    NativeProblem.topRung(
      LibraryHotspots.rung(Spelling.Direct, LibraryHotspots.rungCalls.last),
      group,
      ContestWorkloadInputs.seed
    )

  /** As `hotspotsDirect`, respelled. */
  lazy val hotspotsRespelled: NativeProblem[LibraryHotspots.Drawn] =
    NativeProblem.topRung(
      LibraryHotspots.rung(Spelling.Respelled, LibraryHotspots.rungCalls.last),
      group,
      ContestWorkloadInputs.seed
    )

/** The seed and the repetitions of the benchmarks' points. */
object ContestWorkloadInputs:
  val seed: Long = 20261031L
  val repetitions: Int =
    LibraryLongestCommonSubsequences.nominal.repetitions.end

/** The hand-written native Scala solutions of the workload families
  * (`gezi.contest.corpora.reductions.ContestWorkloadSolutions`), timed on one
  * point of each at its nominal ranges and largest R: the families' reference
  * times. Each benchmark returns the point's answers, so that JMH consumes
  * them. An operation takes a tenth of a second or more, so the warm-up and the
  * measurement iterations are longer than `PipelineBenchmarks`'.
  *
  * The readings of 2026-11-01 (`jmh-pipeline/Jmh/run ContestWorkloadBenchmarks`
  * under `nice -n 19 taskset -c 6,7`, JMH 1.37, JDK 25.0.4.1; average time, 3
  * forks, 3 warm-up iterations of 3 s and 5 measurement iterations of 2 s
  * each), at the nominal ranges of the commit that records them: 05:35 to 05:37
  * UTC, the machine's load average rising from 6.5 to 16.3,
  * `longestCommonSubsequences` 570.2 ± 229.7 ms/op (4 sites of 3000 characters)
  * and `billboards` 521.0 ± 255.0 ms/op (1 site of 20 rods of 1 to 1000). At
  * 05:32 to 05:34 UTC, load 8.4 to 9.4, with the billboards' earlier rods of 1
  * to 500: 229.4 ± 69.7 and 49.4 ± 27.1 ms/op. The readings are noisy under the
  * shared machine's load. The warm-up's readings fall by the second iteration
  * (from 1857 to 1072 ms, from 401 to 148 ms) and then stay within the
  * measurement's spread, so three iterations cover it.
  *
  * The edit distances and the smallest teams, under `nice -n 19 taskset -c
  * 0-5`, the same JMH and JDK and protocol, on the points the generator draws:
  * 2026-11-01 06:56 to 07:01 UTC, load average 7.7 to 12.8,
  * `editDistancesDirect` 230.3 ± 23.1 and `editDistancesRespelled` 204.3 ± 8.2
  * ms/op (4 sites of two strings of 3000 characters); 07:01 to 07:03 UTC, load
  * 10.7 to 10.8, `smallestTeamsDirect` 225.6 ± 16.5 and
  * `smallestTeamsRespelled` 238.5 ± 18.2 ms/op (6 sites of 60 people and 19
  * skills). Their warm-up readings fall by the third iteration (from 290 to 269
  * ms, from 408 to 222 ms) to within the measurement's spread.
  */
@BenchmarkMode(
  Array(Mode.AverageTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(
  value = 3,
  jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 3, time = 3, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 2, timeUnit = TimeUnit.SECONDS)
class ContestWorkloadBenchmarks:

  /** The lengths of the longest common subsequences of the point's sites. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def longestCommonSubsequences(input: ContestWorkloadInputs): Vector[Int] =
    input.strings.map((first, second) =>
      ContestWorkloadSolutions.longestCommonSubsequence(first, second)
    )

  /** Whether the rods of each of the point's billboards reach its target. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def billboards(input: ContestWorkloadInputs): Vector[Boolean] =
    input.billboardSites.map((rods, target) =>
      ContestWorkloadSolutions.billboardReaches(rods, target)
    )

  /** The edit distances of the direct spelling's point, by the family's native
    * solver (`LibraryEditDistances.solved`).
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def editDistancesDirect(input: ContestWorkloadInputs): Vector[NativeValue] =
    input.editDistancesDirect.solved

  /** As `editDistancesDirect`, on the respelled variant's point. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def editDistancesRespelled(
      input: ContestWorkloadInputs
  ): Vector[NativeValue] = input.editDistancesRespelled.solved

  /** The sizes of the smallest teams of the direct spelling's point, by the
    * family's native solver (`LibrarySmallestTeams.solved`).
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def smallestTeamsDirect(input: ContestWorkloadInputs): Vector[NativeValue] =
    input.smallestTeamsDirect.solved

  /** As `smallestTeamsDirect`, on the respelled variant's point. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def smallestTeamsRespelled(
      input: ContestWorkloadInputs
  ): Vector[NativeValue] = input.smallestTeamsRespelled.solved

  /** The last states of the hotspots' point at the top rung of C, direct, by
    * the family's native solver (`LibraryHotspots.solved`). Not yet measured
    * under JMH.
    */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def hotspotsDirect(input: ContestWorkloadInputs): Vector[NativeValue] =
    input.hotspotsDirect.solved

  /** As `hotspotsDirect`, on the respelled variant's point. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def hotspotsRespelled(input: ContestWorkloadInputs): Vector[NativeValue] =
    input.hotspotsRespelled.solved
