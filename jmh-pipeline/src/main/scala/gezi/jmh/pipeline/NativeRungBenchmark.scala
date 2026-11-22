package gezi.jmh.pipeline

import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"): the time unit of JMH's annotations, an immutable enum of the concurrency package
import gezi.contest.corpora.reductions.ContestWorkloadSolutions
import gezi.contest.corpora.reductions.Draws
import gezi.contest.corpora.reductions.LibraryBillboards
import gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import gezi.contest.corpora.reductions.NativeProblem
import gezi.contest.corpora.reductions.NativelySolved
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.RepeatedVariants
import gezi.programfamilies.FixedPointLines
import gezi.weakhead.Expansions
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Level
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Param
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.Setup
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup
import scala.compiletime.uninitialized

/** The input of the per-rung benchmark: a point of a workload family, named
  * `stem:repetitions`, drawn at the seed with that many sites, before the
  * trial, as the generator draws it (`NativelySolved.drawnAt`). The seed is
  * the public seed 20261031 unless `-p seed=N` names another, such as a
  * round's points seed, so that a native time is read on the very draw the
  * round's point holds (the judge hands `--seed-file`'s seed to the
  * generator unchanged, `CorpusSources.seededSources`).
  */
@State(Scope.Benchmark)
class NativeRungInput:

  /** The point, which JMH assigns: the variant's stem and a count of sites R
    * from 1 to the family's top R, for the direct and the respelled variant
    * of edit distances, longest common subsequences, billboards and smallest
    * teams, and of their low rungs (`small` in the family's name).
    */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("repeated_library_edit_distances/direct:1", "repeated_library_edit_distances/direct:2", "repeated_library_edit_distances/direct:3", "repeated_library_edit_distances/direct:4", "repeated_library_edit_distances/respelled:1", "repeated_library_edit_distances/respelled:2", "repeated_library_edit_distances/respelled:3", "repeated_library_edit_distances/respelled:4", "repeated_library_edit_distances_small/direct:1", "repeated_library_edit_distances_small/direct:2", "repeated_library_edit_distances_small/direct:3", "repeated_library_edit_distances_small/direct:4", "repeated_library_edit_distances_small/respelled:1", "repeated_library_edit_distances_small/respelled:2", "repeated_library_edit_distances_small/respelled:3", "repeated_library_edit_distances_small/respelled:4", "repeated_library_longest_common_subsequences/direct:1", "repeated_library_longest_common_subsequences/direct:2", "repeated_library_longest_common_subsequences/direct:3", "repeated_library_longest_common_subsequences/direct:4", "repeated_library_longest_common_subsequences/respelled:1", "repeated_library_longest_common_subsequences/respelled:2", "repeated_library_longest_common_subsequences/respelled:3", "repeated_library_longest_common_subsequences/respelled:4", "repeated_library_longest_common_subsequences_small/direct:1", "repeated_library_longest_common_subsequences_small/direct:2", "repeated_library_longest_common_subsequences_small/direct:3", "repeated_library_longest_common_subsequences_small/direct:4", "repeated_library_longest_common_subsequences_small/respelled:1", "repeated_library_longest_common_subsequences_small/respelled:2", "repeated_library_longest_common_subsequences_small/respelled:3", "repeated_library_longest_common_subsequences_small/respelled:4", "repeated_library_billboards/direct:1", "repeated_library_billboards/respelled:1", "repeated_library_billboards_small/direct:1", "repeated_library_billboards_small/respelled:1", "repeated_library_smallest_teams/direct:1", "repeated_library_smallest_teams/direct:2", "repeated_library_smallest_teams/direct:3", "repeated_library_smallest_teams/direct:4", "repeated_library_smallest_teams/direct:5", "repeated_library_smallest_teams/direct:6", "repeated_library_smallest_teams/respelled:1", "repeated_library_smallest_teams/respelled:2", "repeated_library_smallest_teams/respelled:3", "repeated_library_smallest_teams/respelled:4", "repeated_library_smallest_teams/respelled:5", "repeated_library_smallest_teams/respelled:6", "repeated_library_smallest_teams_small/direct:1", "repeated_library_smallest_teams_small/direct:2", "repeated_library_smallest_teams_small/direct:3", "repeated_library_smallest_teams_small/direct:4", "repeated_library_smallest_teams_small/direct:5", "repeated_library_smallest_teams_small/direct:6", "repeated_library_smallest_teams_small/respelled:1", "repeated_library_smallest_teams_small/respelled:2", "repeated_library_smallest_teams_small/respelled:3", "repeated_library_smallest_teams_small/respelled:4", "repeated_library_smallest_teams_small/respelled:5", "repeated_library_smallest_teams_small/respelled:6", "repeated_library_hotspots_calls_1000/direct:1", "repeated_library_hotspots_calls_1000/respelled:1", "repeated_library_hotspots_calls_10000/direct:1", "repeated_library_hotspots_calls_10000/respelled:1", "repeated_library_hotspots_calls_100000/direct:1", "repeated_library_hotspots_calls_100000/respelled:1")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var point: String = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The seed of the draws, which JMH assigns: the public seed by default. */
  @SuppressWarnings(Array("org.wartremover.warts.Var")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  @Param(Array("20261031")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
  var seed: Long = uninitialized // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")

  /** The reduction group read from Gezi's directory. */
  lazy val group: ReductionGroup = ReductionGroup(FixedPointLines.buildRoot, Expansions.none, gezi.contest.entry.Defaults.caches())

  /** The point's stem and count of sites. */
  lazy val (stem: String, repetitions: Int) = point.split(':').toVector match
    case Vector(stemPart, repetitionsPart) => (stemPart, repetitionsPart.toInt)
    case other                              => throw IllegalArgumentException(s"a point is stem:repetitions, not ${other.mkString(":")}")

  /** The native solver of the point, on draws made once: the family's
    * `NativelySolved.solved` for the families that have one, and for the
    * longest common subsequences and the billboards, which have no solver
    * of their own (a billboards' trap site has no normal form), the
    * hand-written solutions of `ContestWorkloadSolutions` on the draws the
    * generator makes at the seed mixed with the family's `drawStem`: for
    * the billboards, the rods and the target of each site, and whether the
    * rods reach the target.
    */
  lazy val solve: () => Any =
    RepeatedVariants.all.collectFirst {
      case family: NativelySolved[drawn] if family.stem == stem =>
        val problem = NativeProblem(family, family.drawnAt(group, seed, repetitions))
        () => problem.solved
      case family: LibraryLongestCommonSubsequences if family.stem == stem =>
        val strings = LibraryLongestCommonSubsequences
          .drawn(family.nominal, Draws.fromSeedAndStem(seed, family.drawStem), repetitions)
          .sites
          .map(site => (IArray.from(site.first), IArray.from(site.second)))
        () => strings.map((first, second) => ContestWorkloadSolutions.longestCommonSubsequence(first, second))
      case family: LibraryBillboards if family.stem == stem =>
        val sites = LibraryBillboards
          .drawn(family.nominal, Draws.fromSeedAndStem(seed, family.drawStem), repetitions)
          .sites
          .map(site => (IArray.from(site.rods), site.target))
        () => sites.map((rods, target) => ContestWorkloadSolutions.billboardReaches(rods, target))
    }.getOrElse(throw IllegalArgumentException(s"no family has the stem $stem"))

  /** The draws made before the trial, so that no iteration draws. */
  @Setup(Level.Trial)
  def built(): Unit =
    solve() match
      case answers: Vector[?] => assert(answers.size == repetitions, s"$point answers another count of sites")
      case other              => throw IllegalStateException(s"$point answers $other, not a vector of sites")

/** The native solver of the four workload families (the hand-written
  * solutions for the longest common subsequences and the billboards) and their low rungs on
  * one point at every count of sites R from 1 to the family's top R: the
  * per-rung companion of `NativeSolverBenchmark`, with its mode and its
  * settings (average time of a call, one fork with the serial collector,
  * five warm-up and five measurement iterations of one second).
  */
@BenchmarkMode(Array(Mode.AverageTime)) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Fork(value = 1, jvmArgsAppend = Array("-Xmx256m", "-XX:+UseSerialGC")) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构"), Inputs.scala
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
class NativeRungBenchmark:

  /** The family's native solver on the point's draws. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MICROSECONDS)
  def solved(input: NativeRungInput): Any = input.solve()
