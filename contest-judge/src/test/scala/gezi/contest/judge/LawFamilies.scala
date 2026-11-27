package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import java.nio.file.Paths
import gezi.contest.corpora.reductions.LibraryBillboards
import gezi.contest.corpora.reductions.CsesFamilies
import gezi.contest.corpora.reductions.LibraryEditDistances
import gezi.contest.corpora.reductions.LibraryHotspots
import gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import gezi.contest.corpora.reductions.LibrarySmallestTeams
import gezi.contest.corpora.reductions.MixinBuiltinBinary
import gezi.contest.corpora.reductions.MixinBuiltinBoolean
import gezi.contest.corpora.reductions.MixinBuiltinNatural
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.RepeatedVariant
import gezi.contest.corpora.reductions.Repetition
import gezi.contest.corpora.reductions.StandardLibraryFamilyRanges
import gezi.weakhead.Expansions

/** The repeated families the judge's laws draw: `CorpusSources.seededFamilies`,
  * with the workload families of programming-contest size read at the small
  * ranges of their own tests (`StandardLibraryFamilyRanges`), as the Repeated
  * suites' `lawVariant` reads them. At their points' ranges one site of
  * `repeated_library_longest_common_subsequences` is a string of 3000
  * characters, and a one-site point's program is about 3.6 MB (seed 20261031,
  * 2026-11-01), too large for a law drawn 20 times; and
  * `repeated_library_billboards` has R = 1 only;
  * `repeated_library_edit_distances` has strings of 3000 characters as well,
  * and a site of `repeated_library_smallest_teams` is 2^60 choices to
  * weak_head; a site of each rung of `repeated_library_hotspots` (and of its
  * cold and hot calibration variants, and of the hot variants' other shapes) is
  * up to 256 functions of 32 steps called up to 10^5 times, whose native
  * reference a law drawn 20 times would compute again and again; the
  * construction of the program does not depend on the ranges. The mixin_builtin
  * families are not drawn: each of their points carries the whole
  * `problems/mixin_builtin` library, labels as variable arguments partial
  * functions, so a point's line costs seconds to write and read back, and these
  * laws, which check the points file and not the families, overran their
  * deadlines with them (measured 2026-11-21 by JFR on PointsProgramsLawTest at
  * the families' small ranges: of 6556 samples, 4070 in `PointsFile.read`, 1866
  * in writing the directory, 450 in building the points;
  * https://github.com/Atry/private-overlay/pull/1849); the families' own suites
  * (`MixinBuiltinFamilySuite`) check them. The CSES families are drawn but for
  * their top rungs (`CsesFamilies.atConstraints`), whose sites are CSES inputs,
  * up to 2 · 10^5 connections or 10^6 squares a site; their computed references
  * and trap candidates (`CsesFamily.trapCandidates`) reach these laws through
  * their lower rungs. The other families are drawn as the points draw them.
  */
object LawFamilies:

  /** The mixin_builtin families, which these laws do not draw (the object's
    * Scaladoc).
    */
  private val mixinBuiltinNames: Vector[String] =
    Vector(
      MixinBuiltinBinary.name,
      MixinBuiltinNatural.name
    ) ++ MixinBuiltinBoolean.depths.map(MixinBuiltinBoolean.name)

  /** The CSES families' top rungs, which these laws do not draw (the object's
    * Scaladoc).
    */
  private val csesNames: Vector[String] =
    CsesFamilies.atConstraints.map(_.family).distinct

  /** The group every law draws from, made once for the test JVM: a group reads
    * the library and the attractors' tables through the evaluator, and a group
    * per draw read them again for every case (`SeededSourcesLawTest`,
    * 2026-11-12: 68.89 s for twenty cases).
    */
  lazy val group: ReductionGroup = ReductionGroup(
    Paths.get(sys.props("gezi.buildRoot")),
    Expansions.none,
    gezi.contest.entry.Defaults.caches()
  )

  /** The parts of the group the families' draws read, for a suite that draws
    * them to build in `beforeAll` (`FailFastSuite.sharedFixtures`), not in its
    * first test: the library's URI expansions, the prelude the attractors read,
    * the library terms and the mixin library. Measured 2026-11-19 by JFR on
    * TrapJudgmentsLawTest: built in the first of its tests to draw them, they
    * made that test 33 s where each of the next three took 2 to 4 s on as many
    * draws.
    *
    * Also each CSES problem's function (`CsesProblems`), and that of the
    * problem built as one is (`CsesProblems.weightedPaths`), read off its file
    * when first used, one fixture each. MEASURED 2026-11-21 by a scratch replay
    * of ComputedReferencesLawTest's draws at the seed 236429941465892, at which
    * the law overran its 10 s deadline (CPUs 2 and 3 of contest.slice, nice 10,
    * the 1-minute load about 9, the other fixtures forced first): of the 20
    * cases' 7.3 s, 6.0 s went to the CSES families, the first point of each of
    * eleven problems taking 0.19 to 0.70 s (its file read) and each later point
    * of a family 0.06 to 0.3 s (both twins, the respelled one respelling the
    * function, about 0.08 s a point); the non-CSES families took 1.3 s in all.
    */
  val sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(
    _ => group.problems.sharedExpansions,
    _ => group.attractors.fixpoint,
    _ => group.standardLibrary.zero,
    _ => group.mixins,
    _ => group.cses.diceCombinations,
    _ => group.cses.minimizingCoins,
    _ => group.cses.messageRoute,
    _ => group.cses.countingRooms,
    _ => group.cses.exponentiation,
    _ => group.cses.coinCombinationsOrdered,
    _ => group.cses.coinCombinationsUnordered,
    _ => group.cses.removingDigits,
    _ => group.cses.gridPaths,
    _ => group.cses.bookShop,
    _ => group.cses.shortestRoutesSingleSource,
    _ => group.cses.shortestRoutesQueries,
    _ => group.cses.countingDivisors,
    _ => group.cses.binomialCoefficients,
    _ => group.cses.distinctNumbers,
    _ => group.cses.moneySums,
    _ => group.cses.rectangleCutting,
    _ => group.cses.increasingSubsequence,
    _ => group.cses.arrayDescription,
    _ => group.cses.buildingRoads,
    _ => group.cses.roadReparation,
    _ => group.cses.gameRoutes,
    _ => group.cses.staticRangeSums,
    _ => group.cses.trailingZeros,
    _ => group.cses.sumOfDivisors,
    _ => group.cses.exponentiationTwo,
    _ => group.cses.ferrisWheel,
    _ => group.cses.missingNumber,
    _ => group.cses.repetitions,
    _ => group.cses.staticRangeMinimums,
    _ => group.cses.stringMatching,
    _ => group.cses.subarraySums,
    _ => group.cses.sumOfTwoValues,
    _ => group.cses.treeDiameter,
    _ => group.cses.treeMatching,
    _ => group.cses.weightedPaths
  )

  /** The variants of each family, by family name. */
  val variants: Map[String, Vector[RepeatedVariant]] =
    CorpusSources.seededFamilies ++ Map(
      LibraryLongestCommonSubsequences.name -> Repetition.spellings.map(
        LibraryLongestCommonSubsequences(
          _,
          StandardLibraryFamilyRanges.longestCommonSubsequences,
          LibraryLongestCommonSubsequences.name
        )
      ),
      LibraryBillboards.name -> Repetition.spellings.map(
        LibraryBillboards(
          _,
          StandardLibraryFamilyRanges.billboards,
          LibraryBillboards.name
        )
      ),
      LibraryEditDistances.name -> Repetition.spellings.map(
        LibraryEditDistances(
          _,
          StandardLibraryFamilyRanges.editDistances,
          LibraryEditDistances.name
        )
      ),
      LibrarySmallestTeams.name -> Repetition.spellings.map(
        LibrarySmallestTeams(
          _,
          StandardLibraryFamilyRanges.smallestTeams,
          LibrarySmallestTeams.name
        )
      )
    ) -- mixinBuiltinNames -- csesNames ++ (for
      calls <- LibraryHotspots.rungCalls
      calibration <- LibraryHotspots.Calibration.values.toVector
    yield LibraryHotspots.familyName(calls, calibration) -> Repetition.spellings
      .map(
        LibraryHotspots(
          _,
          StandardLibraryFamilyRanges.hotspots,
          LibraryHotspots.familyName(calls, calibration),
          calibration
        )
      )) ++ (for
      shape <- LibraryHotspots.otherShapes
      calls <- LibraryHotspots.shapedRungCalls
    yield LibraryHotspots.shapedFamilyName(
      shape,
      calls,
      LibraryHotspots.Calibration.Hot
    ) -> Repetition.spellings.map(
      LibraryHotspots(
        _,
        StandardLibraryFamilyRanges.hotspots,
        LibraryHotspots
          .shapedFamilyName(shape, calls, LibraryHotspots.Calibration.Hot),
        LibraryHotspots.Calibration.Hot,
        shape
      )
    ))

  /** The family names, sorted. */
  val names: List[String] = variants.keys.toList.sorted

  /** A family every point of which gets a trap, by construction: the CSES
    * problem `missing_number` at its bottom rung, whose common wrong solution
    * is off by one (`MissingNumber.wrongAnswers`, `CsesFamily.offByOne`), an
    * answer below 9 plus one, never the answer, at every site, so that the list
    * of its answers is a trap candidate outside the reference
    * (`CsesFamily.trapCandidates`); its programs are pure below the top rung
    * (`CsesPurityLawTest`) and its reference computed, one normal form, so that
    * the writer takes the candidate (`PointsFile.written`).
    */
  val trapAtEveryPoint: String = gezi.contest.corpora.reductions.CsesFamily
    .familyName("missing_number", "upper_8")

  /** The largest R every variant of the family allows. */
  def largestRepetitions(family: String): Int =
    variants(family).map(_.nominal.repetitions.end).min

  /** One or more R values drawn from 1 to the smaller of `upTo` and the
    * family's largest R, the list's length from 1 to `count`.
    */
  def repetitions(family: String, upTo: Int, count: Int): Gen[Vector[Int]] =
    Gen
      .int(Range.constant(1, upTo.min(largestRepetitions(family))))
      .list(Range.constant(1, count))
      .map(_.toVector)

  /** The family's points drawn from the seed, as `CorpusSources.seededSources`
    * draws them, from the variants above, in the shared `group`.
    */
  def sources(
      family: String,
      seed: Long,
      repetitions: Vector[Int],
      stage: String,
      weight: BigDecimal
  ): Vector[PointSource] =
    CorpusSources.variantSources(
      group,
      family,
      variants(family),
      seed,
      repetitions,
      stage,
      weight
    )
