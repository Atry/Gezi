package gezi.contest.corpora.merges

import hedgehog.Gen
import hedgehog.Range
import gezi.generatedinputs.SeededSamples
import gezi.frontend.Term
import snapshot4s.generated.snapshotConfig

/** The generators of the mixin family, shared by their suites. */
object MixinFamily:
  val library: MixinLibrary = MixinLibrary(MergeTesting.problems)
  val claims: MixinClaims = MixinClaims(MergeTesting.problems, library)

/** The snapshot of `problems/mixin_claims`, whose purpose is to catch a
  * generator change that alters a point's program, a small search's program or
  * a claim fact: the program of every graph, subset and common subsequence
  * point (`point(<name>)`), the programs of `subsetSurface` and
  * `commonSubsequenceSurface` on arguments drawn from a fixed seed, and the
  * claim lines.
  */
class MixinClaimsTest
    extends MergeProblemsSuite
    with snapshot4s.munit.SnapshotAssertions:

  private val claims = MixinFamily.claims

  /** The seed of the drawn arguments. */
  private val seed = 20261112L

  /** Items and a target of a subset search: one or two naturals and a bound,
    * each from 0 to 6.
    */
  private val subsetArguments: Gen[(List[Int], Int)] =
    for
      items <- Gen.list(Gen.int(Range.constant(0, 6)), Range.constant(1, 2))
      target <- Gen.int(Range.constant(0, 6))
    yield (items, target)

  /** Two strings of one or two of the symbols a and b, and a needed length from
    * 0 to 6.
    */
  private val commonSubsequenceArguments: Gen[(List[Char], List[Char], Int)] =
    val string = Gen.list(Gen.element('a', List('b')), Range.constant(1, 2))
    for
      left <- string
      right <- string
      need <- Gen.int(Range.constant(0, 6))
    yield (left, right, need)

  private def points: Vector[(String, () => Term)] =
    (claims.graphPoints.map(_._1) ++ claims.subsetPoints.map(
      _._1
    ) ++ claims.commonSubsequencePoints.map(_._1))
      .map(name => s"point($name)" -> (() => claims.program(name)))

  private def subsetSearches: Vector[(String, () => Term)] =
    SeededSamples
      .samples(subsetArguments, seed, 3)
      .distinct
      .map((items, target) =>
        s"subset_surface(${items.mkString("[", ",", "]")},$target)" ->
          (() =>
            claims.subsetSurface(items.toVector.map(BigInt(_)), BigInt(target))
          )
      )

  private def commonSubsequenceSearches: Vector[(String, () => Term)] =
    SeededSamples
      .samples(commonSubsequenceArguments, seed, 3)
      .distinct
      .map((left, right, need) =>
        s"common_subsequence_surface(${MergeDynamic.symbols(left.toVector)},${MergeDynamic.symbols(right.toVector)},$need)" ->
          (() =>
            claims.commonSubsequenceSurface(left.toVector, right.toVector, need)
          )
      )

  test("the points' and the drawn searches' programs") {
    assertFileSnapshot(
      GeneratedProgramLines.programs(
        points ++ subsetSearches ++ commonSubsequenceSearches
      ),
      "generated_programs/contest_mixin_claims.txt"
    )
  }

  test("the points' claims") {
    assertFileSnapshot(
      GeneratedProgramLines.claims(claims.claims),
      "generated_claims/contest_mixin_claims.txt"
    )
  }
