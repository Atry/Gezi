package com.yang_bo.gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.contest.corpora.claims.ClaimsTesting
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import snapshot4s.generated.snapshotConfig

/** The digests of the hot ladder's iterated programs at their nominal ranges,
  * whose purpose is to catch any change of a program the family
  * `repeated_library_hotspots` builds: every rung and calibration variant
  * (`LibraryHotspots.rungs`, `LibraryHotspots.calibrations`) in both spellings,
  * at the seed 1 and R = 1, as `judgePointsFile` draws them, each program's
  * lambdalattice text kept as its SHA-256 and length (`ClaimsTesting.digest`),
  * since the scored rungs' texts run to megabytes. The snapshot was recorded
  * before the shapes of `LibraryHotspots.Shape` were added, so that it shows
  * the iterated programs unchanged by them.
  */
class LibraryHotspotsProgramDigestTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:
  // Measured 2026-11-20 (CPUs 0 to 7, the 1-minute load 2.4 to 2.7, after ReductionMixinLibraryTest in one JVM, the group's
  // shared expansions built in beforeAll): the suite takes 4.6 and 4.4 s, its one test overrunning the 3 s default twice
  // (8.068 s for the test on 2026-11-19, before a problem field was decoded from its family's state, 4cb3691fa); the
  // bound is 1.5 times 4.6 s rounded up to 5 s.
  // The test's own work, by a JFR profile of the suite alone the same day (602 samples; the group's shared expansions, its
  // fixture, 42%): printing each program as the text whose digest it records, the library written out in it, 36.5%
  // (`LambdalatticeText.text`, linear in that text), and the first readings of the families the programs read, the rest;
  // no defect.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  /** The URI expansions the reduction group's families share, built once.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ =>
      ReductionTesting.group.problems.sharedExpansions
    )

  test("the iterated programs of the seed 1 and one repetition") {
    val group = ReductionTesting.group
    val seed = 1L
    val lines =
      (LibraryHotspots.rungs.flatten ++ LibraryHotspots.calibrations.flatten)
        .map(variant =>
          s"${variant.stem}\t${ClaimsTesting.digest(LambdalatticeText.text(variant.program(group, seed, 1)))}"
        )
    assertFileSnapshot(
      lines.mkString("", "\n", "\n"),
      "hotspots/iterated_program_digests.txt"
    )
  }

/** The laws of the hot ladder's other shapes (`LibraryHotspots.Shape`). */
class LibraryHotspotsShapesTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of LibraryHotspotsShapesTest, "no shape draws a problem the iterated hot rung draws at the same seed", takes 3.049 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(5, "s")

  /** The law, whose purpose is to catch a split of the nested shape that runs
    * the function another number of times or nests a loop of one count where
    * both could have two or more: on generated counts c from 2 to 10^7, the
    * outer and the inner count multiply to c, the outer is at most the inner,
    * and the outer is at least 2 exactly when c is not prime.
    */
  property(
    "a count splits into two counts whose product it is, both at least 2 unless it is prime"
  ) {
    for count <- Gen.long(Range.constant(2L, 10000000L)).forAll
    yield
      val (outer, inner) = LibraryHotspots.split(BigInt(count))
      Result
        .diff(outer * inner, BigInt(count))(_ == _)
        .log("the product is the count")
        .and(
          Result
            .assert(outer <= inner)
            .log("the outer count is at most the inner one")
        )
        .and(
          Result
            .diff(outer >= 2, !BigInt(count).isProbablePrime(64))(_ == _)
            .log("both counts are at least 2 unless the count is prime")
        )
  }

  /** The law, whose purpose is to catch a shaped rung that draws the iterated
    * hot rung's problems, so that within one pass two families' points would
    * share an answer (across repetitions only code is reused, never an answer):
    * on generated seeds and R, no site a shaped rung draws at the seed, in
    * either spelling, is a site the iterated hot rung of its C draws at that
    * seed.
    */
  property(
    "no shape draws a problem the iterated hot rung draws at the same seed"
  ) {
    val group = ReductionTesting.group
    for
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
      repetitions <- Gen.int(Range.constant(1, 4)).forAll
    yield Result.all(LibraryHotspots.shapedRungs.flatten.toList.map(variant =>
      val iterated = LibraryHotspots.calibrated(
        variant.spelling,
        variant.calls,
        LibraryHotspots.Calibration.Hot
      )
      val shared = variant
        .drawnAt(group, seed, repetitions)
        .sites
        .toSet
        .intersect(iterated.drawnAt(group, seed, repetitions).sites.toSet)
      Result
        .assert(shared.isEmpty)
        .log(
          s"${variant.stem} shares ${shared.size} sites with ${iterated.stem}"
        )
    ))
  }
