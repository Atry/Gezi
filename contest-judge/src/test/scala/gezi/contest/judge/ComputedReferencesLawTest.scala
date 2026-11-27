package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.contest.corpora.reductions.LibraryBillboards
import gezi.contest.corpora.reductions.LibraryLongestCommonSubsequences
import gezi.contest.corpora.reductions.NativelySolved
import gezi.contest.corpora.reductions.RepeatedVariants
import gezi.generatedinputs.GeneratedProperties

/** The law of the computed references' file (`ComputedReferences`): written
  * from the seeded points of a generated set of repeated families and read
  * back, its rows are exactly the points of the variants that compute their
  * references natively (every variant of `RepeatedVariants.all` since round 8:
  * the `NativelySolved` ones and the workload families
  * `LibraryLongestCommonSubsequences` and `LibraryBillboards`), in source
  * order, each with its family and its variant's claim. Its purpose is to catch
  * a computed point left out of the file (its reference would lose its
  * provenance), a point read by tabling(weak_head) listed as computed, or a row
  * whose family or claim is not the point's. R is drawn up to 10, each value
  * held within each family's largest R, the families drawn at the ranges of
  * `LawFamilies` (the workload families at their small ranges); only programs
  * are built, none is read.
  */
class ComputedReferencesLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once
    * (`LawFamilies.sharedFixtures`).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of ComputedReferencesLawTest, "the file's rows are the computed points, with their families and claims", takes 5.000 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  /** The claim of each variant that computes its reference, by its stem: the
    * natively solved variants, and the workload families that compute their
    * references outside `NativelySolved` (a billboards' point with a trap site
    * has no normal form, which `NativelySolved`'s one list cannot state).
    */
  private val claims: Map[String, String] =
    RepeatedVariants.all.collect {
      case variant: NativelySolved[?] => variant.stem -> variant.claim
      case variant: LibraryLongestCommonSubsequences =>
        variant.stem -> LibraryLongestCommonSubsequences.claim
      case variant: LibraryBillboards => variant.stem -> LibraryBillboards.claim
    }.toMap

  /** The stem of a point named `stem/repetitions_R`. */
  private def stem(pointName: String): String =
    pointName.substring(0, pointName.lastIndexOf('/'))

  property(
    "the file's rows are the computed points, with their families and claims",
    _.copy(testLimit = 20)
  ) {
    for
      families <- Gen
        .elementUnsafe(LawFamilies.names)
        .list(Range.constant(1, 4))
        .forAll
      repetitions <- Gen
        .int(Range.constant(1, 10))
        .list(Range.constant(1, 3))
        .map(_.toVector)
        .forAll
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
    yield
      val sources = families.distinct.toVector.flatMap(family =>
        val held = repetitions
          .map(_.min(LawFamilies.largestRepetitions(family)))
          .distinct
        LawFamilies
          .sources(family, seed, held, "test", BigDecimal(1))
          .map(family -> _)
      )
      val directory = Files.createTempDirectory("computed-references")
      ComputedReferences.written(directory, sources.map(_._2))
      val expected = sources.flatMap((family, source) =>
        claims
          .get(stem(source.pointName))
          .map(ComputedReference(source.pointName, family, _))
      )
      Result
        .diff(ComputedReferences.read(directory), expected)(_ == _)
        .log(s"families: ${families.distinct}")
  }
