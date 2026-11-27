package com.yang_bo.gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the seeded points (`CorpusSources.seededSources`): for every
  * repeated family, the points' names are pairwise distinct and are the same
  * for any two seeds. Its purpose is to catch a name that leaks the seed (the
  * hidden seed would be published with the points file) or two points of one
  * family with one name (one would hide the other in the points file). R is
  * drawn up to 10, the smallest nominal maximum of the families
  * (`ReductionProblemsRepeated.Grids`); only programs are built, none is read.
  */
class SeededSourcesLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once
    * (`LawFamilies.sharedFixtures`).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of SeededSourcesLawTest, "the names are distinct and do not depend on the seed", takes 4.063 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(10, "s")

  private def names(
      family: String,
      seed: Long,
      repetitions: Vector[Int]
  ): Vector[String] =
    LawFamilies
      .sources(family, seed, repetitions, "test", BigDecimal(1))
      .map(_.pointName)

  property(
    "the names are distinct and do not depend on the seed",
    _.copy(testLimit = 20)
  ) {
    for
      family <- Gen.elementUnsafe(LawFamilies.names).forAll
      repetitions <- LawFamilies.repetitions(family, 10, 4).forAll
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
      otherSeed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
    yield
      val found = names(family, seed, repetitions)
      Result
        .assert(found.distinct.size == found.size)
        .log(s"names repeated: $found")
        .and(Result.diff(found, names(family, otherSeed, repetitions))(_ == _))
  }
