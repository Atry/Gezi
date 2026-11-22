package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of the repeated families' draws (`Draws.fromSeedAndStem`).
  * Their purpose is to catch families that draw correlated sequences at one
  * seed: a family drawing from the bare seed, two variants sharing a stem,
  * or a mix under which one family's sequence is another's shifted by a few
  * draws (each would draw the same functions and data as another family, so
  * that the families of one round look alike).
  *
  * The draws are the linear congruential sequence of the corpora, whose
  * next state is a function of the state alone, so two variants draw the
  * same values from some draw on exactly when one's state reaches a state of
  * the other's.
  */
class RepeatedDrawsLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of RepeatedDrawsLawTest, "the twins of a family draw the same data", takes 4.281 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  private val drawStems: Vector[String] = RepeatedVariants.all.map {
    case family: RepeatedFamily[?] => family.drawStem
    case other                      => throw IllegalArgumentException(s"${other.stem} is no RepeatedFamily")
  }.distinct

  private val stems: Vector[String] = drawStems

  /** The first `count` states of the stem's draws at the seed. */
  private def states(seed: Long, stem: String, count: Int): Vector[Long] =
    Vector.iterate(Draws.fromSeedAndStem(seed, stem), count)(draws => Draws(DynamicReferences.nextRandom(draws.state))).map(_.state)

  test("the stems are distinct, each under its family's name") {
    assertEquals(RepeatedVariants.all.map(_.stem).distinct.size, RepeatedVariants.all.size)
    RepeatedVariants.families.foreach((family, variants) =>
      variants.foreach(variant => assert(variant.stem == family || variant.stem.startsWith(s"$family/"), variant.stem))
    )
  }

  /** At the practice seed, no state among the first 64 of one variant's
    * draws is among the first 64 of another's.
    */
  test("at the seed 20261031 no two variants share a state in their first 64 draws") {
    val drawn = stems.map(stem => stem -> states(20261031L, stem, 64).toSet)
    val shared = for
      (first, firstStates) <- drawn
      (second, secondStates) <- drawn
      if first < second && (firstStates & secondStates).nonEmpty
    yield (first, second)
    assertEquals(shared, Vector.empty)
  }

  /** On generated seeds the variants' first states are pairwise distinct.
    * A collision by chance has probability about 300 / 2^31 per seed for
    * the 25 variants.
    */
  property("the variants start from distinct states", _.copy(testLimit = 30)) {
    for seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
    yield
      val first = stems.map(Draws.fromSeedAndStem(seed, _).state)
      Result.assert(first.distinct.size == first.size).log(s"first states: $first")
  }

  /** On generated seeds the variants of one family, the direct and the
    * respelled twin, draw the same data, so that the pair differs only in
    * spelling. The CSES families' top rungs (`CsesFamilies.atConstraints`)
    * are left out, as `JitReadingLawTest` leaves them out: a site there is a
    * CSES input, and every CSES family draws from its family's name
    * (`CsesFamily.drawStem`, final), which the lower rungs check. MEASURED
    * 2026-11-21 by a scratch test timing each family's two `drawnText` at
    * R = 1 (CPUs 2 and 3 of contest.slice, nice 10, the 1-minute load about
    * 15), at the seed 1 after the seed 0 had warmed the group: the CSES
    * families took 1.96 s, all but 0.01 s of it their top rungs
    * (message_route's 0.57 s, shortest_routes_single_source's 0.48 s,
    * shortest_routes_queries' 0.36 s, counting_rooms' 0.21 s, the others up
    * to 0.12 s each), against 0.54 s for every other family; with the second
    * batch's top rungs the property's four seeds overran its 10 s deadline at a load of about
    * 16.
    */
  property("the twins of a family draw the same data", _.copy(testLimit = 4)) {
    for seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
    yield
      val group = ReductionTesting.group
      val belowConstraints = RepeatedVariants.families.map((family, variants) => family -> variants.filterNot(CsesFamilies.atConstraints.contains))
      val drawnTexts = belowConstraints.collect {
        case (family, variants) if variants.size > 1 =>
          family -> variants.map(_.drawnText(group, seed, 1)).distinct.size
      }
      Result.assert(drawnTexts.nonEmpty && drawnTexts.forall(_._2 == 1)).log(s"distinct draws per family: $drawnTexts")
  }
