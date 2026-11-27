package com.yang_bo.gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import com.yang_bo.gezi.contest.corpora.reductions.Reference
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The trap candidates taken from the second instance's other points of the
  * same family when its point of the same name repeats the reference
  * (`PointsFile.written` with a trap draw). The second instance is the drawn
  * family itself, so every point of the same name reads the reference, plus one
  * extra point of each family under another name, whose computed reference is a
  * drawn set of closed normal forms (an abstraction nest around a variable).
  * The points' own computed trap candidates (`DrawnPoint.trapCandidates`, the
  * CSES families') are dropped, since the writer takes them before the second
  * instance and the fallback would not be reached (`ComputedTrapsLawTest`
  * checks them). Its purpose is to catch a trap that is in the reference or
  * that no peer read. Every iteration checks the law also on a draw of
  * `LawFamilies.trapAtEveryPoint`, whose points are pure with one computed
  * normal form, a list of one answer, which no peer's normal form (an
  * abstraction nest around a variable) is, so that it writes a trap by
  * construction, which catches a fallback that never writes one.
  */
class TrapFamilyFallbackLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once
    * (`LawFamilies.sharedFixtures`).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  // Measured 2026-11-20 (CPUs 0 to 7, the 1-minute load 3.9 to 4.9): the suite, one test, takes 8.4 and 8.9 s alone, the
  // law families' fixtures built in `beforeAll` included (16.3 s on 2026-11-19, before the lexer compiled its parser once,
  // b18f8f987, and when each draw was written and read twice, once for the coverage and once for the law), and 2.4 s the
  // same day in one JVM after the judge's other suites, each draw still written twice. At the 3 s default the test
  // overruns alone by little, three runs of three: the cost of a JVM not yet warm, not a defect of the draws' work, whose
  // reading back and writing are linear in the line.
  // The bound is 1.5 times the longer, rounded up to 5 s.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  private val writerBudget: Long = 200000

  /** A closed normal form: `depth` abstractions around a variable bound by one
    * of them.
    */
  private val normalForms: Gen[Vector[DeBruijnTerm]] =
    (for
      depth <- Gen.int(Range.constant(1, 3))
      index <- Gen.int(Range.constant(0, depth - 1))
    yield (1 to depth).foldLeft[DeBruijnTerm](DeBruijnTerm.Variable(index))(
      (body, _) => DeBruijnTerm.Lambda(body)
    ))
      .list(Range.constant(1, 4))
      .map(_.toVector.distinct)

  private val draws: Gen[(String, Long, Vector[DeBruijnTerm])] = drawsOf(
    Gen.elementUnsafe(LawFamilies.names)
  )

  /** The draws of a family the generator gives. */
  private def drawsOf(
      families: Gen[String]
  ): Gen[(String, Long, Vector[DeBruijnTerm])] =
    for
      family <- families
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1))
      peerNormalForms <- normalForms
    yield (family, seed, peerNormalForms)

  property(
    "a trap of a point repeated by its second instance is a normal form of a peer",
    _.copy(testLimit = 20)
  ) {
    for
      draw <- draws.forAll
      trapped <- drawsOf(Gen.constant(LawFamilies.trapAtEveryPoint)).forAll
    yield
      val (trappedLaw, trappedTraps) = fallbackLaw(trapped)
      fallbackLaw(draw)._1
        .and(trappedLaw)
        .and(
          Result
            .assert(trappedTraps.nonEmpty)
            .log(s"${LawFamilies.trapAtEveryPoint} writes no trap")
        )
  }

  /** The law on the file written from the draw, with its traps. */
  private def fallbackLaw(
      draw: (String, Long, Vector[DeBruijnTerm])
  ): (Result, Vector[(String, DeBruijnTerm)]) =
    val (_, _, peerNormalForms) = draw
    val (references, traps) = written(draw)
    val law = Result.all(
      traps
        .map((evaluation, candidate) =>
          Result
            .assert(
              peerNormalForms.contains(candidate) && !references(evaluation)
                .contains(candidate)
            )
            .log(
              s"$evaluation: a trap outside the peers' normal forms or in the reference"
            )
        )
        .toList
    )
    (law, traps)

  /** The references of the evaluation points written, and the traps as
    * (evaluation point, candidate).
    */
  private def written(
      draw: (String, Long, Vector[DeBruijnTerm])
  ): (Map[String, Set[DeBruijnTerm]], Vector[(String, DeBruijnTerm)]) =
    val (family, seed, peerNormalForms) = draw
    val evaluations = LawFamilies
      .sources(family, seed, Vector(1), "test", BigDecimal(1))
      .collect { case source: PointSource.EvaluationSource =>
        source.copy(trapCandidates = Vector.empty)
      }
    val sources: Vector[PointSource] = evaluations
    val peers = evaluations
      .map(_.family)
      .distinct
      .map(peerFamily =>
        evaluations
          .find(_.family == peerFamily)
          .get
          .copy(
            name = s"peer/$peerFamily",
            reference = Reference.Computed(peerNormalForms, "drawn")
          )
      )
    val directory = Files.createTempDirectory("trap-fallback")
    PointsFile.written(
      directory,
      sources,
      writerBudget,
      Some(
        JudgmentPoints(
          BigDecimal(2),
          false,
          Some(TrapDraw(sources ++ peers, 3))
        )
      )
    )
    val points = PointsFile.read(directory)
    val references = points.collect {
      case Point(name, _, _, _, _, Question.Evaluation(reference)) =>
        name -> reference
    }.toMap
    val traps = points.collect {
      case Point(name, _, _, _, _, Question.Judgment(candidate, false)) =>
        name.substring(
          0,
          name.lastIndexOf("/candidate_")
        ) -> com.yang_bo.gezi.frontend.Defunctionalization.instructionTerm(candidate)
    }
    (references, traps)
