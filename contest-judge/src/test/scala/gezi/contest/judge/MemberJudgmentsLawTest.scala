package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.generatedinputs.GeneratedProperties

/** The law of the member judgment points (`PointsFile.written` with a
  * weight of member judgments): in the file written from generated sources,
  * every judgment point `E/candidate_k` has an evaluation point E written,
  * the same program, the family `<E's family>_judgments`, member true and a
  * candidate in E's reference, and E has one judgment point per member of
  * its reference. Its purpose is to catch a judgment point whose candidate
  * is not a member (it would mark a correct entry wrong), one attached to
  * the wrong evaluation point, or a member left without its point. A name
  * met twice is caught by the writer, which throws (`PointsFile.written`)
  * and so fails the property. The sources are a repeated family drawn from
  * a seed, or a window of a corpus family's problems starting within the
  * family, read within a small budget. An input whose points are all
  * stopped by the budget yields no judgment point, and the law holds on it
  * vacuously; the property requires that at least 20% of its 15 inputs
  * yield one. The share measured on 2026-10-31 was 59% of 100 inputs, in
  * each of two runs, so a run under 20% (fewer than 3 of 15) has a
  * probability of about 4e-4 (the binomial tail at 59%) and is a sign that
  * the writer or the corpora changed.
  *
  * An input is logged by its points' names: Hedgehog's `forAll` logs every
  * input by its `toString`, eagerly, and the derived `toString` of a deep
  * program recurses past the JVM's stack (a StackOverflowError in
  * `DeBruijnTerm.toString`, measured on 2026-10-31 in one run of four).
  */
class MemberJudgmentsLawTest extends GeneratedProperties:

  // Measured 2026-11-19 at 552062eef (CPUs 10 and 11): the suite, one test, takes 15.9 s alone at the 1-minute load 4.7,
  // and 25.3 s in contest-judge/test at 5.4 with the law families' fixtures built in `beforeAll`, which the suite's time
  // includes (32.8 s before they were, the first suite of its JVM building them in its test). A passing test reports no
  // time of its own, so the bound is 1.5 times the longer, rounded up to 5 s.
  // Measured again 2026-11-20 (CPUs 0 to 7, the 1-minute load 2.2 to 2.7): 7.6 s in one JVM after
  // TrapJudgmentsLawTest, which built the law families' fixtures.
  // The cost is the draws' work, not a defect: by a JFR
  // profile of TrapJudgmentsLawTest that day (2,212 samples), writing the points file and reading it back, each linear
  // in the line: the parse, the contraction of the printer's bindings (each value converted once), the printer (at most
  // two passes); each point writes in its line the library it uses. The lexer's per-call compile, the one defect found,
  // was removed in b18f8f987.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(40, "s")

  /** The parts of the law families' group the draws read, built once (`LawFamilies.sharedFixtures`). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  /** The tabling(weak_head) steps the writer reads a reference within: small points
    * only.
    */
  private val writerBudget: Long = 200000

  private val seeded: Gen[Vector[PointSource]] =
    for
      family <- Gen.elementUnsafe(LawFamilies.names)
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1))
      repetitions <- LawFamilies.repetitions(family, 3, 2)
    yield LawFamilies.sources(family, seed, repetitions, "test", BigDecimal(1))

  private val corpus: Gen[Vector[PointSource]] =
    for
      family <- Gen.elementUnsafe(CorpusSources.families.keys.toList.sorted)
      problems = CorpusSources.sources(LawFamilies.group, family, "test", BigDecimal(1))
      start <- Gen.int(Range.constant(0, problems.size - 1))
    yield problems.drop(start).take(3)

  /** The points of the file written from the sources. */
  private def writtenPoints(sources: Vector[PointSource]): Vector[Point] =
    val directory = Files.createTempDirectory("member-judgments")
    PointsFile.written(directory, sources, writerBudget, Some(JudgmentPoints(BigDecimal(2), false, None)))
    PointsFile.read(directory)

  private def isJudgment(point: Point): Boolean = point.question match
    case Question.Judgment(_, _) => true
    case _                       => false

  property("every member judgment's candidate is in its evaluation point's reference", _.copy(testLimit = 15)) {
    for
      points <- Gen
        .choice1(seeded, corpus)
        .forAllWithLog(sources => sources.map(_.pointName).mkString(", "))
        .map(writtenPoints)
        .cover(20,"yields a judgment point", _.exists(isJudgment))
    yield
      val evaluations = points.collect { case point @ Point(name, _, _, _, _, Question.Evaluation(reference)) =>
        name -> (point, reference)
      }.toMap
      val judgments = points.collect { case point @ Point(name, _, _, _, _, Question.Judgment(candidate, member)) =>
        (name, point, candidate, member)
      }
      val attached = judgments.map((name, point, candidate, member) =>
        val evaluationName = name.substring(0, name.lastIndexOf("/candidate_"))
        evaluations.get(evaluationName) match
          case Some((evaluation, reference)) =>
            Result
              .assert(reference.contains(gezi.frontend.Defunctionalization.instructionTerm(candidate)) && member)
              .log(s"$name: the candidate is not a member of $evaluationName's reference")
              .and(Result.assert(point.program == evaluation.program).log(s"$name: another program than $evaluationName's"))
              .and(Result.diff(point.family, s"${evaluation.family}_judgments")(_ == _))
          case None => Result.failure.log(s"$name: no evaluation point $evaluationName")
      )
      val counted = evaluations.toVector.map { case (name, (_, reference)) =>
        Result.diff(judgments.count((judgmentName, _, _, _) => judgmentName.startsWith(s"$name/candidate_")), reference.size)(_ == _)
          .log(s"$name: judgment points per member")
      }
      Result.all((attached ++ counted).toList)
  }
