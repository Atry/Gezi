package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.frontend.Defunctionalization
import gezi.frontend.ExchangeText
import gezi.generatedinputs.GeneratedProperties

/** The laws of the judgment points with traps (`PointsFile.written` with a
  * trap draw), on a repeated family drawn from a seed, its traps from a
  * second seed, read within a small budget:
  *
  *   - every trap (a not_member judgment point) has an evaluation point
  *     whose reference is exactly one normal form, and a candidate other
  *     than it; every member judgment point has a candidate in the
  *     reference. Its purpose is to catch a trap that is a member (it would
  *     mark a correct entry wrong) or one given to a point whose reference
  *     is not one normal form (purity is `ProgramPurity`'s own law);
  *   - every evaluation point with judgment points has a trap among them.
  *     Its purpose is to catch a point whose judgment points all expect
  *     member, which an entry could answer `proved` without reading;
  *   - the judgment points of an evaluation point E are named
  *     `E/candidate_0` to `E/candidate_<n-1>`, the k-th the candidate of
  *     rank k among E's candidates by `ExchangeText.line`, whatever its
  *     expectation. Its purpose is to catch a name that gives the expected
  *     answer away to the entry, which receives the name on the pipe;
  *   - with `judgmentsOnly` the file holds the judgment points of the file
  *     written without it, and no evaluation point. Its purpose is to catch
  *     an evaluation row left in, or a judgment point lost or changed.
  *
  * An input whose points get no trap satisfies the first law vacuously; the
  * property requires that at least 20% of its 30 inputs write one. The
  * share measured on 2026-10-31 was 72% of 100 inputs, in one run, so a run
  * under 20% (fewer than 6 of 30) has a probability of about 4e-10 (the
  * binomial tail at 72%) and is a sign that the writer or the corpora
  * changed.
  *
  * An input is logged by its draw, not by its points: Hedgehog's `forAll`
  * logs every input by its `toString`, eagerly, and the derived `toString`
  * of a deep program overflows the JVM's stack (`MemberJudgmentsLawTest`).
  */
class TrapJudgmentsLawTest extends GeneratedProperties:

  /** The parts of the law families' group the draws read, built once (`LawFamilies.sharedFixtures`). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  // Measured 2026-11-20 (CPUs 0 to 7, the 1-minute load 1.2 to 3.8): the suite, three tests, takes 19.5 s alone with the
  // law families' fixtures built in `beforeAll`; with the first three laws drawn apart, five tests, it took 24.5 to 27 s
  // at the load 4 to 6. A passing test reports no time of its own; the bound stays 55 s, set from the suite's 36.3 s of
  // 2026-11-19 at 552062eef, until a test's own time is measured.
  // The cost is the draws' work, not a defect: by a JFR
  // profile of the suite that day before the laws shared their files (2,212 samples, inclusive), reading the points file
  // back 51% (`ExchangeText.term`: the parse 14%, the contraction of the printer's bindings 19%, printing again to check
  // the spelling), writing it 20%, the printer in both 37%; each is linear in the line, the printer at most two passes,
  // and each point writes in its line the library it uses. The lexer's per-call compile, the one defect found, was
  // removed in b18f8f987.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(55, "s")


  /** The tabling(weak_head) steps the writer reads a reference within: small points
    * only.
    */
  private val writerBudget: Long = 200000

  /** A repeated family, its points' seed, a different trap seed, and the R
    * values, small.
    */
  private val draws: Gen[(String, Long, Long, Vector[Int])] =
    for
      family <- Gen.elementUnsafe(LawFamilies.names)
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1))
      trapSeed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).filter(_ != seed)
      repetitions <- LawFamilies.repetitions(family, 3, 2)
    yield (family, seed, trapSeed, repetitions)

  /** The points of the file written from the draw, with traps of count 3. */
  private def writtenPoints(draw: (String, Long, Long, Vector[Int]), judgmentsOnly: Boolean): Vector[Point] =
    val (family, seed, trapSeed, repetitions) = draw
    val sources = LawFamilies.sources(family, seed, repetitions, "test", BigDecimal(1))
    val secondInstance = LawFamilies.sources(family, trapSeed, repetitions, "test", BigDecimal(1))
    val directory = Files.createTempDirectory("trap-judgments")
    PointsFile.written(
      directory,
      sources,
      writerBudget,
      Some(JudgmentPoints(BigDecimal(2), judgmentsOnly, Some(TrapDraw(secondInstance, 3))))
    )
    PointsFile.read(directory)

  private def evaluationName(judgmentName: String): String = judgmentName.substring(0, judgmentName.lastIndexOf("/candidate_"))

  private def isTrap(point: Point): Boolean = point.question match
    case Question.Judgment(_, false) => true
    case _                           => false

  /** Every trap's point has one normal form and the trap is not it; every
    * member judgment's candidate is in its reference.
    */
  private def trapsOutsideTheirReferences(points: Vector[Point]): Result =
    val references = points.collect { case Point(name, _, _, _, _, Question.Evaluation(reference)) => name -> reference }.toMap
    Result.all(points.collect { case Point(name, _, _, _, _, Question.Judgment(candidate, member)) =>
      val reference = references(evaluationName(name))
      if member then Result.assert(reference.contains(Defunctionalization.instructionTerm(candidate))).log(s"$name: a member judgment outside the reference")
      else
        Result
          .diff(reference.size, 1)(_ == _)
          .log(s"$name: a trap of a reference that is not one normal form")
          .and(Result.assert(!reference.contains(Defunctionalization.instructionTerm(candidate))).log(s"$name: a trap in the reference"))
    }.toList)

  /** Every point with judgment points has a trap among them. */
  private def everyJudgedPointTrapped(points: Vector[Point]): Result =
    val judgments = points.collect { case point @ Point(name, _, _, _, _, Question.Judgment(_, _)) => evaluationName(name) -> point }
    Result.all(judgments.groupMap(_._1)(_._2).toList.map((evaluation, judged) =>
      Result.assert(judged.exists(isTrap)).log(s"$evaluation: judgment points that all expect member")
    ))

  /** A judgment point is named by its candidate's rank, whatever its expectation. */
  private def namedByRank(points: Vector[Point]): Result =
    val judgments = points.collect { case Point(name, _, _, _, _, Question.Judgment(candidate, _)) => (name, candidate) }
    Result.all(judgments.groupBy((name, _) => evaluationName(name)).toList.map((evaluation, named) =>
      val expected = named.map(_._2).sortBy(ExchangeText.line).zipWithIndex.map((candidate, index) =>
        (s"$evaluation/candidate_$index", candidate)
      )
      Result.diff(named.sortBy(_._1), expected.sortBy(_._1))(_ == _)
    ))

  // The first three laws on one file each: each law reads the points of a written file and nothing else, so one file
  // serves all three, each law on 30 inputs as before. Drawn apart, each property wrote and read 30 files of its own,
  // 90 in all, which was the suite's cost.
  property("the points with traps: every trap's point has one normal form, every judged point has a trap, names by rank", _.copy(testLimit = 30)) {
    for points <- draws.forAll.map(writtenPoints(_, false)).cover(20, "writes a trap", _.exists(isTrap))
    yield Result.all(
      List(
        trapsOutsideTheirReferences(points).log("every trap's point has one normal form, and the trap is not it"),
        everyJudgedPointTrapped(points).log("every point with judgment points has a trap among them"),
        namedByRank(points).log("a judgment point is named by its candidate's rank, whatever its expectation")
      )
    )
  }

  property("--judgments-only writes the judgment points and no evaluation point", _.copy(testLimit = 10)) {
    for draw <- draws.forAll
    yield
      val all = writtenPoints(draw, false)
      Result.diff(writtenPoints(draw, true), all.filter(point => point.question match
        case Question.Judgment(_, _) => true
        case _                       => false
      ))(_ == _)
  }

  /** The options the command needs a weight of member judgments for, each
    * given without it: the flag, the two trap options, or the flag with them.
    */
  private val withoutMemberJudgments: Gen[Vector[String]] = Gen.element1(
    Vector("--judgments-only"),
    Vector("--trap-seed-file", "unread", "--trap-judgments", "3"),
    Vector("--judgments-only", "--trap-seed-file", "unread", "--trap-judgments", "3")
  )

  property("the judgment options throw without --member-judgments") {
    for
      extra <- withoutMemberJudgments.forAll
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1)).forAll
    yield
      val output = Files.createTempDirectory("trap-options")
      val arguments = Vector(
        "--corpora", "repeated_reduction_meanings", "--stage", "test", "--weight", "1", "--budget", "1000",
        "--seed", seed.toString, "--repetitions", "1", "--output", output.toString
      ) ++ extra
      intercept[IllegalArgumentException](judgePointsFile(arguments*))
      Result.diff(Files.exists(output.resolve(PointsFile.fileName)), false)(_ == _)
  }
