package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.contest.corpora.common.DeBruijnTerms
import gezi.contest.corpora.reductions.DrawnPoint
import gezi.contest.corpora.reductions.NominalRanges
import gezi.contest.corpora.reductions.Reduction
import gezi.contest.corpora.reductions.ReductionGroup
import gezi.contest.corpora.reductions.Reference
import gezi.contest.corpora.reductions.RepeatedVariant
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties

/** The laws of the traps a family computes (`DrawnPoint.trapCandidates`,
  * `PointsFile.written` with a trap draw), on a generated family whose
  * point at R is a drawn closed βη normal form N, or the choice N + N, with
  * drawn candidates that are N itself or other normal forms, carried from
  * the family through `CorpusSources.variantSources`. The second instance
  * is the family itself, so a point whose candidates hold none outside its
  * reference falls back on its peers' normal forms, as a family without
  * candidates does. Every draw begins with two points, one pure and one a
  * choice, whose candidates hold the reference and a normal form outside it
  * (`everyCase`), so that every case below is drawn in every iteration. Its
  * purpose is to catch:
  *
  *   - a computed candidate written as a trap that is equal to the
  *     reference, which would mark a correct entry wrong;
  *   - a judgment point written for a program that is not pure (the choice
  *     N + N), whose traps no proof covers;
  *   - more than `count` traps on one point;
  *   - a point whose candidates hold one outside its reference given a trap
  *     that is not among them, or fewer than `count` of them when it has
  *     that many, so that the family's wrong answers are not replaced by a
  *     second instance's normal forms;
  *   - a computed candidate that is not a closed βη normal form accepted by
  *     the writer: a redex β-equal to the reference would be a trap that is
  *     a member.
  */
class ComputedTrapsLawTest extends GeneratedProperties:

  /** The tabling(weak_head) steps the writer reads a reference within: the
    * programs are normal forms and choices of them.
    */
  private val writerBudget: Long = 10000

  /** A closed βη normal form: one to three abstractions around a variable
    * applied to up to two variables.
    */
  private val normalForms: Gen[DeBruijnTerm] =
    (for
      depth <- Gen.int(Range.constant(1, 3))
      head <- Gen.int(Range.constant(0, depth - 1))
      arguments <- Gen.int(Range.constant(0, depth - 1)).list(Range.constant(0, 2))
    yield (1 to depth).foldLeft(
      arguments.foldLeft(DeBruijnTerm.Variable(head))((function, argument) => DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(argument)))
    )((body, _) => DeBruijnTerm.Lambda(body))).filter(Reduction.normalFormTerm)

  /** A point of the generated family: its normal form, whether its program
    * is the choice of the normal form with itself, and its candidates.
    */
  private final case class GeneratedPoint(normalForm: DeBruijnTerm, choice: Boolean, candidates: Vector[DeBruijnTerm]):

    def program: Term =
      val pure = DeBruijnTerms.hoas(normalForm)
      if choice then Term.Choice(pure, pure) else pure

  /** The generated family: its point at R is the R-th point drawn, its
    * reference read, with its candidates.
    */
  private final class GeneratedFamily(points: Vector[GeneratedPoint]) extends RepeatedVariant:

    val stem: String = "computed_traps"

    val nominal: NominalRanges = NominalRanges(1 to points.size, Vector.empty)

    private def at(repetitions: Int): GeneratedPoint =
      require(nominal.repetitions.contains(repetitions), s"$repetitions repetitions are outside ${nominal.repetitions}")
      points(repetitions - 1)

    def program(group: ReductionGroup, seed: Long, repetitions: Int): Term = at(repetitions).program

    override def point(group: ReductionGroup, seed: Long, repetitions: Int): DrawnPoint =
      val drawn = at(repetitions)
      DrawnPoint(drawn.program, Reference.Read, drawn.candidates)

    def singlePrograms(group: ReductionGroup, seed: Long, repetitions: Int): Vector[Term] = Vector(program(group, seed, repetitions))

    def drawnText(group: ReductionGroup, seed: Long, repetitions: Int): String = at(repetitions).toString

  /** A point whose candidates are its own normal form (weight 1) or other
    * normal forms (weight 3), up to four.
    */
  private val generatedPoints: Gen[GeneratedPoint] =
    for
      normalForm <- normalForms
      choice <- Gen.frequency1(2 -> Gen.constant(false), 1 -> Gen.constant(true))
      candidates <- Gen.frequency1(1 -> Gen.constant(normalForm), 3 -> normalForms).list(Range.constant(0, 4))
    yield GeneratedPoint(normalForm, choice, candidates.toVector)

  /** Two points that hold every case the laws tell apart, each with the
    * candidates N, equal to its reference, and `λx. N`, outside it (another
    * closed βη normal form: x is not free in the closed N, so the abstraction
    * is neither a β-redex nor an η-redex): one pure, one the choice N + N.
    */
  private val everyCase: Gen[Vector[GeneratedPoint]] =
    for
      pure <- normalForms
      chosen <- normalForms
    yield Vector(
      GeneratedPoint(pure, false, Vector(pure, DeBruijnTerm.Lambda(pure))),
      GeneratedPoint(chosen, true, Vector(chosen, DeBruijnTerm.Lambda(chosen)))
    )

  /** The two points of `everyCase`, then one to four drawn points, and a
    * trap count from one to three.
    */
  private val draws: Gen[(Vector[GeneratedPoint], Int)] =
    for
      cases <- everyCase
      points <- generatedPoints.list(Range.constant(1, 4))
      count <- Gen.int(Range.constant(1, 3))
    yield (cases ++ points.toVector, count)

  private def evaluationName(repetitions: Int): String = s"computed_traps/repetitions_$repetitions"

  private def sources(points: Vector[GeneratedPoint]): Vector[PointSource] =
    CorpusSources.variantSources(
      LawFamilies.group,
      "computed_traps",
      Vector(GeneratedFamily(points)),
      0L,
      (1 to points.size).toVector,
      "test",
      BigDecimal(1)
    )

  /** The file's references, and each evaluation point's traps, by name. */
  private def written(points: Vector[GeneratedPoint], count: Int): (Map[String, Set[DeBruijnTerm]], Map[String, Vector[DeBruijnTerm]], Set[String]) =
    val directory = Files.createTempDirectory("computed-traps")
    val pointSources = sources(points)
    PointsFile.written(directory, pointSources, writerBudget, Some(JudgmentPoints(BigDecimal(2), false, Some(TrapDraw(pointSources, count)))))
    val read = PointsFile.read(directory)
    val references = read.collect { case Point(name, _, _, _, _, Question.Evaluation(reference)) => name -> reference }.toMap
    val judgments = read.collect { case Point(name, _, _, _, _, Question.Judgment(candidate, member)) =>
      (name.substring(0, name.lastIndexOf("/candidate_")), Defunctionalization.instructionTerm(candidate), member)
    }
    val traps = judgments.collect { case (evaluation, candidate, false) => evaluation -> candidate }.groupMap(_._1)(_._2)
    (references, traps, judgments.map(_._1).toSet)

  property("computed traps: never the reference, never on a program that is not pure, at most count, the family's first", _.copy(testLimit = 50)) {
    for
      draw <- draws.forAll
    yield
      val (points, count) = draw
      val (references, traps, judged) = written(points, count)
      Result.all(points.zipWithIndex.toList.map((point, index) =>
        val name = evaluationName(index + 1)
        val reference = references(name)
        val trapsWritten = traps.getOrElse(name, Vector.empty)
        val outside = point.candidates.distinct.filterNot(reference.contains)
        // The reference is the drawn normal form itself, so that a candidate drawn equal to it is one the writer must drop.
        Result
          .diff(reference, Set(point.normalForm))(_ == _)
          .log(s"$name: a reference other than the drawn normal form")
          .and(Result.assert(trapsWritten.forall(trap => !reference.contains(trap))).log(s"$name: a trap equal to the reference"))
          .and(Result.assert(!point.choice || !judged.contains(name)).log(s"$name: a judgment point for a program that is not pure"))
          .and(Result.assert(trapsWritten.size <= count).log(s"$name: ${trapsWritten.size} traps, more than $count"))
          .and(
            Result
              .assert(point.choice || outside.isEmpty || (trapsWritten.forall(outside.contains) && trapsWritten.size == outside.size.min(count)))
              .log(s"$name: traps other than the first $count of its computed candidates outside the reference")
          )
      ))
  }

  property("a computed candidate that is not a closed βη normal form is refused before anything is written", _.copy(testLimit = 10)) {
    for
      points <- generatedPoints.list(Range.constant(1, 3)).forAll
      redexAt <- Gen.int(Range.constant(0, 2)).forAll
    yield
      val pointsVector = points.toVector
      val index = redexAt.min(pointsVector.size - 1)
      val target = pointsVector(index)
      // (λx. x) N, β-equal to N: as a trap it would be a member.
      val redex = DeBruijnTerm.Apply(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)), target.normalForm)
      val withRedex = pointsVector.updated(index, target.copy(candidates = target.candidates :+ redex))
      val directory = Files.createTempDirectory("computed-traps-refused")
      val pointSources = sources(withRedex)
      intercept[IllegalArgumentException](
        PointsFile.written(directory, pointSources, writerBudget, Some(JudgmentPoints(BigDecimal(2), false, Some(TrapDraw(pointSources, 3)))))
      )
      Result.diff(Files.exists(directory.resolve(PointsFile.fileName)), false)(_ == _)
  }
