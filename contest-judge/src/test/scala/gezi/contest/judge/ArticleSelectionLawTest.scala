package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties

/** The law of the article re-read's selection (`ArticleRereading.selected`): on
  * generated families of evaluation and judgment points with generated
  * outcomes, the selection holds every evaluation point answered false, and
  * besides them at most one point of each family, an evaluation point that
  * answered (success, false or incomplete); exactly one when the family has an
  * answered evaluation point and none answered false; each point once, in the
  * families' order. Its purpose is to catch a selection that misses a false
  * answer, checks a judgment point or a point that gave no answer, or draws
  * more than one point of a family.
  */
class ArticleSelectionLawTest extends GeneratedProperties:

  private val program: DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** The program's instruction, which a point holds. */
  private val programInstruction: Configured[NoFacts.type] =
    gezi.frontend.Defunctionalization.thunkInstruction(program)(using
      gezi.ir.NoFacts
    )

  private val evaluationOutcomes: Vector[Outcome] =
    Vector(
      Outcome.Success,
      Outcome.False,
      Outcome.Incomplete,
      Outcome.NoAnswer,
      Outcome.Stopped
    )

  private val judgmentOutcomes: Vector[Outcome] = Vector(
    Outcome.Proved,
    Outcome.False,
    Outcome.Unknown,
    Outcome.Refuted,
    Outcome.Stopped
  )

  /** A point of the family and its outcome: an evaluation point or a judgment
    * point, its outcome one its kind can have.
    */
  private def pointRead(family: String, number: Int): Gen[(Point, Outcome)] =
    for
      evaluation <- Gen.boolean
      outcomes = if evaluation then evaluationOutcomes else judgmentOutcomes
      outcome <- Gen.element1(outcomes.head, outcomes.tail*)
    yield
      val question = if evaluation then Question.Evaluation(Set(program))
      else Question.Judgment(programInstruction, true)
      (
        Point(
          s"$family-$number",
          "test",
          family,
          BigDecimal(1),
          gezi.frontend.ExchangeText.line(programInstruction),
          question
        ),
        outcome
      )

  private val familiesRead: Gen[Vector[(String, Vector[(Point, Outcome)])]] =
    Gen
      .int(Range.linear(1, 4))
      .flatMap(familyCount =>
        (0 until familyCount).foldLeft(
          Gen.constant(Vector.empty[(String, Vector[(Point, Outcome)])])
        ) { (gathered, familyNumber) =>
          val family = s"family$familyNumber"
          for
            before <- gathered
            size <- Gen.int(Range.linear(0, 6))
            points <- (0 until size).foldLeft(
              Gen.constant(Vector.empty[(Point, Outcome)])
            )((pointsSoFar, number) =>
              for
                earlier <- pointsSoFar
                next <- pointRead(family, number)
              yield earlier :+ next
            )
          yield before :+ (family -> points)
        }
      )

  property(
    "the selection is the false evaluation points and at most one answered evaluation point per family"
  ) {
    for
      families <- familiesRead.forAll
      seed <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .forAll
    yield
      val rows = families.flatMap((family, points) =>
        points.map((point, outcome) =>
          Row(
            point.name,
            "entry",
            family,
            "-",
            outcome.written,
            Share.none,
            0,
            0,
            "any",
            false,
            Vector.empty
          )
        )
      )
      val selected = ArticleRereading.selected(
        families.map((family, points) => family -> points.map(_._1)),
        rows,
        seed
      )
      val outcomeOf = families
        .flatMap(_._2)
        .map((point, outcome) => point.name -> outcome)
        .toMap
      def evaluation(point: Point) =
        point.question.isInstanceOf[Question.Evaluation]
      val falsely = families.flatMap((family, points) =>
        points.collect {
          case (point, Outcome.False) if evaluation(point) => (family, point)
        }
      )
      val answered = Set(Outcome.Success, Outcome.False, Outcome.Incomplete)
      val perFamily = families.map((family, points) =>
        val chosen = selected.filter(_._1 == family).map(_._2)
        val drawn =
          chosen.filterNot(point => outcomeOf(point.name) == Outcome.False)
        val anyAnswered = points.exists((point, outcome) =>
          evaluation(point) && answered.contains(outcome)
        )
        val anyFalse = points.exists((point, outcome) =>
          evaluation(point) && outcome == Outcome.False
        )
        drawn.size <= 1 && (!anyAnswered || anyFalse || drawn.size == 1)
      )
      Result
        .all(
          List(
            Result.assert(falsely.forall(selected.contains)),
            Result.assert(
              selected.forall((_, point) =>
                evaluation(point) && answered.contains(outcomeOf(point.name))
              )
            ),
            Result.assert(perFamily.forall(identity)),
            Result.diff(selected.distinct, selected)(_ == _),
            Result.diff(
              selected,
              families
                .flatMap((family, points) => points.map(family -> _._1))
                .filter(selected.contains)
            )(_ == _)
          )
        )
        .log(selected.map(_._2.name).mkString(", "))
  }
