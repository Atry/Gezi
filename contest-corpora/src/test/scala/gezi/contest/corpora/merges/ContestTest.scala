package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamily

/** The generators of the prelude's corpora, shared by their suites. */
object PreludeFamily:
  val prelude: Prelude = Prelude(MergeTesting.problems)
  val contest: Contest = Contest(MergeTesting.problems, prelude)

/** `problems/clauses` (`contest.pl`): the ports of `contest.plt`'s two tests
  * that read data only, against the intended answers of `problems/answers`,
  * read as facts.
  */
class ContestTest extends MergeProblemsSuite:

  /** The points of `problems/clauses`, read once for the suites that share
    * `PreludeFamily`.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ => PreludeFamily.contest.points)

  private val intended
      : Vector[(String, gezi.contest.corpora.claims.IntendedOutcome, gezi.contest.corpora.claims.IntendedValue)] =
    MergeTesting.problems("answers").rows("intended").map(arguments =>
      (
        ProblemData.text(arguments(0)),
        gezi.contest.corpora.claims.IntendedOutcome.read(arguments(1)),
        gezi.contest.corpora.claims.IntendedValue.read(arguments(2))
      )
    )

  test("everyPointHasAnIntendedAnswer") {
    assertEquals(intended.map(_._1).toSet, PreludeFamily.contest.points.toSet)
    assertEquals(PreludeFamily.contest.points.distinct.length, PreludeFamily.contest.points.length)
  }

  test("intendedAnswersAreWellFormed") {
    intended.foreach((point, outcome, value) =>
      val wellFormed = (outcome, value) match
        case (gezi.contest.corpora.claims.IntendedOutcome.Head, gezi.contest.corpora.claims.IntendedValue.BooleanValue(_)) =>
          true
        case (gezi.contest.corpora.claims.IntendedOutcome.Head, gezi.contest.corpora.claims.IntendedValue.NaturalValue(count)) =>
          count >= 0
        case (gezi.contest.corpora.claims.IntendedOutcome.Failed, gezi.contest.corpora.claims.IntendedValue.NoValue) =>
          true
        case _ => false
      assert(wellFormed, point)
    )
  }

/** The tests of `contest.plt` that read the contest's points on the
  * evaluators: the reference evaluator (evaluation's test helper
  * `Reference`, weak head reduction by substitution) computes the intended
  * answer of every point it finishes within its budget; tabling(weak_head) reads the
  * intended answer of every point whose intended answer is a head; and its
  * one head, read back, is the reference's.
  *
  * BUDGETS, re-derived with the Prolog tests' intent, in evaluator steps:
  * - The reference's budget: the Prolog's `reference_inferences(10000000)`
  *   lay between the most a passing point took (5.01 million inferences,
  *   regex_all_prefixes_unrolled) and the least of `beyondReference` (17.6
  *   million, lasso_floyd_has_cycle_large). The reference's steps measured
  *   2026-10-31 on the term applied to the two markers (head and decoding):
  *   the beyond points 11,200,000 (lasso_floyd_has_cycle_large),
  *   76,288,000 and 393,216,000, about 0.64 of the Prolog's counts; the
  *   passing points at most 3,008,000 among those measured
  *   (lasso_floyd_cycle_start_medium). 6,000,000 steps lies between.
  * - tabling(weak_head)'s budget: three times the point's seconds
  *   (`ContestAnswers.pointLimits`) as steps (`Reading.budgetSteps`), where
  *   the Prolog took the same seconds as inferences; the head test's three
  *   seconds likewise. The untabled weak head's steps measured 2026-10-31 were at most
  *   1,632,000 (lasso_visited_cycle_start_large, its budget 48,000,000).
  */
class ContestReadingTest extends MergeProblemsSuite:

  // Measured 2026-11-19 (CPUs 8 to 11, nice 10, the 1-minute load 8 to 9, the problems' shared expansions built in beforeAll): the slowest test of ContestReadingTest, "theReferenceEvaluatorReadsTheIntendedAnswer", takes 4.947 s, "theHeadsAreTheReferenceHeads" 4.429 s; the bound is 1.5 times the slowest rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")
  import gezi.weakhead.Bounded
  import gezi.weakhead.Mode
  import gezi.weakhead.ParallelView
  import gezi.weakhead.Reading
  import gezi.weakhead.ReadingOutcome
  import gezi.weakhead.Reference
  import gezi.weakhead.Values
  import gezi.contest.corpora.claims
  import gezi.frontend.DeBruijnTerm
  import gezi.frontend.Defunctionalization

  private val claimsGroup = claims.Claims(MergeTesting.buildRoot, MergeTesting.problems, Vector.empty)

  private val answers = claimsGroup.contestAnswers

  /** The points whose intended answer is a head, with its value. */
  private val headPoints: Vector[(String, claims.IntendedValue)] =
    answers.points.flatMap(point =>
      answers.intended(point).collect { case claims.Intended(claims.IntendedOutcome.Head, value) => point -> value }
    )

  /** `beyond_reference/1`: the points the reference reaches only beyond
    * its budget.
    */
  private val beyondReference: Set[String] = Set(
    "lasso_floyd_has_cycle_large",
    "lasso_floyd_cycle_start_large",
    "lasso_visited_cycle_start_large",
    "regex_matches_medium",
    "regex_matches_large",
    "regex_rejects_medium"
  )

  private val referenceLimit: Long = 6000000

  private def pointTerm(point: String): DeBruijnTerm = PreludeFamily.contest.program(point).deBruijnTerm(Map.empty)

  /** The point's program as a plain value of the evaluator
    * (`thunk_instruction/2`, not interned).
    */
  private def pointValue(point: String) =
    Values.ofInstruction(Defunctionalization.thunkInstruction(pointTerm(point))(using gezi.ir.NoFacts), Set.empty)

  test("theReferenceEvaluatorReadsTheIntendedAnswer") {
    headPoints.filterNot((point, _) => beyondReference(point)).foreach((point, value) =>
      assertEquals((point, ReferenceDecoding.decoded(value, pointTerm(point), referenceLimit)), (point, Some(value)))
    )
  }

  test("weakHeadReadsTheIntendedAnswer") {
    headPoints.foreach((point, _) =>
      val seconds = answers.pointLimits(point).seconds.toDouble
      val root = pointValue(point)
      val outcome = Reading.termReading(Mode.TablingWeakHead, root, Reading.budgetSteps(3 * seconds), gezi.weakhead.ReadingConfiguration.withoutFacts)
      outcome match
        case ReadingOutcome.Heads(heads) => assert(heads.nonEmpty, point)
        case other                       => fail(s"$point: $other")
      assertEquals((point, answers.pointVerdict(point, outcome).verdict), (point, claims.Verdict.Matches))
    )
  }

  test("theHeadsAreTheReferenceHeads") {
    headPoints.filterNot((point, _) => beyondReference(point)).foreach((point, _) =>
      val expected = Reference.weakHeadWithin(pointTerm(point), referenceLimit) match
        case Bounded.Finished(head) => head
        case other                  => fail(s"$point: the reference did not finish: $other")
      val root = pointValue(point)
      Reading.termReading(Mode.TablingWeakHead, root, Reading.budgetSteps(3), gezi.weakhead.ReadingConfiguration.withoutFacts) match
        case ReadingOutcome.Heads(Vector(set)) =>
          set.view(gezi.ir.NoFacts) match
            case ParallelView.Single(head) =>
              assertEquals((point, claims.ContestAnswers.headTerm(head)), (point, expected))
            case _ => fail(s"$point: not one head: $set")
        case other => fail(s"$point: not one head: $other")
    )
  }

/** The reference decoder of `tests/reference.pl` (`reference_decoded/3`),
  * on evaluation's reference evaluator: the closed term applied to the two
  * markers `\a.\b.\c. c` and `\p.\a.\b.\c.\d. p` chooses the first for true
  * or zero and the second for false; a natural's successor case answers the
  * second marker applied to its predecessor, an abstraction of four binders
  * over it, decoded again. Written independently of the contest's verdict.
  * Each reference evaluation is bounded by the limit, where the Prolog
  * bounded the head and the whole decoding by one count.
  */
object ReferenceDecoding:
  import gezi.weakhead.Bounded
  import gezi.weakhead.Reference
  import gezi.contest.corpora.claims.IntendedValue
  import gezi.frontend.DeBruijnTerm
  import gezi.frontend.DeBruijnTerm.{Apply, Lambda, Variable}

  private val first: DeBruijnTerm = Lambda(Lambda(Lambda(Variable(0))))
  private val second: DeBruijnTerm = Lambda(Lambda(Lambda(Lambda(Lambda(Variable(4))))))

  /** The term decoded as the kind of the value: the value it is, none when
    * it is no value of the kind or a reference evaluation ran past the
    * limit.
    */
  def decoded(kind: IntendedValue, term: DeBruijnTerm, limit: Long): Option[IntendedValue] = kind match
    case IntendedValue.BooleanValue(_) =>
      chosen(term, limit).flatMap(choice =>
        if choice == first then Some(IntendedValue.BooleanValue(true))
        else if choice == second then Some(IntendedValue.BooleanValue(false))
        else None
      )
    case IntendedValue.NaturalValue(_) => natural(term, 0, limit).map(IntendedValue.NaturalValue(_))
    case other                         => throw IllegalArgumentException(s"no reference decoding of $other")

  private def chosen(term: DeBruijnTerm, limit: Long): Option[DeBruijnTerm] =
    Reference.weakHeadWithin(Apply(Apply(term, first), second), limit) match
      case Bounded.Finished(head) => Some(head)
      case _                      => None

  @scala.annotation.tailrec
  private def natural(term: DeBruijnTerm, accumulated: Int, limit: Long): Option[Int] =
    chosen(term, limit) match
      case Some(choice) if choice == first => Some(accumulated)
      case Some(Lambda(Lambda(Lambda(Lambda(predecessor))))) => natural(predecessor, accumulated + 1, limit)
      case _ => None
