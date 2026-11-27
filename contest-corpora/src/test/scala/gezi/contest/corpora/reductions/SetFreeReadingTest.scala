package gezi.contest.corpora.reductions

import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ParallelSetReading
import gezi.weakhead.ReadingState
import gezi.contest.corpora.oldcorpora.BetaEtaNormalisation
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term.λ

/** The test of the set-free families' `.plt` files that decodes the small
  * points: every tree the Scott decoder reads under tabling(weak_head), as
  * often as it is read, is exactly the problem's one expected tree (`findall`
  * of `decoded/4` against `[Expected]`), within `Decoding.limit`.
  */
object SetFreeDecoding:

  def assertDecodesToSnapshot(
      suite: munit.FunSuite,
      problems: Vector[ReductionProblem],
      points: Vector[String]
  ): Unit =
    points.foreach(point =>
      val problem = SetReading.problem(problems, point)
      val trees = Reduction.decodedTrees(
        Mode.TablingWeakHead,
        problem.program,
        problem.typeName,
        Decoding.limit
      ) match
        case Some(found) => found.map(Scott.fromDecoded)
        case None        =>
          throw AssertionError(
            s"$point: a decoding ran past ${Decoding.limit} steps"
          )
      problem.expected match
        case Expected.One(tree) =>
          suite.assertEquals((point, trees), (point, Vector(tree)))
        case other => suite.fail(s"$point expects $other")
    )

class SetFreeDynamicReadingTest extends gezi.generatedinputs.FailFastSuite:

  /** The family's problems, read once, forced before the test with the group
    * they read from (`sharedFixtures`).
    */
  private lazy val problems = SetFreeDynamic.problems(ReductionTesting.group)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => ReductionTesting.group, _ => problems)

  test("theSmallPointsDecodeToTheirSnapshots") {
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      problems,
      Vector(
        "set_free_common_subsequence_small_direct",
        "set_free_common_subsequence_small_respelled",
        "set_free_common_subsequence_small_near_miss"
      )
    )
  }

class SetFreeListLawsReadingTest extends gezi.generatedinputs.FailFastSuite:
  test("theSmallPointsDecodeToTheirSnapshots") {
    val problems = SetFreeListLaws.problems(ReductionTesting.group)
    Vector(
      "set_free_list_law_small_direct" -> "true",
      "set_free_list_law_small_respelled" -> "true",
      "set_free_list_law_small_near_miss" -> "false"
    ).foreach((point, verdict) =>
      assertEquals(
        (point, SetReading.problem(problems, point).expected),
        (point, Expected.One(Scott.leaf(verdict)))
      )
    )
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      problems,
      Vector(
        "set_free_list_law_small_direct",
        "set_free_list_law_small_respelled",
        "set_free_list_law_small_near_miss"
      )
    )
  }

class SetFreePremisesReadingTest extends gezi.generatedinputs.FailFastSuite:
  test("theSmallPointsDecodeToTheirSnapshots") {
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      SetFreePremises.problems(ReductionTesting.group),
      Vector(
        "set_free_rebuild_small_direct",
        "set_free_rebuild_small_respelled",
        "set_free_rebuild_small_near_miss",
        "set_free_involution_small_direct",
        "set_free_involution_small_respelled",
        "set_free_unit_small_direct",
        "set_free_unit_small_respelled",
        "set_free_unit_small_near_miss"
      )
    )
  }

class SetFreeScopeReadingTest extends gezi.generatedinputs.FailFastSuite:
  test("theSmallPointsDecodeToTheirSnapshots") {
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      SetFreeScope.problems(ReductionTesting.group),
      Vector(
        "set_free_scope_small_direct",
        "set_free_scope_small_respelled",
        "set_free_scope_small_near_miss"
      )
    )
  }

class SetFreeSearchReadingTest extends gezi.generatedinputs.FailFastSuite:
  test("theSmallPointsDecodeToTheirSnapshots") {
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      SetFreeSearch.problems(ReductionTesting.group),
      Vector(
        "set_free_ladder_small_reachable_direct",
        "set_free_ladder_small_reachable_respelled",
        "set_free_ladder_small_unreachable_direct",
        "set_free_ladder_small_unreachable_respelled",
        "set_free_ladder_small_near_miss"
      )
    )
  }

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_set_free_empty_search.plt`) that read
  * normal forms or decode. `normalised/3` is the old corpora's normaliser
  * (`oldcorpora.BetaEtaNormalisation`), whose fuel is a count of beta
  * contractions in the Prolog as here, so the Prolog's fuels, 10,000,000 and
  * 1,000, stand unchanged.
  */
class SetFreeEmptySearchReadingTest extends gezi.generatedinputs.FailFastSuite:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts
  private val group = ReductionTesting.group
  private val attractors = group.attractors

  private def term(program: gezi.frontend.Term): DeBruijnTerm =
    program.deBruijnTerm(Map.empty)

  test("theSearchAnswersItsEmptyParameterExactlyWhenUnreachable") {
    Vector((2, 2), (2, 1), (2, 3), (3, 4)).foreach((height, target) =>
      val normal = BetaEtaNormalisation.normalised(
        term(SetFreeEmptySearchTest.searched(attractors, height, target)),
        10000000
      )
      val expected =
        if target <= height then
          term(λ(_ => attractors.attractorSurface("true", Spelling.Direct)))
        else term(λ(empty => empty))
      assertEquals((height, target, normal), (height, target, Some(expected)))
    )
  }

  test("theEmptyTermPutsItsArgumentAtTheHead") {
    val normal = BetaEtaNormalisation.normalised(
      term(λ(kept => SetFreeEmptySearch.emptyTerm(attractors)(λ(_ => kept)))),
      1000
    )
    assertEquals(normal, Some(term(λ(variable => variable))))
  }

  test("theSmallReachablePointsDecodeToTrue") {
    SetFreeDecoding.assertDecodesToSnapshot(
      this,
      SetFreeEmptySearch.problems(group),
      Vector(
        "set_free_empty_search_small_reachable_direct",
        "set_free_empty_search_small_reachable_respelled"
      )
    )
  }

  /** tabling(weak_head) reads no normal form of the small unreachable point:
    * the reading stops, within 2,000,000 steps (`Reading.budgetSteps(1)`) and
    * the state's table space, before a first normal form, the program having
    * none. Which bound it stops at is the reader's cost, not the law: on
    * 2026-11-18 it was the table space, after 0.23 s.
    */
  test("tablingWeakHeadReadsNoNormalFormOfASmallUnreachablePoint") {
    val problem = SetReading.problem(
      SetFreeEmptySearch.problems(group),
      "set_free_empty_search_small_unreachable_direct"
    )
    val root = Reduction.programRoot(problem.program)
    val first = NormalForms
      .normalForm(Mode.TablingWeakHead, ParallelSetReading.Whole, root)
      .pull
      .result(
        ReadingState.fresh(
          gezi.weakhead.Reading.budgetSteps(1),
          gezi.weakhead.ReadingConfiguration.withoutFacts
        )
      )
    first match
      case Computed.Stopped(_)     => ()
      case Computed.Done(found, _) =>
        fail(s"tabling(weak_head) read a normal form or finished: $found")
  }
