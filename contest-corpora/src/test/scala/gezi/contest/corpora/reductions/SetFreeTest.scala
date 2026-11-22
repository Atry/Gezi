package gezi.contest.corpora.reductions

/** The port of the test of `problems/set_free_dynamic` that does not
  * evaluate.
  */
class SetFreeDynamicTest extends gezi.generatedinputs.FailFastSuite:

  test("theNativeProgrammeOnHandWorkedCases") {
    Vector(
      (Vector(), Vector(1, 0), 0),
      (Vector(1, 0, 1, 1), Vector(0, 1, 1, 0), 3),
      (Vector(1, 1, 1), Vector(0, 0), 0),
      (Vector(0, 1, 0, 1), Vector(1, 0, 1, 0), 3)
    ).foreach((left, right, length) =>
      assertEquals((left, right, SetFreeDynamic.longestCommonSubsequence(left, right)), (left, right, length))
    )
  }

/** The port of the test of `problems/set_free_search` that does not
  * evaluate: its near miss's template.
  */
class SetFreeSearchTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  test("theNearMissIsNoRespellingOfDepthFirst") {
    val near = Encodings.deBruijn(SetFreeSearch.leavesOnlyTemplate(group.attractors))
    assert(Reduction.normalFormTerm(near))
    assert(near != group.attractors.attractorFunction("depth_first"))
  }

/** The ports of the tests of `problems/set_free_empty_search` that do not
  * evaluate.
  */
class SetFreeEmptySearchTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  test("theTemplateIsNormalAndNoRespellingOfDepthFirst") {
    val template = Encodings.deBruijn(SetFreeEmptySearch.emptyOnExhaustionTemplate(group.attractors))
    assert(Reduction.normalFormTerm(template))
    assert(template != group.attractors.attractorFunction("depth_first"))
  }

  test("anUnreachablePointHasTheEmptySnapshot") {
    Vector("set_free_empty_search_small_unreachable_direct", "set_free_empty_search_fourteen_unreachable_respelled")
      .foreach(point =>
        val problem = SetFreeEmptySearch.problems(group).find(_.point == point).get
        assertEquals((point, Reduction.snapshot(group.scott, problem)), (point, Vector.empty[String]))
      )
  }

object SetFreeEmptySearchTest:
  import gezi.frontend.Term
  import gezi.frontend.Term.*

  /** The program the test helper `searched/3` normalises:
    * `\e. (Y (Template e append)) Successors Goal (cons 0 nil)`, direct.
    */
  def searched(attractors: Attractors, height: Int, target: Int): Term =
    λ(empty =>
      attractors.fixpoint(
        SetFreeEmptySearch.emptyOnExhaustionTemplate(attractors)(empty)(attractors.functionSurface("append", Spelling.Direct))
      )(SetFreeSearch.successors(attractors, Spelling.Direct, height))(
        SetFreeSearch.goal(attractors, Spelling.Direct, target)
      )(SetFreeSearch.stack(attractors, Spelling.Direct))
    )

/** The port of the test of `problems/set_free_list_laws` that does not
  * evaluate.
  */
class SetFreeListLawsTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  test("filterIsANormalFormOtherThanMap") {
    val filter = group.attractors.attractorFunction("filter")
    assert(Reduction.normalFormTerm(filter))
    assert(filter != group.attractors.attractorFunction("map"))
  }

/** The ports of the tests of `problems/set_free_premises` that do not
  * evaluate.
  */
class SetFreePremisesTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  private def expected(point: String): Expected =
    SetFreePremises.problems(group).find(_.point == point).get.expected

  test("theNearMissesAnswerAnotherNumeral") {
    val numeral = expected("set_free_rebuild_small_direct")
    assert(numeral != expected("set_free_rebuild_small_near_miss"))
    assert(numeral != expected("set_free_unit_small_near_miss"))
  }

  test("theLawsAnswerTheNumeralTheyWereGiven") {
    Vector("small", "medium", "large").foreach(size =>
      val numeral = expected(s"set_free_rebuild_${size}_direct")
      Vector("involution", "unit").foreach(law =>
        val point = s"set_free_${law}_${size}_direct"
        assertEquals((point, expected(point)), (point, numeral))
      )
    )
  }

/** The port of the test of `problems/set_free_scope` that does not
  * evaluate.
  */
class SetFreeScopeTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val group: ReductionGroup = ReductionTesting.group

  test("theNearMissIsNoCanonicalNumeral") {
    SetFreeScope.problems(group).find(_.point == "set_free_scope_small_near_miss").get.expected match
      case Expected.One(tree) =>
        assert(tree != Scott.leaf("zero"))
        assertEquals(tree.name, "even")
      case other => fail(s"not one tree: $other")
  }
