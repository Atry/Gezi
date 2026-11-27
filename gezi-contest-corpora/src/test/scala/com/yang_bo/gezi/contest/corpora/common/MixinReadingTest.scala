package com.yang_bo.gezi.contest.corpora.common

import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.Reading
import com.yang_bo.gezi.weakhead.oldcorpora.ConstructorTree
import com.yang_bo.gezi.contest.corpora.claims.ClaimAnswer
import com.yang_bo.gezi.contest.corpora.claims.ContestClaims
import com.yang_bo.gezi.contest.corpora.claims.Ending
import com.yang_bo.gezi.contest.corpora.claims.Template
import com.yang_bo.gezi.contest.corpora.reductions.Reduction
import com.yang_bo.gezi.contest.corpora.merges.MixinDatalog.ProgramKind
import com.yang_bo.gezi.contest.corpora.merges.MixinDatalog.ProgramShape
import com.yang_bo.gezi.contest.corpora.merges.ProgramFields
import com.yang_bo.gezi.frontend.Term

/** The judge's ending of a point's claim and the Booleans a search decodes to,
  * the helpers of the mixin families' `.plt` files.
  *
  * BUDGETS: the claims were read within 10 seconds as inferences
  * (`budget_inferences(10, I)`, 300,000,000); here the same 10 seconds are
  * steps, `Reading.budgetSteps(10)`, 20,000,000. The Prolog decoding
  * (`decoded/4` under findall) had no budget; here it gets the same 20,000,000
  * steps, the intent being a bound the small searches never reach, so a search
  * the budget stops fails its test.
  */
object MixinReading:

  val limit: Long = Reading.budgetSteps(10)

  /** The ending of the point's claim of the template under the mode, its test
    * `claim_test/3` over every group's points.
    */
  def claimEnding(point: String, template: Template, mode: Mode): Ending =
    val test =
      HardCorpusFixture.corpus.claimsGroup.claims.claimTest(point, template)
    ContestClaims.claimsAnswered(mode, Vector(test), limit) match
      case Vector(ClaimAnswer(ending, _)) => ending
      case answers                        =>
        throw AssertionError(s"one test gave ${answers.size} answers")

  /** `search_answers/2`, `tuple_answers/5`: the distinct Booleans the program
    * decodes to under tabling(weak_head), as constructor trees, sorted by name.
    */
  def booleanAnswers(program: Term): Vector[ConstructorTree] =
    Reduction.decodedTrees(
      Mode.TablingWeakHead,
      program,
      "boolean",
      limit
    ) match
      case Some(trees) =>
        trees.distinct.sortBy {
          case ConstructorTree.Constructor(name, _) => name
          case ConstructorTree.IllFormed            => ""
        }
      case None => throw AssertionError(s"a decoding ran past $limit steps")

  def booleanTree(name: String): ConstructorTree =
    ConstructorTree.Constructor(name, Vector.empty)

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_mixin_claims.plt`), which read the judge
  * and the Scott decoder.
  */
class ContestMixinClaimsReadingTest extends HardCorpusSuite:
  import MixinReading.*

  test("theSmallGraphClaimsSucceed") {
    Vector(
      "mixin_ring_three_reaches" -> Mode.TablingWeakHead,
      "mixin_direct_first_reaches" -> Mode.TablingWeakHead,
      "mixin_diamond_two_hop" -> Mode.TablingWeakHead
    ).foreach((point, mode) =>
      assertEquals(
        (point, claimEnding(point, Template.BooleanTemplate(true), mode)),
        (point, Ending.Succeeded)
      )
    )
  }

  test("theSmallSearchesHaveTheirAnswers") {
    val claims = HardCorpusFixture.corpus.mixinClaims
    Vector(
      (
        "three_is_a_subset_sum_of_three",
        claims.subsetSurface(Vector(3), 3),
        Vector("false", "true")
      ),
      (
        "five_is_no_subset_sum_of_three",
        claims.subsetSurface(Vector(3), 5),
        Vector("false")
      ),
      (
        "a_and_a_share_one_symbol",
        claims.commonSubsequenceSurface(Vector('a'), Vector('a'), 1),
        Vector("false", "true")
      ),
      (
        "a_and_b_share_none",
        claims.commonSubsequenceSurface(Vector('a'), Vector('b'), 1),
        Vector("false")
      )
    ).foreach((name, program, expected) =>
      assertEquals(
        (name, booleanAnswers(program)),
        (name, expected.map(booleanTree))
      )
    )
  }

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_mixin_datalog.plt`) that read the judge
  * and the Scott decoder.
  */
class ContestMixinDatalogReadingTest extends HardCorpusSuite:
  import MixinReading.*

  test("theFiniteProgramsDeriveTheReferenceRelations") {
    val datalog = HardCorpusFixture.corpus.mixinDatalog
    Vector(
      ProgramKind.Composition -> "composed",
      ProgramKind.ThreeWay -> "chain",
      ProgramKind.Intersection -> "multi",
      ProgramKind.ConstantJoin -> "constant_join",
      ProgramKind.Closure(ProgramShape.AbcChain) -> "path"
    ).foreach((kind, head) =>
      val program = datalog.program(ProgramFields.field(kind))
      for
        first <- Vector("a", "b", "c")
        second <- Vector("a", "b", "c")
      do
        val expected =
          if datalog.referenceHolds(program, head, first, second) then
            Vector(booleanTree("true"))
          else Vector.empty
        assertEquals(
          (
            head,
            first,
            second,
            booleanAnswers(datalog.datalogSurface(program, head, first, second))
          ),
          (head, first, second, expected)
        )
    )
  }

  test("theSmallCyclicClaimsSucceed") {
    Vector(
      "mixin_datalog_cycle_path_b_a",
      "mixin_datalog_symmetric_reach_c_a",
      "mixin_datalog_symmetric_reach_a_a"
    ).foreach(point =>
      assertEquals(
        (
          point,
          claimEnding(
            point,
            Template.BooleanTemplate(true),
            Mode.TablingWeakHead
          )
        ),
        (point, Ending.Succeeded)
      )
    )
  }

/** The test of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_mixin_traps.plt`) that reads the judge:
  * the small traps fail, finitely, for both Booleans.
  */
class ContestMixinTrapsReadingTest extends HardCorpusSuite:
  import MixinReading.*

  test("theSmallTrapsAreNotAnswered") {
    for
      (point, mode) <- Vector(
        "mixin_diamond_two_hop_self" -> Mode.TablingWeakHead,
        "mixin_ring_three_misses" -> Mode.TablingWeakHead
      )
      template <- Vector(
        Template.BooleanTemplate(true),
        Template.BooleanTemplate(false)
      )
    do
      assertEquals(
        (point, template, claimEnding(point, template, mode)),
        (point, template, Ending.Failed)
      )
  }
