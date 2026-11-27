package com.yang_bo.gezi.contest.corpora.common

import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.Reading
import com.yang_bo.gezi.contest.corpora.claims.ContestClaims
import com.yang_bo.gezi.contest.corpora.claims.Ending
import com.yang_bo.gezi.contest.corpora.claims.OpenTest
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.λ

/** The part of the port of `gezi/tests/surface_merge.plt` that does not read
  * the deleted Prolog surface: the judge answers a test whose term is a choice
  * of lambda terms.
  *
  * THE BUDGET of a judged ending: the Prolog gave ten seconds as an inference
  * count (`budget_inferences(10, I)`); here the same ten seconds are a budget
  * of evaluator steps, `Reading.budgetSteps(10)`.
  */
class SurfaceMergeTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  /** `ending(Test, Ending)`: the judge's ending of the test, a suite of its
    * own, within ten seconds as steps.
    */
  private def ending(test: OpenTest): Ending =
    ContestClaims.claimsAnswered(
      Mode.TablingWeakHead,
      Vector(test),
      Reading.budgetSteps(10)
    ) match
      case Vector(answer) => answer.ending
      case answers        => fail(s"one test gave ${answers.size} answers")

  test("aChoiceOfLambdaTermsIsAnswered") {
    val chosen = ending(
      OpenTest(
        1,
        free =>
          λ(a => Term.choice(λ(t => λ(_ => t)), λ(_ => λ(f => f)))(a)(free(0)))
      )
    )
    assertEquals(chosen, Ending.Succeeded)
  }
