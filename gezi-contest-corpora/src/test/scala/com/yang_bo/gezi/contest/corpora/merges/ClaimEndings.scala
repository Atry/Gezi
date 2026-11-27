package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.Reading
import com.yang_bo.gezi.contest.corpora.claims.ContestClaims
import com.yang_bo.gezi.contest.corpora.claims.Ending
import com.yang_bo.gezi.contest.corpora.claims.OpenTest
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.λ

/** The judge's ending of a program whose value is a Church Boolean, the helper
  * `true_ending/2` of the merge family's `.plt` files: the test `\a. Term a _`,
  * with one free variable, posed to the judge as a suite of its own
  * (`claims_answered/4`).
  *
  * The budget: the Prolog helper gave 20 seconds as an inference count
  * (`budget_inferences(20, I)`, 600,000,000 inferences at its 30 million a
  * second); here the same 20 seconds are a budget of evaluator steps,
  * `Reading.budgetSteps(20)`, 40,000,000 steps. The intent is a bound none of
  * the small programs reaches: every assertion is `Succeeded` or `Failed`,
  * never `Stopped`, so a program the budget stops fails its test.
  */
object ClaimEndings:

  /** The steps of the budget, `Reading.budgetSteps(20)`. */
  val limit: Long = Reading.budgetSteps(20)

  /** The ending of `\a. Term a _` under the mode. */
  def trueEnding(mode: Mode, term: Term): Ending =
    ending(mode, OpenTest(1, free => λ(argument => term(argument)(free(0)))))

  /** The ending of the test under the mode, a suite of its own. */
  def ending(mode: Mode, test: OpenTest): Ending =
    ContestClaims.claimsAnswered(mode, Vector(test), limit) match
      case Vector(answer) => answer.ending
      case answers        =>
        throw AssertionError(s"one test gave ${answers.size} answers")
