package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of the family budget (`FamilyBudgets.budget`): a family with a
  * published reference time gets a budget within the floor and the cap that
  * does not shrink as the reference time grows, and a family with no time to go
  * by gets the cap. Its purpose is to catch a budget that escapes the floor or
  * the cap, one that shrinks for a slower reference, or a reader without an
  * anchor time cut short of the cap.
  */
class FamilyBudgetsLawTest extends GeneratedProperties:

  private val budgets = FamilyBudgets(20, 60, 600)

  private val referenceSeconds: Gen[Double] =
    Gen.double(Range.linearFrac(0.001, 60.0))

  property(
    "a family's budget lies within the floor and the cap and grows with its reference time"
  ) {
    for
      shorter <- referenceSeconds.forAll
      extra <- referenceSeconds.forAll
    yield
      val budget = budgets.budget(Some(shorter))
      Result.all(
        List(
          Result.assert(
            budget >= budgets.floorSeconds && budget <= budgets.capSeconds
          ),
          Result.assert(budgets.budget(Some(shorter + extra)) >= budget)
        )
      )
  }

  test("a family with no reference time gets the cap") {
    assertEquals(budgets.budget(None), budgets.capSeconds)
  }
