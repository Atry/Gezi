package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of a point's budget (`FamilyBudgets.pointBudget`):
  * every point's budget
  * is non-negative; the family's first point has the family's budget over
  * its point count n, and each later point that over plus what the point
  * before it left unused, so that a point after a cheap point has more than
  * the budget over n, and one after a point that used its whole budget has
  * exactly the budget over n; and the family's points together take no more
  * than the family's budget. Its purpose is to catch a supervisor that
  * shares one budget among the points in the order drawn (a point after an
  * expensive one would get nothing), one that drops what a cheap point left,
  * one that charges a point more than its own time, or one whose shares add
  * up to more than the family's budget.
  *
  * Each sample is a family's budget and, for each of its points, the share
  * of its budget the point spends; the laws read the budgets that
  * `pointBudget` gives as the family's wall time grows by each point's
  * spending.
  */
class PointBudgetLawTest extends GeneratedProperties:

  /** A family's budget in seconds and the share of its own budget each of
    * its points spends.
    */
  private final case class Family(budget: Double, spentShares: Vector[Double])

  /** A point's budget and the seconds it spent. */
  private final case class PointSpending(budget: Double, spent: Double)

  private def families(spentShare: Gen[Double]): Gen[Family] =
    for
      budget <- Gen.double(Range.linearFrac(0.001, 600.0))
      spentShares <- spentShare.list(Range.linear(1, 20))
    yield Family(budget, spentShares.toVector)

  /** A share in [0, 1], the whole budget drawn as often as any other. */
  private val withinBudget: Gen[Double] = Gen.choice1(Gen.constant(1.0), Gen.double(Range.linearFrac(0.0, 1.0)))

  /** Each point's budget and spending, the family's wall time before a point
    * being the sum of the earlier points' spending.
    */
  private def spendings(family: Family): Vector[PointSpending] =
    val pointCount = family.spentShares.size
    family.spentShares.zipWithIndex
      .foldLeft((0.0, Vector.empty[PointSpending])) { case ((familySeconds, gathered), (spentShare, index)) =>
        val budget = FamilyBudgets.pointBudget(family.budget, pointCount, index, familySeconds)
        val spent = spentShare * budget
        (familySeconds + spent, gathered :+ PointSpending(budget, spent))
      }
      ._2

  /** The rounding the laws allow: far below the poll interval. */
  private def tolerance(family: Family): Double = 1e-9 * family.budget

  private def share(family: Family): Double = family.budget / family.spentShares.size

  property("a point's budget is never negative, even after points that ran past theirs") {
    for family <- families(Gen.double(Range.linearFrac(0.0, 2.0))).forAll
    yield Result.all(spendings(family).map(spending => Result.assert(spending.budget >= 0.0).log(s"$spending")).toList)
  }

  property("the family's points together take no more than the family's budget") {
    for family <- families(withinBudget).forAll
    yield
      val total = spendings(family).map(_.spent).sum
      Result.assert(total <= family.budget + tolerance(family)).log(s"$total of ${family.budget}")
  }

  property("the first point has the budget over n, and each later one that plus what the point before it left") {
    for family <- families(withinBudget).forAll
    yield
      val found = spendings(family)
      val expected = share(family) +: found.init.map(before => share(family) + before.budget - before.spent)
      Result.all(
        found.zip(expected).map((spending, budget) => Result.assert((spending.budget - budget).abs <= tolerance(family)).log(s"$spending, expected $budget")).toList
      )
  }

  property("a point after a cheap point has more than the budget over n") {
    for family <- families(Gen.double(Range.linearFrac(0.0, 0.9))).forAll
    yield Result.all(spendings(family).drop(1).map(spending => Result.assert(spending.budget > share(family)).log(s"$spending").log(s"${share(family)}")).toList)
  }

  property("a point after a point that used its whole budget has exactly the budget over n") {
    for family <- families(withinBudget).forAll
    yield
      val found = spendings(family)
      Result.all(
        found
          .zip(family.spentShares)
          .zip(found.drop(1))
          .collect { case ((_, 1.0), after) => Result.assert((after.budget - share(family)).abs <= tolerance(family)).log(s"$after") }
          .toList
      )
  }
