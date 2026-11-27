package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.claims.Template
import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_binary.pl`; its data are
  * `problems/merge_binary`): the product of two Scott binary naturals compared
  * with a claimed one, by the shift and add multiplication of `MergeDynamic`,
  * with no choice. The table of points is read from the family's directory,
  * `gezi/problems/merge_binary`.
  */
final class MergeBinary(problems: ProblemFamilies, dynamic: MergeDynamic):

  private val file = problems("merge_binary")

  /** The Church Boolean of `left * right == claimed` (`product_term/4`). */
  def productTerm(left: BigInt, right: BigInt, claimed: BigInt): ProblemTerm =
    dynamic.withArithmetic(names =>
      λ(zero =>
        λ(times =>
          names.equality(times(dynamic.binary(left))(dynamic.binary(right)))(
            dynamic.binary(claimed)
          )
        )(
          dynamic.timesFunction(names.plus, zero)
        )
      )(dynamic.binary(0))
    )

  /** The points, each with its factors and the bits flipped in its claim, 0 for
    * the true product (`product_point/4`).
    */
  val points: Vector[(String, BigInt, BigInt, BigInt)] =
    file
      .rows("product_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          ProblemData.integer(arguments(1)),
          ProblemData.integer(arguments(2)),
          ProblemData.integer(arguments(3))
        )
      )

  /** The point's factors and its claimed product (`claimed/4`). */
  def claimed(point: String): (BigInt, BigInt, BigInt) =
    val (_, left, right, flipped) = points
      .find(_._1 == point)
      .getOrElse(
        throw IllegalArgumentException(
          s"$point is no point of contest_merge_binary"
        )
      )
    (left, right, (left * right) ^ flipped)

  /** The point's program. */
  def program(point: String): ProblemTerm =
    val (left, right, claimedProduct) = claimed(point)
    productTerm(left, right, claimedProduct)

  /** The intended value of the point's program (`product_value/2`). */
  def value(point: String): Template =
    ClaimFact.boolean(points.find(_._1 == point).exists(_._4 == 0))

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((point, _, _, _) =>
      val (left, right, claimedProduct) = claimed(point)
      val template = value(point)
      ClaimFact.headPoint(point, template) :+ ScoredFiniteHead(
        point,
        Vector(template),
        s"$left * $right = ${left * right}, so the product == $claimedProduct is ${ClaimFact.text(template)}: the multiplication is a finite recursion on the bits of finite binary numerals, each step one binary addition, and the binary equality compares bit by bit, so the check reaches the Church Boolean of the equation in finitely many head reductions"
      )
    )
