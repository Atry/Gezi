package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.claims.Template
import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_merge_twins.pl`; its data are
  * `problems/merge_twins`): each twin asks
  * its original's question (grid paths, Fibonacci, the binary product) at the
  * same size with the twin arithmetic of `MergeDynamic` and twin bodies. The
  * twin bodies and the table of twins are read from the family's directory,
  * `gezi/problems/merge_twins`.
  */
final class MergeTwins(
    problems: ProblemFamilies,
    dynamic: MergeDynamic,
    fibonacci: MergeFibonacci,
    binary: MergeBinary
):
  import MergeTwins.TwinProblem

  private val file = problems("merge_twins")

  /** The twins, each with its problem and its original (`twin/3`), the
    * problem a constructor of problems/merge_twins/problem read by its
    * position (`ProblemData.alternative`).
    */
  val twins: Vector[(String, TwinProblem, String)] =
    file.rows("twin").map(arguments =>
      (
        ProblemData.text(arguments(1)),
        ProblemData.alternative(arguments(0), TwinProblem.values.size) match
          case (position, Vector()) => TwinProblem.fromOrdinal(position)
          case (_, fields)          => throw IllegalArgumentException(s"a problem of contest_merge_twins has ${fields.size} fields"),
        ProblemData.text(arguments(2))
      )
    )

  /** The twin's program on its original's data (`twin_term/2`). */
  def program(twin: String): Term =
    twins.find(_._1 == twin) match
      case Some((_, TwinProblem.Grid, original)) =>
        val (_, size, claimed) = dynamic.gridPoints
          .find(_._1 == original)
          .getOrElse(throw IllegalArgumentException(s"$original is no grid point"))
        twinGridTerm(size, claimed)
      case Some((_, TwinProblem.Fibonacci, original)) =>
        val (n, claimed) = fibonacci.point(original)
        twinFibonacciTerm(n, claimed)
      case Some((_, TwinProblem.Product, original)) =>
        val (left, right, claimed) = binary.claimed(original)
        twinProductTerm(left, right, claimed)
      case None => throw IllegalArgumentException(s"$twin is no twin of contest_merge_twins")

  /** Grid paths casing on c first, paths(r, c - 1) + paths(r - 1, c)
    * (`twin_grid_term/3`).
    */
  def twinGridTerm(size: Int, claimed: BigInt): Term =
    dynamic.withTwinArithmetic(names =>
      λ(one =>
        λ(grid => names.equality(grid(dynamic.unary(size))(dynamic.unary(size)))(dynamic.binary(claimed)))(
          file.program("twin_grid_body", names.plus, one)(file.program("twin_grid_body", names.plus, one))
        )
      )(dynamic.binary(1))
    )

  /** fib(n - 2) + fib(n - 1) (`twin_fibonacci_term/3`). */
  def twinFibonacciTerm(n: Int, claimed: BigInt): Term =
    dynamic.withTwinArithmetic(names =>
      λ(zero =>
        λ(one =>
          λ(function => names.equality(function(dynamic.unary(n)))(dynamic.binary(claimed)))(
            file.program("twin_fibonacci_body", names.plus, zero, one)(
              file.program("twin_fibonacci_body", names.plus, zero, one)
            )
          )
        )(dynamic.binary(1))
      )(dynamic.binary(0))
    )

  /** The product with the twin multiplication (`twin_product_term/4`). */
  def twinProductTerm(left: BigInt, right: BigInt, claimed: BigInt): Term =
    dynamic.withTwinArithmetic(names =>
      λ(zero =>
        λ(times => names.equality(times(dynamic.binary(left))(dynamic.binary(right)))(dynamic.binary(claimed)))(
          dynamic.twinTimesFunction(names.plus, zero)
        )
      )(dynamic.binary(0))
    )

  /** The intended head of the twin's original, which the twin shares. */
  private def originalValue(problem: TwinProblem, original: String): Template = problem match
    case TwinProblem.Grid      => dynamic.gridValue(original)
    case TwinProblem.Fibonacci => fibonacci.value(original)
    case TwinProblem.Product   => binary.value(original)

  /** The claim facts of the twins: each poses its original's claim with its
    * own argument.
    */
  def claims: Vector[ClaimFact] =
    twins.flatMap((twin, problem, original) =>
      val template = originalValue(problem, original)
      ClaimFact.headPoint(twin, template) :+ ScoredFiniteHead(
        twin,
        Vector(template),
        s"the twin of $original asks the same question at the same size with the arithmetic respelled (casing on the other operand first, the carry added to the other half, multiplication recursing on the right operand), each function computing the same values by finite recursion on finite numerals, so its Church Boolean is ${ClaimFact.text(template)}, the original's, reached in finitely many head reductions"
      )
    )

object MergeTwins:

  /** The problem a twin respells, the constructors of
    * problems/merge_twins/problem in order: grid paths (`MergeDynamic`),
    * Fibonacci (`MergeFibonacci`) and the binary product (`MergeBinary`).
    */
  enum TwinProblem:
    case Grid
    case Fibonacci
    case Product
