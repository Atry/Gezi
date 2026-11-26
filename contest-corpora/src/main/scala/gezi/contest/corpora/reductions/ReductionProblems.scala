package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The first problems of the reduction series, the port of
  * `problems/reduction_problems`: the label-free families'
  * programs with the claimed value taken away, so that the answer is the
  * value itself, a binary natural read by Scott case analysis. The programs
  * are built by the families' own builders, with the same sizes as their
  * points: fib(N) for N = 20, 40, 80, 160, 320; the products of
  * `problems/merge_binary` (its facts `product_point/4`); the lattice paths
  * of an N by N grid, C(2N, N), N = 8, 16, 32, 64; and the choice
  * `[a + b, b + a]` of two numbers (the facts `sum_problem/3`), two heads
  * that decode to one value. The expected trees are computed: fib by
  * iteration, the product and the sum by integer arithmetic, the binomial by
  * its product formula.
  */
object ReductionProblems:

  private val family = "reduction_problems"

  /** The problems, in the order of the Prolog's clauses. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    val fibonacci = Vector(
      "reduction_fibonacci_twenty" -> 20,
      "reduction_fibonacci_forty" -> 40,
      "reduction_fibonacci_eighty" -> 80,
      "reduction_fibonacci_one_hundred_sixty" -> 160,
      "reduction_fibonacci_three_hundred_twenty" -> 320
    ).map((point, number) =>
      problem(point, fibonacciProgram(group, number), group.fibonacci.referenceFibonacci(number))
    )
    val products = group.problems(family).rows("product_problem").map {
      case Vector(point, original) =>
        val (left, right, _) = group.products.claimed(ProblemData.text(original))
        problem(ProblemData.text(point), productProgram(group, left, right), left * right)
      case other => throw IllegalArgumentException(s"not a product problem: $other")
    }
    val grids = Vector(
      "reduction_grid_paths_eight" -> 8,
      "reduction_grid_paths_sixteen" -> 16,
      "reduction_grid_paths_thirty_two" -> 32,
      "reduction_grid_paths_sixty_four" -> 64
    ).map((point, size) => problem(point, gridProgram(group, size), binomial(2 * size, size)))
    val sums = group.problems(family).rows("sum_problem").map {
      case Vector(point, left, right) =>
        val (leftValue, rightValue) = (ProblemData.integer(left), ProblemData.integer(right))
        problem(ProblemData.text(point), sumBothOrdersProgram(group, leftValue, rightValue), leftValue + rightValue)
      case other => throw IllegalArgumentException(s"not a sum problem: $other")
    }
    fibonacci ++ products ++ grids ++ sums

  private def problem(point: String, program: ProblemTerm, value: BigInt): ReductionProblem =
    ReductionProblem(point, program, "binary", Expected.One(Scott.binaryTree(value)), Reduction.defaultLimits)

  /** C(total, chosen) by its product formula (`binomial/3`). */
  def binomial(total: Int, chosen: Int): BigInt =
    (1 to chosen).foldLeft(BigInt(1))((accumulated, index) => accumulated * (total - chosen + index) / index)

  /** fib(n) under the lets of zero, one and the Fibonacci function of
    * `problems/merge_fibonacci`.
    */
  def fibonacciProgram(group: ReductionGroup, number: Int): ProblemTerm =
    withFibonacci(group)(function => function(unary(number)))

  /** The body under the lets of the arithmetic, zero, one and the Fibonacci
    * function; the body is given the let variable of the function.
    */
  private[reductions] def withFibonacci(group: ReductionGroup)(body: ProblemTerm => ProblemTerm): ProblemTerm =
    group.arithmetic.withArithmetic(names =>
      λ(zero =>
        λ(one => λ(function => body(function))(group.fibonacci.fibonacciFunction(names.plus, zero, one)))(
          binary(1)
        )
      )(binary(0))
    )

  /** The product under the lets of zero and times. */
  def productProgram(group: ReductionGroup, left: BigInt, right: BigInt): ProblemTerm =
    withTimes(group)(times => times(binary(left))(binary(right)))

  /** The body under the lets of the arithmetic, zero and times; the body is
    * given the let variable times.
    */
  private[reductions] def withTimes(group: ReductionGroup)(body: ProblemTerm => ProblemTerm): ProblemTerm =
    group.arithmetic.withArithmetic(names =>
      λ(zero => λ(times => body(times))(group.arithmetic.timesFunction(names.plus, zero)))(
        binary(0)
      )
    )

  /** The lattice paths of the grid under the lets of one and the paths. */
  def gridProgram(group: ReductionGroup, size: Int): ProblemTerm =
    withGrid(group)(grid => squareGridPaths(grid, unary(size)))

  /** The body under the lets of the arithmetic, one and the paths; the body
    * is given the let variable of the paths.
    */
  private[reductions] def withGrid(group: ReductionGroup)(body: ProblemTerm => ProblemTerm): ProblemTerm =
    group.arithmetic.withArithmetic(names =>
      λ(one => λ(grid => body(grid))(group.arithmetic.gridFunction(names.plus, one)))(binary(1))
    )

  /** The paths of the square grid whose side is the unary numeral. */
  private[reductions] def squareGridPaths(grid: ProblemTerm, side: ProblemTerm): ProblemTerm = grid(side)(side)

  /** `[plus a b, plus b a]` under the lets of the arithmetic. */
  def sumBothOrdersProgram(group: ReductionGroup, left: BigInt, right: BigInt): ProblemTerm =
    withPlus(group)(plus => sumBothOrders(plus, binary(left), binary(right)))

  /** The body under the lets of the arithmetic; the body is given the let
    * variable plus.
    */
  private[reductions] def withPlus(group: ReductionGroup)(body: ProblemTerm => ProblemTerm): ProblemTerm =
    group.arithmetic.withArithmetic(names => body(names.plus))

  /** `[plus a b, plus b a]`. */
  private[reductions] def sumBothOrders(plus: ProblemTerm, left: ProblemTerm, right: ProblemTerm): ProblemTerm =
    members(Vector(plus(left)(right), plus(right)(left)))
