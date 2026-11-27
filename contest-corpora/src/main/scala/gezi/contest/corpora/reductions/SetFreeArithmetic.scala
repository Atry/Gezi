package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.common.DeBruijnTerms.hoas as fromDeBruijn
import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term

/** Binary sums and products by the standard library's merge_binary_plus and
  * merge_binary_times, in both spellings of the point (the library function is
  * the same define in both), the port of `problems/set_free_arithmetic`: direct
  * and respelled twins, and a near miss whose times template has its even and
  * odd cases exchanged.
  */
object SetFreeArithmetic:

  private val family = "set_free_arithmetic"

  /** A point: its operation, spelling and operands (`arithmetic_point/5`). */
  final case class ArithmeticPoint(
      point: String,
      operation: String,
      spelling: Spelling,
      left: BigInt,
      right: BigInt
  )

  /** The points: the facts read, then each product size with each twin
    * (`product_size/2`, `product_twin/3`), the operands `10^Digits // 7` and
    * `10^Digits // 3`.
    */
  def points(group: ReductionGroup): Vector[ArithmeticPoint] =
    val stated = group.problems(family).rows("arithmetic_point").map {
      case Vector(point, operation, spelling, left, right) =>
        ArithmeticPoint(
          ProblemData.text(point),
          ProblemData.text(operation),
          SetFree.spelling(spelling),
          ProblemData.integer(left),
          ProblemData.integer(right)
        )
      case other =>
        throw IllegalArgumentException(s"not an arithmetic point: $other")
    }
    val sized = for
      size <- group.problems(family).rows("product_size")
      twin <- group.problems(family).rows("product_twin")
    yield
      val digits = ProblemData.small(size(1))
      ArithmeticPoint(
        s"set_free_product_${ProblemData.text(size(0))}_digits_${ProblemData.text(twin(0))}",
        ProblemData.text(twin(1)),
        SetFree.spelling(twin(2)),
        BigInt(10).pow(digits) / 7,
        BigInt(10).pow(digits) / 3
      )
    stated ++ sized

  /** `Function LeftNumeral RightNumeral` (`arithmetic_point_surface/2`); the
    * function of a sum or a product is the standard library's define.
    */
  def pointSurface(group: ReductionGroup, point: ArithmeticPoint): ProblemTerm =
    operationFunction(group, point.operation, point.spelling)(
      binary(point.left)
    )(binary(point.right))

  /** The function a point applies to its two numerals. */
  private[reductions] def operationFunction(
      group: ReductionGroup,
      operation: String,
      spelling: Spelling
  ): ProblemTerm =
    if operation == "near_times" then
      nearTimesApplied(group)(nearTimesApplied(group))
    else SetFree.libraryFunction(group, operation, spelling)

  /** The near miss's template applied to the standard library's plus. */
  private def nearTimesApplied(group: ReductionGroup): ProblemTerm =
    nearTimesTemplate(group.attractors)(
      SetFree.libraryFunction(group, "merge_binary_plus", Spelling.Direct)
    )

  /** A fresh copy of the times template with its even and odd cases exchanged,
    * a beta eta normal form like the attractor's (`near_times_template/1`): the
    * attractor's `\plus. \self. \a. \b. a zero (\h1. E) (\h2. plus b O)`
    * becomes `\plus. \self. \a. \b. a zero (\h1. plus b E) (\h2. O)`. Throws
    * when the attractor has not that shape, where the Prolog's unification
    * fails.
    */
  def nearTimesTemplate(attractors: Attractors): ProblemTerm =
    import DeBruijnTerm.*
    attractors.attractorFunction("merge_binary_times") match
      case Lambda(
            Lambda(
              Lambda(
                Lambda(
                  Apply(
                    Apply(Apply(Variable(1), zero), Lambda(evenDouble)),
                    Lambda(
                      Apply(Apply(Variable(4), Variable(1)), oddDouble)
                    )
                  )
                )
              )
            )
          ) =>
        def plusOfB(term: ProblemDeBruijnTerm) =
          Apply(Apply(Variable(4), Variable(1)), term)
        fromDeBruijn(
          Lambda(
            Lambda(
              Lambda(
                Lambda(
                  Apply(
                    Apply(
                      Apply(Variable(1), zero),
                      Lambda(plusOfB(evenDouble))
                    ),
                    Lambda(oddDouble)
                  )
                )
              )
            )
          )
        )
      case other =>
        throw IllegalArgumentException(
          s"the times attractor has not the template's shape: $other"
        )

  /** `0 b = 0, 2h b = b + double(h b), (2h + 1) b = double(h b)`
    * (`near_product/3`).
    */
  def nearProduct(left: BigInt, right: BigInt): BigInt =
    if left == 0 then 0
    else
      val halfProduct = nearProduct(left >> 1, right)
      if (left & 1) == 0 then right + 2 * halfProduct else 2 * halfProduct

  /** The result the point expects: the near product, or the attractor's
    * reference (`reference/4`, `attractor_reference/3`).
    */
  def reference(point: ArithmeticPoint): BigInt = point.operation match
    case "near_times"         => nearProduct(point.left, point.right)
    case "merge_binary_plus"  => point.left + point.right
    case "merge_binary_times" => point.left * point.right
    case other => throw IllegalArgumentException(s"no reference of $other")

  /** The problems. Every near miss's reference differs from the product, so
    * each is a trap for the native product (`near_misses_differ/0`); a near
    * miss that does not throws.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    points(group).map(point =>
      if point.operation == "near_times" && reference(
          point
        ) == point.left * point.right
      then throw IllegalArgumentException(s"near_miss_trap: ${point.point}")
      ReductionProblem(
        point.point,
        pointSurface(group, point),
        "binary",
        Expected.One(Scott.binaryTree(reference(point))),
        Reduction.defaultLimits
      )
    )
