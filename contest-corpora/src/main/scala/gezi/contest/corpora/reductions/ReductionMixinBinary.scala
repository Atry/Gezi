package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.frontend.Term

/** MIXINv2's BinNat library in the mixin encoding, the port of
  * `problems/reduction_mixin_binary`: `C.equality(A.plus(B))` or
  * `C.equality(A.times(B))` read at church, whose answer is one Boolean.
  */
object ReductionMixinBinary:

  private val family = "reduction_mixin_binary"

  /** The program of an equation (`binary_point_surface/2`). */
  def binaryPointSurface(
      mixins: MixinLibrary,
      operation: String,
      left: BigInt,
      right: BigInt,
      result: BigInt
  ): ProblemTerm =
    withBinaryLibrary(mixins)(names =>
      equationRead(
        mixins,
        operation,
        mixins.binaryInstance(names, left),
        mixins.binaryInstance(names, right),
        mixins.binaryInstance(names, result)
      )
    )

  /** The body under the lets of the library `binary`. */
  private[reductions] def withBinaryLibrary(mixins: MixinLibrary)(
      body: MixinNames => ProblemTerm
  ): ProblemTerm =
    mixins.withMixinLibrary(Vector("binary"), Vector.empty)(body)

  /** `Result.equality(Left.operation(Right))` read at church, the three
    * operands binary objects.
    */
  private[reductions] def equationRead(
      mixins: MixinLibrary,
      operation: String,
      left: ProblemTerm,
      right: ProblemTerm,
      result: ProblemTerm
  ): ProblemTerm =
    val operated = mixins.slotApplied("binary", operation, left, right)
    val compared = mixins.slotApplied("binary", "equality", result, operated)
    mixins.readSlot("boolean", "church", compared)

  /** The problems (`binary_point/5`), each expecting the Boolean of its
    * equation.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("binary_point").map {
      case Vector(point, operation, left, right, result) =>
        val name = ProblemData.text(operation)
        val (leftValue, rightValue, resultValue) =
          (
            ProblemData.integer(left),
            ProblemData.integer(right),
            ProblemData.integer(result)
          )
        val value = name match
          case "plus"  => leftValue + rightValue
          case "times" => leftValue * rightValue
          case other   => throw IllegalArgumentException(s"no operation $other")
        ReductionProblem(
          ProblemData.text(point),
          binaryPointSurface(
            group.mixins,
            name,
            leftValue,
            rightValue,
            resultValue
          ),
          "boolean",
          Expected.One(Scott.booleanTree(value == resultValue)),
          Reduction.defaultLimits
        )
      case other =>
        throw IllegalArgumentException(s"not a binary point: $other")
    }
