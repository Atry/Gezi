package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** An object with two implementations of one method in the mixin encoding, the
  * port of `problems/reduction_mixins`: the class {Base, Increment_1, ...,
  * Increment_m}, Base = {Run, Start}, read at `run n start`, whose answers are
  * the sums of n increments.
  */
object ReductionMixins:

  private val family = "reduction_mixins"

  /** `run n accumulator = n accumulator (\p. run p (step accumulator))`. */
  private def runMixin(mixins: MixinLibrary): ProblemTerm =
    mixins.selfMixin("counter", "run")(self =>
      λ(count =>
        λ(accumulator =>
          count(accumulator)(
            λ(predecessor =>
              mixins.slotApplied(
                "counter",
                "run",
                self,
                predecessor,
                mixins.slotApplied("counter", "step", self, accumulator)
              )
            )
          )
        )
      )
    )

  /** `run Count start` of the object {{Run, Start}, Increment_a ...} under the
    * lets of the arithmetic and of the mixin encoding (`counter_surface/3`).
    */
  def counterSurface(
      group: ReductionGroup,
      count: Int,
      increments: Vector[Int]
  ): ProblemTerm =
    val mixins = group.mixins
    group.arithmetic.withArithmetic(names =>
      mixins.withMixinLibrary(Vector.empty, Vector("counter"))(_ =>
        val instance = members(
          members(
            Vector(
              runMixin(mixins),
              mixins.valueMixin("counter", "start" -> binary(0))
            )
          ) +:
            increments.map(increment =>
              mixins.valueMixin(
                "counter",
                "step" -> λ(value => names.plus(value)(binary(increment)))
              )
            )
        )
        λ(objectTerm =>
          mixins.slotApplied(
            "counter",
            "run",
            objectTerm,
            unary(count),
            mixins.readSlot("counter", "start", objectTerm)
          )
        )(instance)
      )
    )

  /** The sums of Count increments from consecutive increments, every integer
    * from Count times the least to Count times the greatest (`sum_range/3`).
    */
  def sumRange(count: Int, increments: Vector[Int]): Vector[Int] =
    val (least, greatest) = (increments.min, increments.max)
    require(
      increments == (least to greatest).toVector,
      s"the increments are not consecutive: $increments"
    )
    (count * least to count * greatest).toVector

  /** The problems (`problem/3`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("problem").map {
      case Vector(point, count, increments) =>
        val (countValue, incrementValues) =
          (ProblemData.small(count), ProblemData.smalls(increments))
        ReductionProblem(
          ProblemData.text(point),
          counterSurface(group, countValue, incrementValues),
          "binary",
          Expected.Trees(
            sumRange(countValue, incrementValues).map(Scott.binaryTree(_))
          ),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a problem: $other")
    }
