package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The Fibonacci class in the mixin encoding, the port of
  * `problems/reduction_mixin_fibonacci`:
  * `Claimed.equality({fibonacci, n : Count}.value)` read at church.
  */
object ReductionMixinFibonacci:

  private val family = "reduction_mixin_fibonacci"

  /** The program (`fibonacci_surface/3`). */
  def fibonacciSurface(mixins: MixinLibrary, count: Int, claimed: Int): Term =
    mixins.withMixinLibrary(Vector("natural"), Vector("fibonacci_module", "fibonacci"))(names =>
      val module = fibonacciModule(mixins, names)
      val value = callValue(mixins, module, mixins.naturalInstance(names, count))
      val compared = mixins.slotApplied("natural", "equality", mixins.naturalInstance(names, claimed), value)
      mixins.readSlot("boolean", "church", compared)
    )

  /** The module whose one slot is the class fibonacci (`fibonacci_module/2`). */
  private def fibonacciModule(mixins: MixinLibrary, names: MixinNames): Term =
    members(Vector(mixins.selfMixin("fibonacci_module", "fibonacci")(module =>
      members(Vector(fibonacciMixin(mixins, names, module)))
    )))

  /** value over self's n, each read of self.n, and of the class from the
    * module (`fibonacci_mixin/3`).
    */
  private def fibonacciMixin(mixins: MixinLibrary, names: MixinNames, module: Term): Term =
    mixins.selfMixin("fibonacci", "value")(self =>
      val sum = mixins.slotApplied(
        "natural",
        "plus",
        callValue(mixins, module, selfPredecessors(mixins, self, 1)),
        callValue(mixins, module, selfPredecessors(mixins, self, 2))
      )
      val predecessorDispatched = mixins.slotApplied(
        "natural",
        "accept",
        selfPredecessors(mixins, self, 1),
        mixins.naturalInstance(names, 1),
        λ(_ => sum)
      )
      mixins.slotApplied(
        "natural",
        "accept",
        selfPredecessors(mixins, self, 0),
        mixins.naturalInstance(names, 0),
        λ(_ => predecessorDispatched)
      )
    )

  /** self.n followed by `count` reads of predecessor
    * (`self_n_predecessors/3`).
    */
  private def selfPredecessors(mixins: MixinLibrary, self: Term, count: Int): Term =
    (1 to count).foldLeft(mixins.readSlot("fibonacci", "n", self))((read, _) =>
      mixins.readSlot("natural", "predecessor", read)
    )

  /** `{fibonacci, n : N}.value`, the class read from the module
    * (`call_value/3`).
    */
  private def callValue(mixins: MixinLibrary, module: Term, number: Term): Term =
    val fibonacci = mixins.readSlot("fibonacci_module", "fibonacci", module)
    mixins.readSlot("fibonacci", "value", members(Vector(fibonacci, mixins.valueMixin("fibonacci", "n" -> number))))

  /** fib by its recursion (`fibonacci/2`). */
  def fibonacci(count: Int): BigInt =
    (1 to count).foldLeft((BigInt(0), BigInt(1)))((pair, _) => (pair._2, pair._1 + pair._2))._1

  /** The problems (`fibonacci_point/3`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("fibonacci_point").map {
      case Vector(point, count, claimed) =>
        val (countValue, claimedValue) = (ProblemData.small(count), ProblemData.small(claimed))
        ReductionProblem(
          ProblemData.text(point),
          fibonacciSurface(group.mixins, countValue, claimedValue),
          "boolean",
          Expected.One(Scott.booleanTree(fibonacci(countValue) == claimedValue)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a Fibonacci point: $other")
    }
