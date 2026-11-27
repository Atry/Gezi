package com.yang_bo.gezi.contest.natives.plover

import com.yang_bo.gezi.jit.NaturalLattice
import java.math.BigInteger

/** The value of the definition it replaces, the typed version
  * `plover_typed_billboard`, as the term it is ≃_O to: the target when two
  * disjoint subsets of the rods both sum to it; otherwise the choice of the
  * heights H that two disjoint subsets can share, in parallel with the target,
  * which has no normal form but is not `top`, a context consuming it can have
  * an answer. For each height of the left subset up to a bound it keeps the set
  * of heights the right subset can have with it, a bit set, and reads the rods
  * in turn, in O(rods * bound^2 / 64) machine words: the bound is the target,
  * and when the target is not reached, half the rods' sum, which every height
  * of H is at most.
  *
  * The rods and the target are canonical naturals, which is what the native's
  * places declare, and a narrow block compiles the call only when the filters
  * at the operands' roots name them. A native does not check its operands
  * (`CONTRIBUTING.md`, "Types live only in the term"). A bound above
  * `largestBound` is more bits than a table holds, and this throws
  * `ArithmeticException` on it.
  */
object Billboard:

  /** The largest bound whose table is computed: 30,000^2 bits are 112 MB. */
  private val largestBound: Int = 30000

  /** The term the typed version is ≃_O to, the JVM convention of
    * `com.yang_bo.gezi.jit.StaticBlockResult.Lattice`: the target's numeral when two
    * disjoint subsets of the rods both sum to it; otherwise the choice of the
    * heights two disjoint subsets share, in increasing order, in parallel with
    * the target.
    */
  def term(rods: Vector[BigInteger], target: BigInteger): NaturalLattice =
    val total = rods.foldLeft(BigInteger.ZERO)(_.add(_))
    val half = total.shiftRight(1)
    val reached = target.compareTo(half) <= 0 && balanced(rods, target).testBit(
      target.intValue
    )
    if reached then NaturalLattice.Numeral(target)
    else
      val table = balanced(rods, half)
      val heights = Vector
        .range(0, half.intValue + 1)
        .filter(table.testBit)
        .map(height => NaturalLattice.Numeral(BigInteger.valueOf(height)))
      NaturalLattice.Parallel(
        NaturalLattice.Choice(heights),
        NaturalLattice.Numeral(target)
      )

  /** The bit set of the heights up to `bound` that two disjoint subsets of the
    * rods both sum to: bit h is set when the left sum h goes with the right sum h.
    * For each left sum l up to the bound, the set of right sums up to the bound
    * that go with it, a rod at a time; a sum only grows, so a state past the
    * bound never comes back to it, and a rod above the bound can only be left
    * out.
    */
  private def balanced(
      rods: Vector[BigInteger],
      bound: BigInteger
  ): BigInteger =
    if bound.bitLength > 31 || bound.intValue > largestBound then
      throw ArithmeticException(s"a bound of $bound is more than $largestBound")
    val height = bound.intValue
    val usable = rods.filter(_.compareTo(bound) <= 0).map(_.intValue)
    val within = BigInteger.ONE.shiftLeft(height + 1).subtract(BigInteger.ONE)
    val noRod = Vector.tabulate(height + 1)(left =>
      if left == 0 then BigInteger.ONE else BigInteger.ZERO
    )
    val everyRod = usable.foldLeft(noRod) { (before, rod) =>
      Vector.tabulate(height + 1) { left =>
        val onRight = before(left).or(before(left).shiftLeft(rod).and(within))
        if left >= rod then onRight.or(before(left - rod)) else onRight
      }
    }
    everyRod.zipWithIndex.foldLeft(BigInteger.ZERO) {
      case (heights, (rights, left)) =>
        if rights.testBit(left) then heights.setBit(left) else heights
    }
