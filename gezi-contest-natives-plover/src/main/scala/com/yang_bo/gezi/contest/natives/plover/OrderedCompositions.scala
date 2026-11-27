package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The number of ordered sequences of items that sum to a target, modulo a
  * modulus, by the recurrence on the distance d still to cover: f(0) = 1 and
  * f(d) is the sum of f(d - c) over the items c no larger than d. An item
  * listed twice counts twice, as in the definition it replaces, the typed
  * version `plover_typed_ordered_compositions`, whose count from a sum s
  * already reached is f(t - s) for the target t. It takes O(target * items)
  * additions.
  *
  * The items are positive, the target is a natural and the modulus is positive:
  * the native's places declare the positive naturals, and a narrow block
  * compiles the call only when the filters at the operands' roots name them. A
  * native does not check its operands (`CONTRIBUTING.md`, "Types live only in
  * the term"), so nothing here checks them. A target beyond an `Int` is more
  * cells than a table holds, and `intValueExact` throws `ArithmeticException`
  * on it.
  */
object OrderedCompositions:

  /** The largest bit length of a modulus whose residues add in a `Long`. */
  private val longModulusBits: Int = 62

  /** f(target) modulo the modulus. */
  def count(
      items: Vector[BigInteger],
      target: BigInteger,
      modulus: BigInteger
  ): BigInteger =
    val distance = target.intValueExact
    val reachable = items.filter(_.compareTo(target) <= 0).map(_.intValueExact)
    if modulus.bitLength <= longModulusBits then
      BigInteger.valueOf(
        countedInLongs(reachable, distance, modulus.longValueExact)
      )
    else countedInBigIntegers(reachable, distance, modulus)

  private def countedInLongs(
      items: Vector[Int],
      distance: Int,
      modulus: Long
  ): Long =
    val table = (1 to distance).foldLeft(Vector(1L % modulus)) {
      (cells, covered) =>
        cells :+ items.foldLeft(0L) { (sum, item) =>
          if item > covered then sum
          else
            val added = sum + cells(covered - item)
            if added >= modulus then added - modulus else added
        }
    }
    table(distance)

  private def countedInBigIntegers(
      items: Vector[Int],
      distance: Int,
      modulus: BigInteger
  ): BigInteger =
    val table = (1 to distance).foldLeft(Vector(BigInteger.ONE.mod(modulus))) {
      (cells, covered) =>
        cells :+ items.foldLeft(BigInteger.ZERO) { (sum, item) =>
          if item > covered then sum
          else
            val added = sum.add(cells(covered - item))
            if added.compareTo(modulus) >= 0 then added.subtract(modulus)
            else added
        }
    }
    table(distance)
