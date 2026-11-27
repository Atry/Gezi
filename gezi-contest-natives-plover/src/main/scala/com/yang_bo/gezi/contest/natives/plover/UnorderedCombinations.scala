package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The number of ways to reach a target with the items, each usable any number
  * of times, two ways being the same when they use each position of the list
  * equally often, modulo a modulus. An item listed twice is two items, as in
  * the definition it replaces, the typed version `plover_typed_combinations`.
  *
  * The knapsack over the items in turn: after an item c, ways(s) is the ways
  * before it at s plus the ways after it at s - c, so along each residue class
  * of c the table is the running sum of the table before it. It takes O(target
  * * items) additions.
  *
  * The items are positive, the target is a natural and the modulus is positive:
  * the native's places declare the positive naturals, and a narrow block
  * compiles the call only when the filters at the operands' roots name them. A
  * native does not check its operands (`CONTRIBUTING.md`, "Types live only in
  * the term"), so nothing here checks them. A target of `Int.MaxValue` or
  * beyond is more cells than a table holds, and `intValueExact` or `addExact`
  * throws `ArithmeticException` on it.
  */
object UnorderedCombinations:

  /** The largest bit length of a modulus whose residues add in a `Long`. */
  private val longModulusBits: Int = 62

  /** The ways to reach the target modulo the modulus. */
  def count(
      items: Vector[BigInteger],
      target: BigInteger,
      modulus: BigInteger
  ): BigInteger =
    val cells = Math.addExact(target.intValueExact, 1)
    val reachable = items.filter(_.compareTo(target) <= 0).map(_.intValueExact)
    if modulus.bitLength <= longModulusBits then
      BigInteger.valueOf(
        countedInLongs(reachable, cells, modulus.longValueExact)
      )
    else countedInBigIntegers(reachable, cells, modulus)

  private def countedInLongs(
      items: Vector[Int],
      cells: Int,
      modulus: Long
  ): Long =
    val start =
      IArray.tabulate(cells)(sum => if sum == 0 then 1L % modulus else 0L)
    items.foldLeft(start)((before, item) => longsAfter(before, item, modulus))(
      cells - 1
    )

  /** The table after the item: the running sums of each residue class, each
    * class's sums starting at 0 so that the sum through position i is at i + 1.
    */
  private def longsAfter(
      before: IArray[Long],
      item: Int,
      modulus: Long
  ): IArray[Long] =
    val sums = IArray.tabulate(math.min(item, before.length)) { residue =>
      val positions = (before.length - residue - 1) / item + 1
      IArray
        .tabulate(positions)(position => before(residue + position * item))
        .scanLeft(0L) { (sum, value) =>
          val added = sum + value
          if added >= modulus then added - modulus else added
        }
    }
    IArray.tabulate(before.length)(sum => sums(sum % item)(sum / item + 1))

  private def countedInBigIntegers(
      items: Vector[Int],
      cells: Int,
      modulus: BigInteger
  ): BigInteger =
    val start = IArray.tabulate(cells)(sum =>
      if sum == 0 then BigInteger.ONE.mod(modulus) else BigInteger.ZERO
    )
    items.foldLeft(start)((before, item) =>
      bigIntegersAfter(before, item, modulus)
    )(cells - 1)

  private def bigIntegersAfter(
      before: IArray[BigInteger],
      item: Int,
      modulus: BigInteger
  ): IArray[BigInteger] =
    val sums = IArray.tabulate(math.min(item, before.length)) { residue =>
      val positions = (before.length - residue - 1) / item + 1
      IArray
        .tabulate(positions)(position => before(residue + position * item))
        .scanLeft(BigInteger.ZERO) { (sum, value) =>
          val added = sum.add(value)
          if added.compareTo(modulus) >= 0 then added.subtract(modulus)
          else added
        }
    }
    IArray.tabulate(before.length)(sum => sums(sum % item)(sum / item + 1))
