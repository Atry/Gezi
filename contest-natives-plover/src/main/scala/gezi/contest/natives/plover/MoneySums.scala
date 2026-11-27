package gezi.contest.natives.plover

import java.math.BigInteger

/** The sum of the distinct sums that nonempty sets of the coins make, the value
  * of the definition it replaces, the typed version `plover_typed_money_sums`.
  * A bit set holds the sums reachable with the coins read so far, the empty set's
  * zero among them, in O(coins * total / 64) machine words. Zero adds nothing to
  * the sum, so it does not matter whether a nonempty set also makes it, which a
  * coin of zero does.
  *
  * The coins are canonical naturals, which is what the native's place declares,
  * and a narrow block compiles the call only when the filter at the operand's
  * root names them. A native does not check its operands (`CONTRIBUTING.md`,
  * "Types live only in the term").
  */
object MoneySums:

  /** The largest total of the coins whose bit set is built: 12.5 MB of bits. */
  private val largestTotal: BigInteger = BigInteger.valueOf(100000000)

  /** The sum of the distinct sums. Throws `ArithmeticException` when the coins
    * total more than `largestTotal`.
    */
  def total(coins: Vector[BigInteger]): BigInteger =
    val coinTotal = coins.foldLeft(BigInteger.ZERO)(_.add(_))
    if coinTotal.compareTo(largestTotal) > 0 then
      throw ArithmeticException(s"coins totalling $coinTotal are more than $largestTotal")
    val reachable = coins.foldLeft(BigInteger.ONE)((sums, coin) => sums.or(sums.shiftLeft(coin.intValue)))
    @scala.annotation.tailrec
    def summed(position: Int, sum: Long): Long =
      if position >= reachable.bitLength then sum
      else summed(position + 1, if reachable.testBit(position) then sum + position else sum)
    BigInteger.valueOf(summed(1, 0))
