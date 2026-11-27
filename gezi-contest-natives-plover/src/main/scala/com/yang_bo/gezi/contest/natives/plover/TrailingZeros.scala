package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The number of decimal zeros that end the factorial of a canonical natural,
  * the value of the definition it replaces, the typed version
  * `plover_typed_trailing_zeros`, by Legendre's formula in O(log n) divisions.
  * A native does not check its operand (`CONTRIBUTING.md`, "Types live only in
  * the term").
  */
object TrailingZeros:

  private val five: BigInteger = BigInteger.valueOf(5)

  /** The sum over k >= 1 of the floor of the number over five to the k: the
    * power of five in its factorial, which the power of two is no smaller than.
    */
  def count(number: BigInteger): BigInteger =
    @scala.annotation.tailrec
    def summed(rest: BigInteger, total: BigInteger): BigInteger =
      if rest.signum == 0 then total
      else
        val quotient = rest.divide(five)
        summed(quotient, total.add(quotient))
    summed(number, BigInteger.ZERO)
