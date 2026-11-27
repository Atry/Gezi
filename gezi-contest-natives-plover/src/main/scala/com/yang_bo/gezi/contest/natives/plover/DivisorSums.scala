package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The sum over i from 1 to a limit of the sum of the divisors of i, modulo a
  * positive modulus, the value of the definition it replaces, the typed version
  * `plover_typed_divisor_sums`. Each d divides floor(n / d) of the numbers up
  * to n, so the total is the sum over d of d times floor(n / d), and that
  * quotient is constant on runs of d, about 2 sqrt(n) of them. The operands are
  * what the native's places declare, and a native does not check them
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
object DivisorSums:

  /** The longest limit, in bits, whose runs are walked. */
  private val longestLimit: Int = 62

  /** The longest modulus, in bits, whose products fit a `Long`. */
  private val longestWordModulus: Int = 31

  /** The total modulo the modulus. Throws `ArithmeticException` for a limit
    * longer than `longestLimit` bits.
    */
  def total(limit: BigInteger, modulus: BigInteger): BigInteger =
    if limit.bitLength > longestLimit then
      throw ArithmeticException(
        s"a limit of ${limit.bitLength} bits is longer than $longestLimit"
      )
    val number = limit.longValueExact
    if modulus.bitLength <= longestWordModulus then
      BigInteger.valueOf(inWords(number, modulus.longValueExact))
    else inBigIntegers(number, modulus)

  /** The two factors of the sum of the run from first to last, the count and
    * the sum of its ends, with the even one halved.
    */
  private def runFactors(first: Long, last: Long): (Long, Long) =
    val count = last - first + 1
    val ends = first + last
    if count % 2 == 0 then (count / 2, ends) else (count, ends / 2)

  private def inWords(number: Long, modulus: Long): Long =
    @scala.annotation.tailrec
    def summed(first: Long, total: Long): Long =
      if first > number then total
      else
        val quotient = number / first
        val last = number / quotient
        val (left, right) = runFactors(first, last)
        val run = (left % modulus) * (right % modulus) % modulus
        summed(last + 1, (total + run * (quotient % modulus)) % modulus)
    summed(1, 0)

  private def inBigIntegers(number: Long, modulus: BigInteger): BigInteger =
    @scala.annotation.tailrec
    def summed(first: Long, total: BigInteger): BigInteger =
      if first > number then total
      else
        val quotient = number / first
        val last = number / quotient
        val (left, right) = runFactors(first, last)
        val run = BigInteger
          .valueOf(left)
          .multiply(BigInteger.valueOf(right))
          .multiply(BigInteger.valueOf(quotient))
        summed(last + 1, total.add(run).mod(modulus))
    summed(1, BigInteger.ZERO)
