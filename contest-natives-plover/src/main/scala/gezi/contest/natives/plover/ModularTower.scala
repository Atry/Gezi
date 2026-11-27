package gezi.contest.natives.plover

import java.math.BigInteger

/** A natural to the power of a power, modulo a positive modulus, the value of
  * the definition it replaces, the typed version `plover_typed_modular_tower`,
  * with a number to the power zero being one, zero to the power zero included.
  *
  * The exponent E = b^c is not computed when it is large. For every base a and
  * every E at least the bit length of the modulus m,
  * a^E = a^((E mod φ(m)) + φ(m)) modulo m, which holds whether or not a is
  * coprime to m, so a multiple of a prime modulus stays zero at every positive
  * exponent. A smaller E is computed exactly.
  *
  * The operands are what the native's places declare, and a native does not
  * check them (`CONTRIBUTING.md`, "Types live only in the term").
  */
object ModularTower:

  /** The longest modulus, in bits, whose totient is found by trial division. */
  private val longestModulus: Int = 48

  /** base^(exponentBase^exponentPower) modulo the modulus. Throws
    * `ArithmeticException` for a modulus longer than `longestModulus` bits
    * whose exponent is too large to compute.
    */
  def power(base: BigInteger, exponentBase: BigInteger, exponentPower: BigInteger, modulus: BigInteger): BigInteger =
    exactExponent(exponentBase, exponentPower, modulus.bitLength) match
      case Some(exponent) => base.modPow(exponent, modulus)
      case None =>
        if modulus.bitLength > longestModulus then
          throw ArithmeticException(s"a modulus of ${modulus.bitLength} bits is longer than $longestModulus")
        val totientOfModulus = BigInteger.valueOf(totient(modulus.longValueExact))
        base.modPow(exponentBase.modPow(exponentPower, totientOfModulus).add(totientOfModulus), modulus)

  /** b^c when it is less than the bound, none when it is at least the bound.
    * Only a base of at least two grows, so at most the bound's bit length of
    * multiplications are made.
    */
  private def exactExponent(exponentBase: BigInteger, exponentPower: BigInteger, bound: Int): Option[BigInteger] =
    val limit = BigInteger.valueOf(bound.toLong)
    if exponentPower.signum == 0 then Option.when(BigInteger.ONE.compareTo(limit) < 0)(BigInteger.ONE)
    else if exponentBase.compareTo(BigInteger.ONE) <= 0 then Option.when(exponentBase.compareTo(limit) < 0)(exponentBase)
    else
      @scala.annotation.tailrec
      def raised(product: BigInteger, remaining: BigInteger): Option[BigInteger] =
        if product.compareTo(limit) >= 0 then None
        else if remaining.signum == 0 then Some(product)
        else raised(product.multiply(exponentBase), remaining.subtract(BigInteger.ONE))
      raised(exponentBase, exponentPower.subtract(BigInteger.ONE))

  /** Euler's totient of a positive number, by trial division. */
  private def totient(number: Long): Long =
    @scala.annotation.tailrec
    def reduced(rest: Long, divisor: Long, result: Long): Long =
      if divisor > rest / divisor then if rest > 1 then result / rest * (rest - 1) else result
      else if rest % divisor == 0 then reduced(withoutFactor(rest, divisor), divisor + 1, result / divisor * (divisor - 1))
      else reduced(rest, divisor + 1, result)
    reduced(number, 2, number)

  @scala.annotation.tailrec
  private def withoutFactor(number: Long, factor: Long): Long =
    if number % factor == 0 then withoutFactor(number / factor, factor) else number
