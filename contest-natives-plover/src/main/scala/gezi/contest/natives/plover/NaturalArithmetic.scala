package gezi.contest.natives.plover

import java.math.BigInteger

/** The remainder and the difference of canonical naturals, the values of the
  * recursions `plover_binary_modulo` and
  * `binary_subtract minuend subtrahend false` that the typed versions
  * `plover_typed_natural_modulo` and `plover_typed_natural_difference` carry.
  * The operands are what the natives' places declare, and a native does not
  * check them (`CONTRIBUTING.md`, "Types live only in the term").
  */
object NaturalArithmetic:

  /** What the remainder's recursion gives: the number modulo the modulus, and
    * the number itself when the modulus is zero, where the recursion never
    * finds a part smaller than the modulus and subtracts zero.
    */
  def modulo(number: BigInteger, modulus: BigInteger): BigInteger =
    if modulus.signum == 0 then number else number.mod(modulus)

  /** What the subtraction's recursion gives with no borrow. It walks the
    * minuend's bits and stops at its end, dropping the subtrahend's higher bits
    * and the last borrow, so its value is the difference modulo two to the
    * minuend's bit length: the difference itself when the subtrahend is no
    * larger than the minuend.
    */
  def difference(minuend: BigInteger, subtrahend: BigInteger): BigInteger =
    minuend
      .subtract(subtrahend)
      .mod(BigInteger.ONE.shiftLeft(minuend.bitLength))
