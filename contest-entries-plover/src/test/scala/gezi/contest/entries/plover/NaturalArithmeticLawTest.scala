package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.natives.plover.NaturalArithmetic
import gezi.generatedinputs.GeneratedProperties

/** The laws of the remainder and of the difference with no borrow. Their
  * purpose is to catch a native that differs from the recursion it replaces
  * where the recursion is not the plain operation: a subtrahend larger than
  * the minuend, a subtrahend longer than the minuend, a zero minuend and a
  * zero modulus.
  */
class NaturalArithmeticLawTest extends GeneratedProperties:

  private val drawnNatural: Gen[BigInt] =
    Gen.choice1(
      Gen.int(Range.linear(0, 1000)).map(BigInt(_)),
      Gen.int(Range.linear(0, 1000)).map(offset => (BigInt(1) << 40) + BigInt(offset))
    )

  /** `binary_subtract` as its term reads the bits, from the low bit up to the
    * end of the minuend.
    */
  private def subtracted(minuend: BigInt, subtrahend: BigInt, borrow: Boolean): BigInt =
    if minuend == 0 then BigInt(0)
    else
      val bits = (if minuend.testBit(0) then 1 else 0) - (if subtrahend.testBit(0) then 1 else 0) - (if borrow then 1 else 0)
      val rest = subtracted(minuend >> 1, subtrahend >> 1, bits < 0)
      (rest << 1) + (bits & 1)

  property("the difference is what the recursion gives, a larger subtrahend included") {
    for
      minuend <- drawnNatural.forAll
      subtrahend <- drawnNatural.forAll
    yield
      val computed = NaturalArithmetic.difference(minuend.bigInteger, subtrahend.bigInteger)
      Result.diff(BigInt(computed), subtracted(minuend, subtrahend, false))(_ == _)
  }

  property("the remainder of quotient times modulus plus a smaller number is that number") {
    for
      quotient <- drawnNatural.forAll
      modulus <- drawnNatural.map(_ + 1).forAll
      offset <- drawnNatural.forAll
    yield
      val remainder = offset % modulus
      val computed = NaturalArithmetic.modulo((quotient * modulus + remainder).bigInteger, modulus.bigInteger)
      Result.diff(BigInt(computed), remainder)(_ == _)
  }

  property("a zero modulus leaves the number, as the recursion subtracts zero") {
    for number <- drawnNatural.forAll
    yield Result.diff(BigInt(NaturalArithmetic.modulo(number.bigInteger, java.math.BigInteger.ZERO)), number)(_ == _)
  }
