package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.contest.natives.plover.ModularPower
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the modular power: the native's value is the product of the
  * exponent's copies of the base, as the definition multiplies them, reduced
  * modulo the modulus. Its purpose is to catch a wrong value at a zero base or
  * a zero exponent, where the definition gives one, and at the modulus one,
  * where every value is zero.
  */
class ModularPowerLawTest extends GeneratedProperties:

  private val drawnModulus: Gen[BigInt] =
    Gen.choice1(
      Gen.int(Range.linear(1, 1000)).map(BigInt(_)),
      Gen
        .int(Range.linear(0, 1000))
        .map(offset => BigInt(2).pow(70) + BigInt(offset))
    )

  property(
    "the power is the product of the exponent's copies of the base, modulo the modulus"
  ) {
    for
      base <- Gen.int(Range.linear(0, 12)).forAll
      exponent <- Gen.int(Range.linear(0, 24)).forAll
      modulus <- drawnModulus.forAll
    yield
      val multiplied =
        (1 to exponent).foldLeft(BigInt(1))((product, _) => product * base)
      val computed = ModularPower.power(
        BigInteger.valueOf(base),
        BigInteger.valueOf(exponent),
        modulus.bigInteger
      )
      Result.diff(BigInt(computed), multiplied % modulus)(_ == _)
  }
