package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.natives.plover.ModularTower
import gezi.generatedinputs.GeneratedProperties

/** The law of the power of a power: the native's value is the base multiplied
  * by itself the exact exponent's times, reduced modulo the modulus. Its
  * purpose is to catch the reduction of the exponent where it does not hold as
  * Fermat's theorem states it: a base that shares a factor with the modulus, a
  * multiple of a prime modulus, a zero exponent (zero to the power zero is
  * one), a modulus of one, and a prime power as modulus, where the exponent
  * must not be reduced below the prime's multiplicity.
  */
class ModularTowerLawTest extends GeneratedProperties:

  private val prime: BigInt = BigInt(1000000007)

  private val drawnModulus: Gen[BigInt] =
    Gen.element1(
      BigInt(1),
      BigInt(2),
      BigInt(12),
      BigInt(64),
      BigInt(360),
      BigInt(1024),
      BigInt(3).pow(10),
      BigInt(2).pow(20) * BigInt(3).pow(5),
      prime,
      prime * 2
    )

  private def drawnBase(modulus: BigInt): Gen[BigInt] =
    Gen.choice1(
      Gen.int(Range.linear(0, 40)).map(BigInt(_)),
      Gen.int(Range.linear(0, 3)).map(multiple => modulus * multiple),
      Gen.int(Range.linear(0, 3)).map(multiple => prime * multiple)
    )

  property(
    "the value is the base to the exact power of the power, modulo the modulus"
  ) {
    for
      modulus <- drawnModulus.forAll
      base <- drawnBase(modulus).forAll
      exponentBase <- Gen.int(Range.linear(0, 6)).forAll
      exponentPower <- Gen.int(Range.linear(0, 5)).forAll
    yield
      val exponent = BigInt(exponentBase).pow(exponentPower).toInt
      val multiplied = (1 to exponent).foldLeft(BigInt(1) % modulus)(
        (product, _) => product * base % modulus
      )
      val computed = ModularTower.power(
        base.bigInteger,
        BigInt(exponentBase).bigInteger,
        BigInt(exponentPower).bigInteger,
        modulus.bigInteger
      )
      Result.diff(BigInt(computed), multiplied)(_ == _)
  }
