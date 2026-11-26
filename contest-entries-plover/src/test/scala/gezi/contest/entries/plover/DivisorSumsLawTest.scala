package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.natives.plover.DivisorSums
import gezi.generatedinputs.GeneratedProperties

/** The law of the divisor sums: the native's value is the sum, over the numbers
  * up to the limit, of their divisors found by trying every candidate, reduced
  * modulo the modulus. Its purpose is to catch a wrong run of equal quotients,
  * a product reduced wrongly, on each side of the word-sized modulus, a modulus
  * of one, and a limit of zero, whose total is zero.
  */
class DivisorSumsLawTest extends GeneratedProperties:

  private val drawnModulus: Gen[BigInt] =
    Gen.element1(
      BigInt(1),
      BigInt(2),
      BigInt(7),
      BigInt(1000000007),
      (BigInt(1) << 31) - 1,
      BigInt(1) << 31,
      BigInt(1) << 40,
      (BigInt(1) << 70) + 1
    )

  property("the total is the sum of every number's divisors, modulo the modulus") {
    for
      limit <- Gen.int(Range.linear(0, 300)).forAll
      modulus <- drawnModulus.forAll
    yield
      val summed = (1 to limit).flatMap(number => (1 to number).filter(number % _ == 0)).foldLeft(BigInt(0))(_ + _)
      val computed = DivisorSums.total(BigInt(limit).bigInteger, modulus.bigInteger)
      Result.diff(BigInt(computed), summed % modulus)(_ == _)
  }
