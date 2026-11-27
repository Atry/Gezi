package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.UnorderedCombinations
import gezi.generatedinputs.GeneratedProperties

/** The law of the unordered combinations: the native's count is the number of
  * ways enumerated by the definition, each a sequence of items that never moves
  * back along the list, reduced modulo the modulus. Its purpose is to catch an
  * order counted twice, an off-by-one in a residue class, an item larger than
  * the target read out of range, a duplicate item counted once, and a
  * difference between the `Long` path and the `BigInteger` path, which the two
  * moduli of the law both reach.
  */
class UnorderedCombinationsLawTest extends GeneratedProperties:

  /** The ways to cover the remainder with the suffix of the items, counted one
    * by one.
    */
  private def enumerated(suffix: Vector[Int], remainder: Int): BigInt =
    if remainder < 0 then BigInt(0)
    else if remainder == 0 then BigInt(1)
    else
      suffix.indices
        .map(start => enumerated(suffix.drop(start), remainder - suffix(start)))
        .sum

  private val drawnItems: Gen[Vector[Int]] =
    Gen.int(Range.linear(1, 6)).list(Range.linear(0, 4)).map(_.toVector)

  private val drawnModulus: Gen[BigInt] =
    Gen.choice1(
      Gen.int(Range.linear(1, 1000)).map(BigInt(_)),
      Gen
        .int(Range.linear(0, 1000))
        .map(offset => BigInt(2).pow(70) + BigInt(offset))
    )

  property("the count is the enumerated ways modulo the modulus") {
    for
      items <- drawnItems.forAll
      target <- Gen.int(Range.linear(0, 12)).forAll
      modulus <- drawnModulus.forAll
    yield
      val counted = UnorderedCombinations.count(
        items.map(BigInteger.valueOf(_)),
        BigInteger.valueOf(target),
        modulus.bigInteger
      )
      Result.diff(BigInt(counted), enumerated(items, target) % modulus)(_ == _)
  }
