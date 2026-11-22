package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.OrderedCompositions
import gezi.generatedinputs.GeneratedProperties

/** The law of the ordered compositions: the native's count is the number
  * of ordered sequences of the items that sum to the target, enumerated by the
  * definition, reduced modulo the modulus. Its purpose is to catch an
  * off-by-one in the table, an item larger than the distance read out of
  * range, a duplicate item counted once, and a difference between the `Long`
  * path and the `BigInteger` path, which the two moduli of the law both reach.
  */
class OrderedCompositionsLawTest extends GeneratedProperties:

  /** The sequences summing to the remainder, counted one by one. */
  private def enumerated(items: Vector[Int], remainder: Int): BigInt =
    if remainder < 0 then BigInt(0)
    else if remainder == 0 then BigInt(1)
    else items.map(item => enumerated(items, remainder - item)).sum

  private val drawnItems: Gen[Vector[Int]] =
    Gen.int(Range.linear(1, 6)).list(Range.linear(0, 4)).map(_.toVector)

  private val drawnModulus: Gen[BigInt] =
    Gen.choice1(
      Gen.int(Range.linear(1, 1000)).map(BigInt(_)),
      Gen.int(Range.linear(0, 1000)).map(offset => BigInt(2).pow(70) + BigInt(offset))
    )

  // The enumeration makes up to 4^9 = 262,144 calls, at four items of value 1 and the target 9.
  property("the count is the enumerated sequences modulo the modulus") {
    for
      items <- drawnItems.forAll
      target <- Gen.int(Range.linear(0, 9)).forAll
      modulus <- drawnModulus.forAll
    yield
      val counted = OrderedCompositions.count(
        items.map(BigInteger.valueOf(_)),
        BigInteger.valueOf(target),
        modulus.bigInteger
      )
      Result.diff(BigInt(counted), enumerated(items, target) % modulus)(_ == _)
  }
