package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.MoneySums
import gezi.generatedinputs.GeneratedProperties

/** The law of the money sums: the native's value is the sum of the distinct
  * sums of the nonempty subsets, every subset enumerated. Its purpose is to
  * catch a sum counted twice, the empty set's zero counted as a sum, a coin of
  * zero, and the empty list of coins, whose total is zero.
  */
class MoneySumsLawTest extends GeneratedProperties:

  private val drawnCoins: Gen[List[Int]] =
    Gen.choice1(
      Gen.constant(Nil),
      Gen.int(Range.linear(0, 40)).list(Range.linear(1, 11)),
      Gen.int(Range.linear(0, 3)).list(Range.linear(1, 11))
    )

  property(
    "the total is the sum of the distinct sums of the nonempty subsets"
  ) {
    for coins <- drawnCoins.forAll
    yield
      val distinct = coins.indices.toSet
        .subsets()
        .filter(_.nonEmpty)
        .map(_.toList.map(coins).sum)
        .toSet
      val computed = MoneySums.total(
        coins.toVector.map(coin => BigInteger.valueOf(coin.toLong))
      )
      Result.diff(BigInt(computed), BigInt(distinct.sum))(_ == _)
  }
