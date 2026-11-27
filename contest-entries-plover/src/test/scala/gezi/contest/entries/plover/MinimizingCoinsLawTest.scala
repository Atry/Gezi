package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.MinimizingCoins
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.ConstructedNaturals

/** The law of the fewest coins: the native's value is the least length of the
  * sequences of coins that sum to the target, every sequence walked as the
  * definition walks them, none when there is none. Its purpose is to catch a
  * target no coins reach, a target of zero (the empty sequence), an empty list
  * of coins, a coin above the target and a coin listed twice.
  */
class MinimizingCoinsLawTest extends GeneratedProperties:

  private def lengths(coins: List[Int], remaining: Int): List[Int] =
    if remaining < 0 then Nil
    else if remaining == 0 then List(0)
    else coins.flatMap(coin => lengths(coins, remaining - coin).map(_ + 1))

  private val drawnCoins: Gen[List[Int]] =
    Gen.choice1(
      Gen.constant(Nil),
      Gen.int(Range.linear(2, 9)).list(Range.linear(1, 3)),
      Gen.int(Range.linear(1, 6)).list(Range.linear(1, 3))
    )

  property(
    "the value is the least length of a sequence that sums to the target"
  ) {
    for
      coins <- drawnCoins.forAll
      target <- Gen.int(Range.linear(0, 13)).forAll
    yield
      val expected = lengths(coins, target).minOption match
        case None        => ConstructedNaturals(0, Vector.empty)
        case Some(count) =>
          ConstructedNaturals(1, Vector(BigInteger.valueOf(count.toLong)))
      Result.diff(
        MinimizingCoins.fewest(
          coins.toVector.map(coin => BigInteger.valueOf(coin.toLong)),
          BigInteger.valueOf(target.toLong)
        ),
        expected
      )(_ == _)
  }
