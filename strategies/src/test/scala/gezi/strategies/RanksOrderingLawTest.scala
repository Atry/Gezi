package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law of `OrderValue.ranksOrdering`: on two vectors of ranks it orders
  * them as the standard order orders the Prolog lists of their elements,
  * `OrderValue.list(left*)` against `OrderValue.list(right*)`, which is its
  * definition. Its purpose is to catch a comparison that, compared element by
  * element without making the lists,
  * orders a proper
  * prefix, or the first differing element, otherwise than the lists do.
  */
class RanksOrderingLawTest extends GeneratedProperties:

  /** Values of the standard order: numbers, atoms, and compounds of up to
    * two arguments, a few levels deep, from small alphabets so that ties and
    * shared prefixes occur.
    */
  private def value(depth: Int): Gen[OrderValue] =
    val leaves = Gen.choice1(
      Gen.int(Range.linear(-3, 3)).map(OrderValue.number),
      Gen.element1("a", "b", "[]").map(OrderValue.Atom(_))
    )
    if depth == 0 then leaves
    else
      Gen.frequency1(
        2 -> leaves,
        1 -> (for
          name <- Gen.element1("f", "g", "[|]")
          arguments <- value(depth - 1).list(Range.linear(0, 2))
        yield OrderValue.Compound(name, arguments.toVector))
      )

  private val ranks: Gen[Vector[OrderValue]] = value(2).list(Range.linear(0, 4)).map(_.toVector)

  property("the ranks ordering orders two vectors as the standard order orders their lists") {
    for
      left <- ranks.forAll
      right <- Gen.choice1(ranks, Gen.constant(left), ranks.map(suffix => left ++ suffix)).forAll
    yield
      val expected = Integer.signum(OrderValue.ordering.compare(OrderValue.list(left*), OrderValue.list(right*)))
      val obtained = Integer.signum(OrderValue.ranksOrdering.compare(left, right))
      Result.diff(obtained, expected)(_ == _).log(s"$left against $right")
  }
