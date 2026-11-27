package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.Billboard
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.NaturalLattice

/** The law of the billboard: the native's term is the target's numeral exactly
  * when the definition's recursion reaches a leaf whose two sums both equal it,
  * and otherwise the choice, in increasing order, of the sums of every leaf
  * whose two sums are equal, in parallel with the target. Its purpose is to
  * catch a right answer lost, a target answered that the rods do not reach, a
  * rod used on both sides, and a height of the choice missed or added, which
  * would make the term stand for another one than the definition's.
  */
class BillboardLawTest extends GeneratedProperties:

  /** The sums of the definition's leaves whose two sums are equal, the
    * definition read as written with no table.
    */
  private def heightsByDefinition(
      rods: List[Int],
      left: Int,
      right: Int
  ): Set[Int] = rods match
    case Nil         => if left == right then Set(left) else Set.empty
    case rod :: rest =>
      heightsByDefinition(rest, left, right) ++ heightsByDefinition(
        rest,
        left + rod,
        right
      ) ++
        heightsByDefinition(rest, left, right + rod)

  private def numeral(value: Int): NaturalLattice =
    NaturalLattice.Numeral(BigInteger.valueOf(value))

  property(
    "the native's term is the target when the recursion reaches it, and the heights in parallel with it otherwise"
  ) {
    for
      rods <- Gen.list(Gen.int(Range.linear(1, 9)), Range.linear(0, 7)).forAll
      target <- Gen.int(Range.linear(0, 16)).forAll
    yield
      val term = Billboard.term(
        rods.toVector.map(rod => BigInteger.valueOf(rod)),
        BigInteger.valueOf(target)
      )
      val heights = heightsByDefinition(rods, 0, 0)
      val expected =
        if heights.contains(target) then numeral(target)
        else
          NaturalLattice.Parallel(
            NaturalLattice.Choice(heights.toVector.sorted.map(numeral)),
            numeral(target)
          )
      Result.diff(term, expected)(_ == _)
  }
