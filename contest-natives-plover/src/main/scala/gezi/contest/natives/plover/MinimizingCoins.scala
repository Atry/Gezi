package gezi.contest.natives.plover

import java.math.BigInteger
import gezi.jit.ConstructedNaturals

/** The fewest coins whose values sum to a target, each usable any number of
  * times, or none when no coins do, the value of the definition it replaces,
  * the typed version `plover_typed_minimizing_coins`, by the recurrence f(0) =
  * 0 and f(s) = 1 + the least f(s - c) over the coins c no larger than s, in
  * O(target * coins) steps. The value is the option family's: none at position
  * 0 and some of the count at position 1.
  *
  * The coins are positive and the target is a natural, which is what the
  * native's places declare; a native does not check its operands
  * (`CONTRIBUTING.md`, "Types live only in the term"). A target beyond an `Int`
  * is more cells than a table holds, and `intValueExact` throws
  * `ArithmeticException` on it.
  */
object MinimizingCoins:

  private val unreachable: Int = Int.MaxValue

  /** The option of the fewest coins. */
  def fewest(
      coins: Vector[BigInteger],
      target: BigInteger
  ): ConstructedNaturals =
    val distance = target.intValueExact
    val values = coins
      .filter(_.compareTo(target) <= 0)
      .map(_.intValueExact)
      .distinct
      .sorted
    val table = (1 to distance).foldLeft(Vector(0)) { (cells, sum) =>
      @scala.annotation.tailrec
      def least(index: Int, found: Int): Int =
        if index == values.size || values(index) > sum then found
        else
          val before = cells(sum - values(index))
          least(
            index + 1,
            if before != unreachable && before + 1 < found then before + 1
            else found
          )
      cells :+ least(0, unreachable)
    }
    if table(distance) == unreachable then ConstructedNaturals(0, Vector.empty)
    else
      ConstructedNaturals(1, Vector(BigInteger.valueOf(table(distance).toLong)))
