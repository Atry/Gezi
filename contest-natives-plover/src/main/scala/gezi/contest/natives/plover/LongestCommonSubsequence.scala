package gezi.contest.natives.plover

import java.math.BigInteger

/** The length of a longest common subsequence of two lists, the value of the
  * definition it replaces, the typed version
  * `plover_typed_longest_common_subsequence`, whose recursion reads the two
  * suffixes: an empty suffix gives zero, equal first characters one more than
  * the rests, and different ones the larger of the two pairs that drop one
  * character. The table is that recursion's, over the lists reversed, so that
  * a suffix of a list is a prefix of its reverse. It takes O(first * second)
  * cells and keeps one row.
  *
  * The characters are canonical naturals, which is what the native's places
  * declare, and a narrow block compiles the call only when the filters at the
  * operands' roots name them. A native does not check its operands
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
object LongestCommonSubsequence:

  /** The length of a longest common subsequence of the two lists. */
  def length(first: Vector[BigInteger], second: Vector[BigInteger]): BigInteger =
    val numbers = (first ++ second).distinct.zipWithIndex.toMap
    val firstReversed = IArray.from(first.reverseIterator.map(numbers))
    val secondReversed = IArray.from(second.reverseIterator.map(numbers))
    val emptyFirst = IArray.fill(secondReversed.length + 1)(0)
    val lastRow = IArray.range(0, firstReversed.length).foldLeft(emptyFirst) { (before, index) =>
      rowAfter(before, firstReversed(index), secondReversed)
    }
    BigInteger.valueOf(lastRow(secondReversed.length).toLong)

  /** The row of a first suffix, from the row of the suffix one shorter and
    * the character that extends it.
    */
  private def rowAfter(before: IArray[Int], character: Int, second: IArray[Int]): IArray[Int] =
    IArray.range(0, second.length).scanLeft(0) { (secondDropped, position) =>
      if character == second(position) then before(position) + 1
      else math.max(before(position + 1), secondDropped)
    }
