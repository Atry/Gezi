package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The edit distance of two lists, the value of the definition it replaces, the
  * typed version `plover_typed_edit_distance`, whose recursion reads the two
  * suffixes: an empty suffix costs the other's length, equal first characters
  * cost the distance of the rests, and different ones one more than the least
  * of the three smaller pairs. The table is that recursion's, over the lists
  * reversed, so that a suffix of a list is a prefix of its reverse. It takes
  * O(first * second) cells and keeps one row.
  *
  * The characters are canonical naturals, which is what the native's places
  * declare, and a narrow block compiles the call only when the filters at the
  * operands' roots name them. A native does not check its operands
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
object EditDistance:

  /** The edit distance of the two lists. */
  def distance(
      first: Vector[BigInteger],
      second: Vector[BigInteger]
  ): BigInteger =
    val numbers = (first ++ second).distinct.zipWithIndex.toMap
    val firstReversed = IArray.from(first.reverseIterator.map(numbers))
    val secondReversed = IArray.from(second.reverseIterator.map(numbers))
    val emptyFirst = IArray.range(0, secondReversed.length + 1)
    val lastRow = IArray.range(0, firstReversed.length).foldLeft(emptyFirst) {
      (before, index) =>
        rowAfter(before, firstReversed(index), index + 1, secondReversed)
    }
    BigInteger.valueOf(lastRow(secondReversed.length).toLong)

  /** The row of a first suffix of `length` characters, from the row of the
    * suffix one shorter and the character that extends it.
    */
  private def rowAfter(
      before: IArray[Int],
      character: Int,
      length: Int,
      second: IArray[Int]
  ): IArray[Int] =
    IArray.range(0, second.length).scanLeft(length) { (inserted, position) =>
      val substituted = before(position)
      if character == second(position) then substituted
      else 1 + math.min(substituted, math.min(before(position + 1), inserted))
    }
