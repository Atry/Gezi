package gezi.contest.natives.plover

import java.math.BigInteger

/** The fewest cuts that leave a rectangle of positive sides in squares, the
  * value of the definition it replaces, the typed version
  * `plover_typed_rectangle_cutting`, by a table over the rectangles up to it.
  * The definition is symmetric in the two sides, so the table has the shorter
  * side as its height, and a cut at c and a cut at side - c make the same two
  * pieces, so only the cuts up to half a side are tried. The operands are what
  * the native's places declare, and a native does not check them
  * (`CONTRIBUTING.md`, "Types live only in the term").
  */
object RectangleCutting:

  /** The largest first * second * (first + second) the table is built for, the
    * order of its cost: each of the first * second cells tries up to half of
    * first + second cuts. It bounds a thin rectangle as well as a square, which an
    * area alone does not.
    */
  private val largestWork: BigInteger = BigInteger.valueOf(4000000000L)

  /** The fewest cuts of the rectangle. Throws `ArithmeticException` when the
    * table's cost is above `largestWork`.
    */
  def cuts(first: BigInteger, second: BigInteger): BigInteger =
    if first.multiply(second).multiply(first.add(second)).compareTo(largestWork) > 0 then
      throw ArithmeticException(s"a table for a rectangle of $first by $second costs more than $largestWork")
    val height = first.min(second).intValue
    val width = first.max(second).intValue
    val rows = (1 to height).foldLeft(Vector.empty[IArray[Int]])((done, rowHeight) => done :+ row(done, rowHeight, width))
    BigInteger.valueOf(rows(height - 1)(width - 1).toLong)

  /** The fewest cuts of the rectangles of this height and widths 1 to `width`. */
  private def row(done: Vector[IArray[Int]], height: Int, width: Int): IArray[Int] =
    IArray.from((1 to width).foldLeft(Vector.empty[Int])((current, cellWidth) => current :+ cell(done, current, height, cellWidth)))

  /** The fewest cuts of height by width, from the rows above it and the cells
    * to its left: none for a square, and otherwise one cut at the best place.
    * A rectangle that is no square has a side of at least two, so a cut exists.
    */
  private def cell(done: Vector[IArray[Int]], current: Vector[Int], height: Int, width: Int): Int =
    if height == width then 0
    else
      @scala.annotation.tailrec
      def acrossHeight(cut: Int, least: Int): Int =
        if cut > height / 2 then least
        else acrossHeight(cut + 1, math.min(least, 1 + done(cut - 1)(width - 1) + done(height - cut - 1)(width - 1)))
      @scala.annotation.tailrec
      def acrossWidth(cut: Int, least: Int): Int =
        if cut > width / 2 then least
        else acrossWidth(cut + 1, math.min(least, 1 + current(cut - 1) + current(width - cut - 1)))
      acrossWidth(1, acrossHeight(1, Int.MaxValue))
