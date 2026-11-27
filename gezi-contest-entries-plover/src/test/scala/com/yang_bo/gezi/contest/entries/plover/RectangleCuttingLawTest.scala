package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.contest.natives.plover.RectangleCutting
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the rectangle's cuts: the native's value is what the recursion
  * gives, with the pieces of each first cut as the program names them. Its
  * purpose is to catch the two reductions the table makes and the definition
  * does not, taking the shorter side as the height and trying only the cuts up
  * to half a side, including on a side of one and on a square.
  */
class RectangleCuttingLawTest extends GeneratedProperties:

  /** The recursion as the program reads it, each rectangle read once. */
  private def read(
      first: Int,
      second: Int,
      known: Map[(Int, Int), Int]
  ): (Int, Map[(Int, Int), Int]) =
    known.get((first, second)) match
      case Some(value)             => (value, known)
      case None if first == second => (0, known.updated((first, second), 0))
      case None                    =>
        val pieces =
          (1 until first).map(cut => ((cut, second), (first - cut, second))) ++
            (1 until second).map(cut => ((cut, first), (second - cut, first)))
        val (least, after) = pieces.foldLeft((Int.MaxValue, known)) {
          case ((best, table), ((a, b), (c, d))) =>
            val (left, afterLeft) = read(a, b, table)
            val (right, afterRight) = read(c, d, afterLeft)
            (math.min(best, 1 + left + right), afterRight)
        }
        (least, after.updated((first, second), least))

  property("the cuts are what the recursion gives") {
    for
      first <- Gen.int(Range.linear(1, 16)).forAll
      second <- Gen.int(Range.linear(1, 16)).forAll
    yield
      val computed = RectangleCutting.cuts(
        BigInteger.valueOf(first.toLong),
        BigInteger.valueOf(second.toLong)
      )
      Result.diff(computed.intValueExact, read(first, second, Map.empty)._1)(
        _ == _
      )
  }
