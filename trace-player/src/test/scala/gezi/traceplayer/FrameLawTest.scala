package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of `Frame.frame` on generated sequences and positions: a later
  * position never shows an earlier step, nor less progress within the same
  * step; the progress lies in [0, 1); and the term shown is the step's. Its
  * purpose is to catch a frame that plays backwards or skips back (a
  * rounding at a step's boundary, a clamp on the wrong side), which would make
  * the player jump while it plays.
  */
class FrameLawTest extends GeneratedProperties:

  private val terms: Gen[Vector[Int]] = Gen.int(Range.linear(0, 1000)).list(Range.linear(1, 20)).map(_.toVector)

  /** Positions around and past the sequence's ends, whole and fractional. */
  private def positions(count: Int): Gen[Double] =
    Gen.choice1(
      Gen.double(Range.linearFrac(-2.0, count + 2.0)),
      Gen.int(Range.linear(-2, count + 2)).map(_.toDouble)
    )

  property("a later position shows no earlier step and, in the same step, no less progress") {
    for
      shown <- terms.forAll
      earlier <- positions(shown.size).forAll
      later <- positions(shown.size).map(earlier + _.abs).forAll
    yield
      val before = Frame.frame(shown, earlier)
      val after = Frame.frame(shown, later)
      Result.assert(
        before.step < after.step || (before.step == after.step && before.progress <= after.progress)
      ).log(s"$before at $earlier, $after at $later")
  }

  property("the progress lies in [0, 1) and the term is the step's") {
    for
      shown <- terms.forAll
      position <- positions(shown.size).forAll
    yield
      val frame = Frame.frame(shown, position)
      Result
        .all(
          List(
            Result.assert(shown.indices.contains(frame.step)),
            Result.assert(0 <= frame.progress && frame.progress < 1),
            Result.assert(frame.term == shown(frame.step))
          )
        )
        .log(s"$frame at $position")
  }
