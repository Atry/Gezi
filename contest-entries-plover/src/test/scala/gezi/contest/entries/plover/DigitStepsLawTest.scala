package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.contest.natives.plover.DigitSteps
import gezi.generatedinputs.GeneratedProperties

/** The law of the fewest digit steps: the native's count is the least length
  * among all the step sequences from the number to zero, enumerated by the
  * definition. Its purpose is to catch a zero digit taken as a step, a digit
  * missed, an off-by-one in the table, and a greedy shortcut that is not the
  * least.
  */
class DigitStepsLawTest extends GeneratedProperties:

  private def digits(number: Int): Vector[Int] =
    number.toString.toVector.map(_.asDigit)

  /** The length of every step sequence from the number to zero. */
  private def lengths(number: Int): Vector[Int] =
    if number == 0 then Vector(0)
    else digits(number).filter(_ != 0).flatMap(digit => lengths(number - digit).map(_ + 1))

  property("the count is the least length of the enumerated step sequences") {
    for number <- Gen.int(Range.linear(0, 45)).forAll
    yield Result.diff(DigitSteps.count(BigInteger.valueOf(number)).intValueExact, lengths(number).min)(_ == _)
  }
