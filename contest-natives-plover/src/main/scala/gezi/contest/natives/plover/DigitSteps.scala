package gezi.contest.natives.plover

import java.math.BigInteger

/** The fewest steps that take a natural to zero, a step subtracting one of the
  * nonzero decimal digits of the current number, by the recurrence f(0) = 0 and
  * f(n) = 1 + the least f(n - d) over the nonzero digits d of n, the value of
  * the definition it replaces, the typed version `plover_typed_digit_steps`. It
  * takes O(number * digits) table reads.
  *
  * The operand is a canonical natural, which is what the native's place
  * declares. A native does not check its operands (`CONTRIBUTING.md`, "Types
  * live only in the term"). A number beyond an `Int` is more cells than a table
  * holds, and `intValueExact` throws `ArithmeticException` on it.
  */
object DigitSteps:

  /** f(number). */
  def count(number: BigInteger): BigInteger =
    val last = number.intValueExact
    val table = (1 to last).foldLeft(Vector(0)) { (steps, value) =>
      steps :+ (1 + leastAfterDigits(steps, value, value, Int.MaxValue))
    }
    BigInteger.valueOf(table(last).toLong)

  /** The least f(value - d) over the nonzero digits d of `rest`, at most
    * `least`.
    */
  @scala.annotation.tailrec
  private def leastAfterDigits(
      steps: Vector[Int],
      value: Int,
      rest: Int,
      least: Int
  ): Int =
    if rest == 0 then least
    else
      val digit = rest % 10
      leastAfterDigits(
        steps,
        value,
        rest / 10,
        if digit == 0 then least else math.min(least, steps(value - digit))
      )
