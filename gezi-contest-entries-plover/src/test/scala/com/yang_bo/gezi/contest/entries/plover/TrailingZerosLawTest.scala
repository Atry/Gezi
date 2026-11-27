package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.contest.natives.plover.TrailingZeros
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the trailing zeros: the native's value is the number of decimal
  * zeros that end the factorial, as the definition counts them. Its purpose is
  * to catch a formula wrong at a power of five, where the count jumps by more
  * than one, and at zero, whose factorial is one.
  */
class TrailingZerosLawTest extends GeneratedProperties:

  @scala.annotation.tailrec
  private def zeros(number: BigInt, count: Int): Int =
    if number % 10 != 0 then count else zeros(number / 10, count + 1)

  property("the count is the decimal zeros that end the factorial") {
    for number <- Gen.int(Range.linear(0, 700)).forAll
    yield
      val factorial = (1 to number).foldLeft(BigInt(1))(_ * _)
      Result.diff(
        BigInt(TrailingZeros.count(BigInt(number).bigInteger)),
        BigInt(zeros(factorial, 0))
      )(_ == _)
  }
