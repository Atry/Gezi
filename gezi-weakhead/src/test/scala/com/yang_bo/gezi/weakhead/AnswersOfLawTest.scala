package com.yang_bo.gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.standardlibrary.SplitMix

/** The law of `Answers.of`: the stream of a vector's answers, collected, is the
  * vector, the same answers in the same order. Its purpose is to catch a
  * construction that grows the call stack with the vector's size, which
  * overflowed an entry's main thread on the 2,917 heads of one tabled instance
  * of the JIT (2026-11-02), and one that drops, repeats or reorders an answer.
  * The vectors are of random sizes up to 100,000, with random longs as answers,
  * under the tests' default stack.
  */
class AnswersOfLawTest extends GeneratedProperties:

  private val vectors =
    for
      size <- Gen.int(Range.linear(0, 100000))
      seed <- Gen.long(Range.linear(Long.MinValue, Long.MaxValue))
    yield Vector.unfold((size, SplitMix(seed)))((remaining, random) =>
      if remaining == 0 then None
      else
        val (bits, next) = random.bits
        Some((bits, (remaining - 1, next)))
    )

  property("Answers.of collects to its vector", _.copy(testLimit = 20)) {
    for answers <- vectors.forAll
    yield Answers.of[Unit, Long](answers).collected.result(()) match
      case Computed.Done(collected, _) =>
        Result.diff(collected, answers)(_ == _)
      case Computed.Stopped(_) =>
        Result.failure.log("a computation with no budget stopped")
  }
