package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of the seeded order: the same seed gives the same order, and the
  * order is a permutation of the elements. Its purpose is to catch a shuffle
  * that reads state outside its arguments (entries would read different
  * orders), or one that drops or repeats an element (a point read twice or
  * never).
  */
class SeededOrderLawTest extends GeneratedProperties:

  private val elements: Gen[Vector[Int]] =
    Gen.int(Range.linear(0, 1000)).list(Range.linear(0, 40)).map(_.toVector)

  property("the same seed gives the same order") {
    for
      found <- elements.forAll
      seed <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .forAll
    yield Result.diff(
      SeededOrder.shuffled(found, seed),
      SeededOrder.shuffled(found, seed)
    )(_ == _)
  }

  property("the order is a permutation of the elements") {
    for
      found <- elements.forAll
      seed <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .forAll
    yield Result.diff(
      SeededOrder.shuffled(found, seed)._1.sorted,
      found.sorted
    )(_ == _)
  }
