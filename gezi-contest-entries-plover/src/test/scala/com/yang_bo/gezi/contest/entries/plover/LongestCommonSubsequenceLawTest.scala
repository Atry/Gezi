package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.contest.natives.plover.LongestCommonSubsequence
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the longest common subsequence: the native's value is the value
  * of the recursion the program writes, on the two suffixes. Its purpose is to
  * catch a table that reads the lists in the wrong direction, a wrong boundary
  * row or column, and characters compared by reference instead of by number.
  */
class LongestCommonSubsequenceLawTest extends GeneratedProperties:

  /** The definition, read as written, with no table. */
  private def byDefinition(first: List[Int], second: List[Int]): Int =
    (first, second) match
      case (Nil, _) | (_, Nil)                           => 0
      case (character :: firstRest, other :: secondRest) =>
        if character == other then 1 + byDefinition(firstRest, secondRest)
        else
          math.max(
            byDefinition(firstRest, second),
            byDefinition(first, secondRest)
          )

  property("the length is the value of the recursion on the two suffixes") {
    val strings = Gen.list(Gen.int(Range.linear(0, 3)), Range.linear(0, 7))
    for
      first <- strings.forAll
      second <- strings.forAll
    yield
      // Each item a new object, so that a comparison by reference would find no equal characters.
      val items = (values: List[Int]) =>
        values.toVector.map(value => new BigInteger(value.toString))
      Result.diff(
        LongestCommonSubsequence
          .length(items(first), items(second))
          .intValueExact,
        byDefinition(first, second)
      )(_ == _)
  }
