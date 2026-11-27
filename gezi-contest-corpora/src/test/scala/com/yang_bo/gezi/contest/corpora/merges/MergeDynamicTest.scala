package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.frontend.Term

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_merge_dynamic.plt`) that read programs
  * on the judge under tabling(weak_head), against the references of the deleted
  * Prolog file (`git show
  * 6ab16a338^:lambda_jit/corpora/contest_dynamic_references.pl`) (the reduction
  * group's port).
  */
class MergeDynamicEndingsTest extends MergeProblemsSuite:
  import com.yang_bo.gezi.weakhead.Mode
  import com.yang_bo.gezi.contest.corpora.claims.Ending
  import com.yang_bo.gezi.contest.corpora.reductions.DynamicReferences

  private val dynamic = MergeDynamic(MergeTesting.problems)

  private def ending(term: Term): Ending =
    ClaimEndings.trueEnding(Mode.TablingWeakHead, term)

  test("gridPathsAgreeWithTheReference") {
    Vector(0, 1, 2, 3).foreach(size =>
      val count = DynamicReferences.referenceGridPaths(size, size)
      assertEquals(
        (size, ending(dynamic.gridTerm(size, count))),
        (size, Ending.Succeeded)
      )
      assertEquals(
        (size, ending(dynamic.gridTerm(size, count + 8))),
        (size, Ending.Failed)
      )
    )
  }

  test("subsetSumsAgreeWithTheReference") {
    val items = Vector(3, 5, 7)
    val sums = DynamicReferences.referenceSubsetSums(items)
    (0 to 16).foreach(target =>
      val expected =
        if sums.contains(target) then Ending.Succeeded else Ending.Failed
      assertEquals(
        (target, ending(dynamic.subsetTerm(items.map(BigInt(_)), target))),
        (target, expected)
      )
    )
  }

  test("lcsAgreesWithTheReference") {
    Vector(("ab", "ba"), ("aab", "abb"), ("bab", "aba")).foreach(
      (leftText, rightText) =>
        val (left, right) = (leftText.toVector, rightText.toVector)
        val length =
          DynamicReferences.referenceLongestCommonSubsequence(left, right)
        assertEquals(
          (leftText, rightText, ending(dynamic.lcsTerm(left, right, length))),
          (leftText, rightText, Ending.Succeeded)
        )
        assertEquals(
          (
            leftText,
            rightText,
            ending(dynamic.lcsTerm(left, right, length + 1))
          ),
          (leftText, rightText, Ending.Failed)
        )
    )
  }
