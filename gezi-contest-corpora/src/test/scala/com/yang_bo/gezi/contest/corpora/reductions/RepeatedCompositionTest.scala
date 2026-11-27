package com.yang_bo.gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import com.yang_bo.gezi.weakhead.Mode

/** The tests of a stage one family (`RepeatedCompositions.scala`): the law and
  * the snapshot of `RepeatedVariantSuite`, read under tabling(weak_head), and
  * one property more.
  *
  * The property, whose purpose is to catch a family whose sites share their
  * data, so that a site's answer could be copied from another's instead of
  * computed: on generated seeds and R from 1 to 256, the R sites' data
  * (`RepeatedComposition.siteData`, each site's data as one Scott list) are
  * pairwise distinct terms.
  *
  * The steps at each class are the untabled weak head's
  * (`NormalForms.normalForms` under `Mode.WeakHead` from a fresh state, the
  * reading the law took when they were measured) at R = 6, the largest R the
  * law draws: for the practice seed 20261031, and the largest and the median
  * over 30 seeds of a fixed scratch sequence, which is not in the repository;
  * none stopped within `Decoding.limit`. The practice seed's readings at R = 64
  * and R = 256 are given beside them to show the growth in R (measured
  * 2026-10-31 at -Xmx256m).
  */
abstract class RepeatedCompositionSuite(
    family: RepeatedComposition,
    snapshotName: String
) extends RepeatedVariantSuite(family, Mode.TablingWeakHead, snapshotName):

  property("the sites' data are pairwise distinct", _.copy(testLimit = 30)) {
    for
      seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
      repetitions <- Gen
        .int(hedgehog.Range.constant(1, Repetition.repetitions.end))
        .forAll
    yield
      val data = family
        .siteData(ReductionTesting.group, seed, repetitions)
        .map(Encodings.deBruijn)
      Result
        .assert(data.size == repetitions)
        .log(s"${data.size} sites for $repetitions repetitions")
        .and(
          Result
            .assert(data.distinct.size == data.size)
            .log(s"${data.size - data.distinct.size} sites repeat a datum")
        )
  }

/** Steps at R = 6: 3,915 for the practice seed; largest 115,148 and median
  * 5,169 over 30 seeds. The practice seed at R = 64: 40,848; at R = 256:
  * 161,933.
  */
class RepeatedIdenticalSubtermsDirectTest
    extends RepeatedCompositionSuite(
      RepeatedIdenticalSubterms(Spelling.Direct),
      "identical_subterms_direct"
    )

/** Steps at R = 6: 5,800 for the practice seed; largest 164,752 and median
  * 5,592 over 30 seeds. The practice seed at R = 64: 64,548; at R = 256:
  * 257,986.
  */
class RepeatedIdenticalSubtermsRespelledTest
    extends RepeatedCompositionSuite(
      RepeatedIdenticalSubterms(Spelling.Respelled),
      "identical_subterms_respelled"
    )

/** Steps at R = 6: 1,190 for the practice seed; largest 180,482 and median
  * 5,842 over 30 seeds. The practice seed at R = 64: 12,340; at R = 256:
  * 51,756.
  */
class RepeatedClosuresDirectTest
    extends RepeatedCompositionSuite(
      RepeatedClosures(Spelling.Direct),
      "closures_direct"
    )

/** Steps at R = 6: 173,313 for the practice seed; largest 283,214 and median
  * 6,300 over 30 seeds. The practice seed at R = 64: 2,158,404; at R = 256:
  * 8,714,049.
  */
class RepeatedClosuresRespelledTest
    extends RepeatedCompositionSuite(
      RepeatedClosures(Spelling.Respelled),
      "closures_respelled"
    )

/** Steps at R = 6: 1,009 for the practice seed; largest 53,066 and median 2,878
  * over 30 seeds. The practice seed at R = 64: 7,977; at R = 256: 31,660.
  */
class RepeatedLibraryCompositionsDirectTest
    extends RepeatedCompositionSuite(
      RepeatedLibraryCompositions(Spelling.Direct),
      "library_compositions_direct"
    )

/** Steps at R = 6: 45,905 for the practice seed; largest 141,586 and median
  * 5,429 over 30 seeds. The practice seed at R = 64: 441,449; at R = 256:
  * 1,736,498.
  */
class RepeatedLibraryCompositionsRespelledTest
    extends RepeatedCompositionSuite(
      RepeatedLibraryCompositions(Spelling.Respelled),
      "library_compositions_respelled"
    )

/** Steps at R = 6: 772 for the practice seed; largest 171,370 and median 2,942
  * over 30 seeds. The practice seed at R = 64: 9,674; at R = 256: 39,729.
  */
class RepeatedGeneralCompositionsDirectTest
    extends RepeatedCompositionSuite(
      RepeatedGeneralCompositions(Spelling.Direct),
      "general_compositions_direct"
    )

/** Steps at R = 6: 1,096 for the practice seed; largest 136,254 and median
  * 2,152 over 30 seeds. The practice seed at R = 64: 13,266; at R = 256:
  * 51,696.
  */
class RepeatedGeneralCompositionsRespelledTest
    extends RepeatedCompositionSuite(
      RepeatedGeneralCompositions(Spelling.Respelled),
      "general_compositions_respelled"
    )

/** Steps at R = 6: 1,339 for the practice seed; largest 118,039 and median
  * 4,411 over 30 seeds. The practice seed at R = 64: 15,996; at R = 256:
  * 64,337.
  */
class RepeatedNestedCompositionsDirectTest
    extends RepeatedCompositionSuite(
      RepeatedNestedCompositions(Spelling.Direct),
      "nested_compositions_direct"
    )

/** Steps at R = 6: 2,445 for the practice seed; largest 484,124 and median
  * 6,135 over 30 seeds. The practice seed at R = 64: 27,458; at R = 256:
  * 116,134.
  */
class RepeatedNestedCompositionsRespelledTest
    extends RepeatedCompositionSuite(
      RepeatedNestedCompositions(Spelling.Respelled),
      "nested_compositions_respelled"
    )
