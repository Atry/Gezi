package com.yang_bo.gezi.interfacelaws

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.jit.Jit
import com.yang_bo.gezi.jit.JitTesting
import com.yang_bo.gezi.standardlibrary.SplitMix
import com.yang_bo.gezi.weakhead.NoJitState

/** The law of the reader interface `JitEvaluator`, run on any implementation: a
  * suite that extends this class with the implementation of the facts checks it
  * ([[com.yang_bo.gezi.interfacelaws]]). At a generated closed term with choices and
  * parallels and no library name, where the reference reader weak_head and the
  * evaluator both finish, the evaluator reads the parallel sets weak_head
  * reads, encoded whole (`JitEvaluator.heads` and `encoded`), compared as sets
  * of parallel sets, so that neither the order of the sets nor the order of a
  * set's heads is compared (`ParallelSet`'s equality), by the comparison
  * protocol of `JitTesting.comparison`: one side that finishes within the limit
  * and the other not is read again within the larger limit. A term neither
  * finishes on is no counterexample. Its purpose is to catch a reader that
  * loses or adds a parallel set where both readers finish, which no other test
  * of a replacement would catch before a round's points did.
  */
abstract class JitEvaluatorLaws(
    evaluatorOf: JitTesting.noFactsEncoding.type => Jit[
      JitTesting.noFactsEncoding.type
    ]
) extends GeneratedProperties:

  /** The configuration of the laws' terms: the encoding of the facts of no
    * library.
    */
  private type E = JitTesting.noFactsEncoding.type

  private given E = JitTesting.noFactsEncoding

  property(
    "where weak_head and the evaluator both finish, they read the same parallel sets"
  ) {
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      size <- Gen.int(Range.linear(2, 24)).forAll
    yield
      val (term, _) = JitTesting.randomLatticeApplication(size, SplitMix(seed))
      val value = JitTesting.instructionValue(JitTesting.instructionOf[E](term))
      val question =
        JitTesting.headsQuestion(evaluatorOf(JitTesting.noFactsEncoding), value)
      JitTesting
        .comparison(
          question,
          JitEvaluatorLaws.limit,
          NoJitState,
          cacheDropped = true
        )
        .disagreement match
        case None                   => Result.success
        case Some((read, expected)) =>
          Result.failure.log(
            s"at $term the evaluator read $read where weak_head read $expected"
          )
  }

object JitEvaluatorLaws:

  /** The steps of a first reading, `JitTest`'s on its random terms. */
  val limit: Long = 200000
