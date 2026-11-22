package gezi.interfacelaws

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.BackendFacts
import gezi.jit.JitTesting
import gezi.standardlibrary.SplitMix
import gezi.weakhead.JitEvaluator
import gezi.weakhead.NoJitState
import gezi.weakhead.Values

/** The law of the reader interface `JitEvaluator`, run on any
  * implementation: a suite that extends this class with the implementation
  * of the facts checks it ([[gezi.interfacelaws]]). At a generated closed term
  * with choices and parallels and no library name, where the reference
  * reader weak_head and the evaluator both finish, the evaluator reads the
  * heads weak_head reads, in weak_head's order, encoded whole
  * (`JitEvaluator.heads` and `encoded`), by the comparison protocol of
  * `JitTesting.comparison`: one side that finishes within the limit and the
  * other not is read again within the larger limit. A term neither finishes
  * on is no counterexample. Its purpose is to catch a reader that loses,
  * adds or reorders a head, which no other test of a replacement would
  * catch before a round's points did.
  *
  * FIXME: the law fixes the order of the heads, which the https://github.com/Atry/private-overlay/issues/2037
  * vision calls an approximation's behaviour, not a program's meaning ("Its evaluation order, caching, tables, call
  * counts and where it stops are its behaviour, not what a program means", CONTRIBUTING.md, "The Vision"), so it
  * rejects any evaluator configured to read in another order. The law that holds of every sound approximation is
  * that the evaluator reads no head weak_head does not.
  */
abstract class JitEvaluatorLaws(evaluatorOf: BackendFacts => JitEvaluator) extends GeneratedProperties:

  property("where weak_head and the evaluator both finish, they read the same heads in the same order") {
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      size <- Gen.int(Range.linear(2, 24)).forAll
    yield
      val (term, _) = JitTesting.randomLatticeApplication(size, SplitMix(seed))
      val value = Values.ofInstruction(JitTesting.instructionOf(term), Set.empty)
      val question = JitTesting.headsQuestion(evaluatorOf(JitTesting.noFacts), value)
      JitTesting.comparison(question, JitEvaluatorLaws.limit, NoJitState, cacheDropped = true).disagreement match
        case None => Result.success
        case Some((read, expected)) =>
          Result.failure.log(s"at $term the evaluator read $read where weak_head read $expected")
  }

object JitEvaluatorLaws:

  /** The steps of a first reading, `JitTest`'s on its random terms. */
  val limit: Long = 200000
