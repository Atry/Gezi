package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The two options of `ContinuationReading` on generated programs in
  * continuation passing style (`ContinuationPrograms`), read by
  * `tabling(weak_head)` under the extremes of the contest's readings (top a
  * greatest term, `KnownExtremes.onlyTop`).
  *
  * The first law: where both readings finish, every parallel set `Packed` reads
  * is one `Substituted` reads. `Substituted` is the β rule as it is, so a set
  * `Packed` adds would be an answer of no path of the program. Its purpose:
  * catch a `Packed` reading that keeps an answer of a branch whose step did not
  * pass the check, that reads a pack's tuple of a head that is not one, or that
  * misplaces a field of the tuple in the continuation.
  *
  * The second law: on programs whose every step calls its continuation in tail
  * position at the step's arity, the two readings read the same parallel sets
  * where both finish. Its purpose: catch a `Packed` reading that loses an
  * answer where the condition holds, such as a branch dropped with no head
  * marked, so that no fallback restores it, which the first law cannot see (the
  * review of https://github.com/Atry/private-overlay/pull/1798).
  */
class ContinuationReadingLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  /** The steps of one reading, `ApplicationReadingLawTest`'s limit. */
  private val limit: Long = 20000

  private def heads(
      term: Configured[NoFacts.type],
      continuations: ContinuationReading
  ): Bounded[Vector[ParallelSet[NoFacts.type]]] =
    val start = ReadingState
      .knowingTop(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
      .copy(continuations = continuations)
    WeakHead
      .heads(Mode.TablingWeakHead, gezi.ir.Value.of(term))
      .collected
      .result(start) match
      case Computed.Done(found, _) => Bounded.Finished(found)
      case Computed.Stopped(after) => EvaluatorTesting.stopped(after)

  property("packedReadsNoParallelSetSubstitutedDoesNotWhereBothFinish") {
    for program <- ContinuationPrograms.programs.forAll
    yield
      val term = EvaluatorTesting.instructionOf(program)
      (
        heads(term, ContinuationReading.Substituted),
        heads(term, ContinuationReading.Packed)
      ) match
        case (Bounded.Finished(substituted), Bounded.Finished(packed)) =>
          Result.diff(
            packed.toSet -- substituted.toSet,
            Set.empty[ParallelSet[NoFacts.type]]
          )(_ == _)
        case _ => Result.success
  }

  property("packedReadsWhatSubstitutedReadsOnTailProgramsWhereBothFinish") {
    for program <- ContinuationPrograms.tailPrograms.forAll
    yield
      val term = EvaluatorTesting.instructionOf(program)
      (
        heads(term, ContinuationReading.Substituted),
        heads(term, ContinuationReading.Packed)
      ) match
        case (Bounded.Finished(substituted), Bounded.Finished(packed)) =>
          Result.diff(packed.toSet, substituted.toSet)(_ == _)
        case _ => Result.success
  }
