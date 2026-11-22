package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.hotspot.ExpansionSource
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Instruction

/** The options of `ParallelReading` on generated closed terms, read under
  * tabling(weak_head) with top a known greatest term (`KnownExtremes.onlyTop`).
  *
  * `HeadsMet` merges the lambda heads of one code in a parallel set and drops
  * a set whose heads apply different binders, which may lose answers and adds
  * none, so where both readings finish its normal forms are among
  * `BothSides`'s, also for a pair of heads that clash applied to arguments
  * that make them agree, where it loses them. A parity fold over a Scott list
  * of booleans filtered at each call by the list type of the boolean type
  * reads under `HeadsMet` the normal form of the fold over the unfiltered
  * list, in steps linear in the list's length.
  */
class ParallelReadingLawTest extends GeneratedProperties:

  /** The steps of one reading, `ApplicationReadingLawTest`'s limit for the
    * laws of `sharedLimit`'s kind (a choice step costs its members).
    */
  private val limit: Long = 2000

  /** `λx₁ … λxₙ. body(x₁ … xₙ)`. */
  private def abstraction(binders: Int, body: Vector[Term] => Term): Term =
    def under(bound: Vector[Term]): Term =
      if bound.size == binders then body(bound) else λ(variable => under(bound :+ variable))
    under(Vector.empty)

  private def closed(instruction: Instruction): Term = Term.closed(instruction)

  /** Two heads of as many binders, each an application of one of its
    * binders (the same one or two different ones), or of a captured closed
    * term, to generated arguments, in parallel, applied to generated
    * arguments: the sets `HeadsMet` merges (one code, other fillings) or
    * drops (two binders), and keeps (a captured head, which is no binder), in
    * contexts that may make the two heads agree, such as the proofs file's
    * (K* ∥ K) Ω Ω.
    */
  private val clashes: Gen[Instruction] =
    val argument = HoasGenerators.evaluatorInstruction(3).map(closed)
    def head(binders: Int): Gen[Term] =
      for
        applied <- Gen.int(Range.constant(0, binders))
        captured <- argument
        arguments <- argument.list(Range.linear(0, 2))
      yield abstraction(
        binders,
        bound => arguments.foldLeft(if applied < binders then bound(applied) else captured)(_(_))
      )
    for
      binders <- Gen.int(Range.constant(1, 3))
      first <- head(binders)
      second <- head(binders)
      arguments <- argument.list(Range.linear(0, binders))
    yield EvaluatorTesting.instructionOf(arguments.foldLeft(first ∥ second)(_(_)))

  /** Generated terms, a parallel of two generated terms at the root, and
    * clashing pairs applied to arguments.
    */
  private val terms: Gen[Instruction] =
    Gen.frequency1(
      2 -> HoasGenerators.evaluatorInstruction(8),
      1 -> (for
        left <- HoasGenerators.evaluatorInstruction(6)
        right <- HoasGenerators.evaluatorInstruction(6)
      yield Instruction.Parallel(left, right)),
      2 -> clashes
    )

  /** The normal forms and the steps of one reading. */
  private def read(term: Instruction, parallels: ParallelReading, steps: Long): Bounded[(Set[Instruction], Long)] =
    val start = ReadingState.knowingTop(steps).copy(parallels = parallels)
    NormalForms.normalForms(Mode.TablingWeakHead, term).result(start) match
      case Computed.Done(forms, after) => Bounded.Finished((forms.toSet, after.budget.spent))
      case Computed.Stopped(after)     => EvaluatorTesting.stopped(after)

  /** Purpose: catch a meet that adds an answer: fillings merged across heads
    * of different codes or holes, a filling of one head given to another, a
    * neutral head merged, or a set kept that should have been read as both
    * its heads.
    */
  property("headsMetReadsOnlyNormalFormsOfBothSidesWhereBothFinish") {
    for term <- terms.forAll
    yield (read(term, ParallelReading.BothSides, limit), read(term, ParallelReading.HeadsMet, limit)) match
      case (Bounded.Finished((bothSides, _)), Bounded.Finished((met, _))) =>
        Result.assert(met.subsetOf(bothSides)).log(s"forms both sides do not read: ${met -- bothSides}")
      case _ => Result.success
  }

  /** The parallel sets of a tabled reading, if it finished. */
  private def heads(term: Instruction, state: ReadingState): Option[Set[ParallelSet]] =
    WeakHead.heads(Mode.TablingWeakHead, term).collected.result(state) match
      case Computed.Done(sets, _) => Some(sets.toSet)
      case Computed.Stopped(_)    => None

  /** Purpose: catch a cache service that hands a `BothSides` reading the
    * tables a `HeadsMet` reading completed (a namespace that leaves the
    * parallel reading out, the review of
    * https://github.com/Atry/private-overlay/pull/1882), which would give the
    * default reading the option's lossy answers: a `BothSides` reading after
    * a `HeadsMet` reading of the same term on one service reads the heads of
    * a `BothSides` reading from no table.
    */
  property("aBothSidesReadingSharingAServiceWithAHeadsMetReadingReadsItsOwnHeads") {
    for term <- terms.forAll
    yield
      val provider = BaselineCaches.provider()
      val source = ExpansionSource.fresh()
      def shared(parallels: ParallelReading): ReadingState =
        ReadingState.knowingTop(limit).copy(sharing = TableSharing.Shared(provider, Retention.Strong, source), parallels = parallels)
      val _ = heads(term, shared(ParallelReading.HeadsMet))
      (heads(term, shared(ParallelReading.BothSides)), heads(term, ReadingState.knowingTop(limit))) match
        case (Some(found), Some(expected)) => Result.diff(found, expected)(_ == _)
        case _                             => Result.success
  }

  private val fixpoint: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))
  private val trueTerm: Term = λ(t => λ(_ => t))
  private val falseTerm: Term = λ(_ => λ(f => f))
  private val booleanType: Term = trueTerm + falseTerm
  private val nil: Term = λ(n => λ(_ => n))
  private def cons(head: Term, tail: Term): Term = λ(_ => λ(c => c(head)(tail)))
  private val listType: Term = fixpoint(λ(l => λ(_ => λ(c => c(booleanType)(l))) + nil))

  /** The parity of the list's true elements: a fold whose list is filtered
    * at each call when `isFiltered`.
    */
  private def parity(isFiltered: Boolean, list: Term): Instruction =
    val fold = fixpoint(
      λ(self =>
        λ(scrutinee =>
          (if isFiltered then scrutinee ∥ listType else scrutinee)(falseTerm)(
            λ(head => λ(tail => head(self(tail)(falseTerm)(trueTerm))(self(tail))))
          )
        )
      )
    )
    EvaluatorTesting.instructionOf(fold(list))

  /** The steps of the parity folds below: the unfiltered fold of 64 elements
    * took 1,164 and the filtered fold under `BothSides` 3,232 (2026-11-21).
    */
  private val foldLimit: Long = 100000

  /** Purpose: catch a meet that loses the list a filter admits (another
    * normal form than the unfiltered fold's), or one that still reads the
    * fold over the type itself or the tail's whole normal form at each call
    * (steps growing faster than the list). The bound is set from the steps
    * at 0, 8, 32 and 64 elements (MEASURED 2026-11-21): unfiltered 26, 173,
    * 597 and 1,164; filtered under `HeadsMet` 41, 262, 878 and 1,765; under
    * `BothSides` 190, 577, 1,713 and 3,232.
    */
  property("aFilteredParityFoldReadsTheUnfilteredFoldsFormInLinearSteps") {
    for elements <- Gen.boolean.list(Range.linear(0, 64)).forAll
    yield
      val list = elements.foldRight(nil)((element, rest) => cons(if element then trueTerm else falseTerm, rest))
      (
        read(parity(false, list), ParallelReading.HeadsMet, foldLimit),
        read(parity(true, list), ParallelReading.HeadsMet, foldLimit)
      ) match
        case (Bounded.Finished((unfiltered, unfilteredSteps)), Bounded.Finished((filtered, filteredSteps))) =>
          Result.all(
            List(
              Result.diff(unfiltered, filtered)(_ == _).log("the normal forms"),
              Result
                .assert(filteredSteps <= 2 * unfilteredSteps + 200)
                .log(s"steps: filtered $filteredSteps, unfiltered $unfilteredSteps, ${elements.size} elements")
            )
          )
        case other => Result.failure.log(s"a reading did not finish: $other")
  }
