package gezi.weakhead

import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.weakhead.EvaluatorTesting.*

/** The laws of the whole read-out of a parallel set, whose heads are read in
  * order (`NormalForms.setRead`, 2026-11-08), on
  * generated closed terms, under `weak_head` and `tabling(weak_head)`:
  * (1) heads that finish with no common read decide the set: `(Ŝ ∥ K) ∥ m`
  * reads ∅ within a few steps more than the evaluator takes to find the
  * heads of `m`, Ŝ and K having no common normal form, so that the heads of
  * `m` are found and not read; (2) a first head the limit stops is no read
  * of ∅: `θ ∥ m`,
  * `θ = Y (λf. λx. x f)`, whose Böhm tree is infinite, so that its normal
  * form reading opens binders without end at depths no reading repeats
  * (tabling reads a term with no head, Ω's kind, as ∅ by its least fixed
  * point, and so is no witness), does not finish; (3) under `weak_head`, the whole read-out and the
  * read-out by membership read the same normal forms of `m ∥ n` wherever both
  * finish. Their purpose is to catch a short-circuit that answers ∅ for a
  * head whose reading did not finish, one that does not fire, or a whole
  * read-out of a parallel set that disagrees with the membership read-out.
  */
class ParallelEmptyLeftLawTest extends GeneratedProperties:

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private val sHat: Term = λ(x => λ(y => λ(z => x(z)(y(z)))))
  private val k: Term = λ(x => λ(_ => x))
  private def growing: Term =
    val fixedPoint = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))
    fixedPoint(λ(f => λ(x => x(f))))

  /** The steps the reading of `Ŝ ∥ K` may take beside the steps of finding
    * the other side's heads. A choice: the readings of Ŝ and K are a few
    * dozen steps, which were not measured on this evaluator, and no smaller
    * limit was tried.
    */
  private val emptyLeftLimit: Long = 400

  /** The steps within which the heads of the generated side are looked for;
    * a side whose heads are not found within it is not judged.
    */
  private val headsLimit: Long = 400

  private val limit: Long = 20000

  private val closed = HoasGenerators.closedTerm

  property("aLeftSideWithNoReadDecidesTheParallel") {
    for right <- closed.forAll
    yield Result.all(modes.toList.map(mode =>
      if plainHeadsWithin(mode, valueOf(right), headsLimit).finished then
        Result
          .diff(
            normalFormsWithin(mode, valueOf((sHat ∥ k) ∥ right), emptyLeftLimit + headsLimit),
            Bounded.Finished(Vector.empty)
          )(_ == _)
          .log(s"under $mode")
      else Result.success
    ))
  }

  property("aLeftSideTheLimitStopsIsNoEmptyRead") {
    for right <- closed.forAll
    yield Result.all(modes.toList.map(mode =>
      Result.assert(!normalFormsWithin(mode, valueOf(growing ∥ right), limit).finished).log(s"under $mode")
    ))
  }

  property("theWholeAndTheMembershipReadOutsAgreeOnAParallel") {
    for
      left <- closed.forAll
      right <- closed.forAll
    yield
      val value = valueOf(left ∥ right)
      val whole = normalFormsWithin(Mode.WeakHead, value, limit)
      val membership = NormalForms
        .normalForm(Mode.WeakHead, ReadOut.Membership, value)
        .collected
        .result(ReadingState.fresh(limit)) match
        case Computed.Done(found, _) => Bounded.Finished(found.distinct.sortBy(_.toString))
        case Computed.Stopped(after) => stopped(after)
      (whole, membership) match
        case (Bounded.Finished(wholeForms), Bounded.Finished(membershipForms)) =>
          Result.diff(wholeForms.distinct.sortBy(_.toString), membershipForms)(_ == _)
        case _ => Result.success
  }
