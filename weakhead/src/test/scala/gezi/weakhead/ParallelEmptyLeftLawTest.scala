package gezi.weakhead

import gezi.ir.NoFacts

import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.weakhead.EvaluatorTesting.*

/** The laws of the whole read-out of a parallel set, whose heads are tried in
  * turn within doubling shares of steps (`NormalForms.setRead`), on generated
  * closed terms, under `weak_head` and `tabling(weak_head)`: (1) heads that
  * finish with no common read decide the set: `(Ŝ ∥ K) ∥ m` reads ∅ within a
  * few steps more than the evaluator takes to find the heads of `m`, Ŝ and K
  * having no common normal form, so that the heads of `m` are found and not
  * read; (2) a head the limit stops is no read of ∅, and the set is read from a
  * head that ends: `θ ∥ m`, `θ = Y (λf. λx. x f)`, whose Böhm tree is infinite,
  * so that its normal form reading opens binders without end at depths no
  * reading repeats (tabling reads a term with no head, Ω's kind, as ∅ by its
  * least fixed point, and so is no witness), reads ∅ where m alone ends within
  * an eighth of the limit, θ having no normal form, each of m's reads tested on
  * θ and found apart at a finite depth (θ's share of 4,096 steps given up, then
  * m read within its share, its reads expanded and θ descended to the first
  * difference, within the limit), and does not end where m alone does not end
  * within the limit; (3) under `weak_head`, the whole read-out and the read-out
  * by membership read the same normal forms of `m ∥ n` wherever both finish.
  * Their purpose is to catch a short-circuit that answers ∅ for a head whose
  * reading did not finish, one that does not fire, or a whole read-out of a
  * parallel set that disagrees with the membership read-out.
  */
class ParallelEmptyLeftLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private val sHat: Term = λ(x => λ(y => λ(z => x(z)(y(z)))))
  private val k: Term = λ(x => λ(_ => x))
  private def growing: Term =
    val fixedPoint = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))
    fixedPoint(λ(f => λ(x => x(f))))

  /** The steps the reading of `Ŝ ∥ K` may take beside the steps of finding the
    * other side's heads. A choice: the readings of Ŝ and K are a few dozen
    * steps, which were not measured on this evaluator, and no smaller limit was
    * tried.
    */
  private val emptyLeftLimit: Long = 400

  /** The steps within which the heads of the generated side are looked for; a
    * side whose heads are not found within it is not judged.
    */
  private val headsLimit: Long = 400

  private val limit: Long = 20000

  private val closed = HoasGenerators.closedTerm

  property("aLeftSideWithNoReadDecidesTheParallel") {
    for right <- closed.forAll
    yield Result.all(
      modes.toList.map(mode =>
        if plainHeadsWithin(mode, valueOf(right), headsLimit).finished then
          Result
            .diff(
              normalFormsWithin(
                mode,
                valueOf((sHat ∥ k) ∥ right),
                emptyLeftLimit + headsLimit
              ),
              Bounded.Finished(Vector.empty)
            )(sameBounded)
            .log(s"under $mode")
        else Result.success
      )
    )
  }

  property("aLeftSideTheLimitStopsIsNoEmptyRead") {
    for right <- closed.forAll
    yield Result.all(modes.toList.map(mode =>
      val both = normalFormsWithin(mode, valueOf(growing ∥ right), limit)
      if normalFormsWithin(mode, valueOf(right), limit / 8).finished then
        Result
          .diff(both, Bounded.Finished(Vector.empty))(sameBounded)
          .log(s"under $mode, the right side ending")
      else if !normalFormsWithin(mode, valueOf(right), limit).finished then
        Result.assert(!both.finished).log(s"under $mode, neither side ending")
      else Result.success
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
        .normalForm(Mode.WeakHead, ParallelSetReading.Membership, value)
        .collected
        .result(
          ReadingState
            .fresh(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
        ) match
        case Computed.Done(found, _) =>
          Bounded.Finished(
            found.distinct.sorted(gezi.ir.ContentComparison.ordering)
          )
        case Computed.Stopped(after) => stopped(after)
      (whole, membership) match
        case (
              Bounded.Finished(wholeForms),
              Bounded.Finished(membershipForms)
            ) =>
          Result.diff(
            wholeForms.distinct.sorted(gezi.ir.ContentComparison.ordering),
            membershipForms
          )(sameInstructions)
        case _ => Result.success
  }
