package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.NoFacts

import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.weakhead.EvaluatorTesting.*

/** The laws of the normal-form reading of a parallel set that holds a closed
  * head beside the variable of an opened binder
  * (`NormalForms.closedBesideOpenedVariable`), and of top, on generated closed
  * terms, under `weak_head` and `tabling(weak_head)`: (1) `λx. m ∥ x`,
  * `λx. x ∥ m` and `λx. m ∥ x n` read nothing wherever their reading finishes,
  * whatever the closed m and n are: the evaluator evaluates m to its heads, so
  * a reading need not finish; (2) top = Y (λz. λx. z ∥ x), whose body under its
  * binder is top ∥ x, reads ∅ under the plain evaluator, and under the
  * evaluator that knows top as a greatest term (`KnownExtremes`) so do top m
  * and top m n within a few steps, m and n not evaluated; (3) m + top reads
  * what m reads wherever m's reading finishes. Their purpose is to catch a rule
  * that does not fire for top (the term that stands for no answer once 0 has
  * left the calculus), a known top whose arguments are evaluated, and a top
  * that adds or removes a read of the term it is chosen with.
  */
class ClosedBesideOpenedVariableLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private def fixedPoint: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))

  private def top: Term = fixedPoint(λ(z => λ(x => z ∥ x)))

  /** The evaluator's variant that knows top as a greatest term. */
  private def knowingTop: KnownExtremes = KnownExtremes(
    Vector(com.yang_bo.gezi.frontend.Defunctionalization.pure(lambdaTerm(top))),
    Vector.empty
  )

  /** The steps a reading that evaluates no argument of a known top may take. A
    * choice: the readings take a handful of steps each, which were not
    * measured, and no smaller limit was tried.
    */
  private val noArgumentLimit: Long = 400

  private val limit: Long = 20000

  private val closed = HoasGenerators.closedTerm

  /** The reading read nothing, or did not finish within the limit. */
  private def readsNothingWhereFinished(term: Term): Result =
    Result.all(
      modes.toList.map(mode =>
        normalFormsWithin(mode, valueOf(term), limit) match
          case Bounded.Finished(read) =>
            Result.diff(read, Vector.empty)(_ == _).log(s"under $mode")
          case _ => Result.success
      )
    )

  /** The reading finished within the limit with nothing read, under the known
    * extremes.
    */
  private def readsNothing(
      term: Term,
      stepLimit: Long,
      extremes: KnownExtremes
  ): Result =
    Result.all(
      modes.toList.map(mode =>
        Result
          .diff(
            normalFormsWithin(mode, valueOf(term), stepLimit, extremes),
            Bounded.Finished(Vector.empty)
          )(_ == _)
          .log(s"under $mode")
      )
    )

  property("aClosedSideBesideAnOpenedVariableReadsNothing") {
    for
      side <- closed.forAll
      argument <- closed.forAll
    yield Result.all(
      List(
        readsNothingWhereFinished(λ(x => side ∥ x)).log("closed on the left"),
        readsNothingWhereFinished(λ(x => x ∥ side)).log("closed on the right"),
        readsNothingWhereFinished(λ(x => side ∥ x(argument)))
          .log("the variable applied")
      )
    )
  }

  property("topReadsNothingAppliedOrNot") {
    for
      first <- closed.forAll
      second <- closed.forAll
    yield Result.all(
      List(
        readsNothing(top, limit, KnownExtremes.none)
          .log("top under the plain evaluator"),
        readsNothing(top, noArgumentLimit, knowingTop).log("top"),
        readsNothing(top(first), noArgumentLimit, knowingTop)
          .log("top applied once"),
        readsNothing(top(first)(second), noArgumentLimit, knowingTop)
          .log("top applied twice")
      )
    )
  }

  property("topChosenWithATermReadsWhatTheTermReads") {
    for term <- closed.forAll
    yield Result.all(
      modes.toList.map(mode =>
        normalFormsWithin(mode, valueOf(term), limit) match
          case Bounded.Finished(alone) =>
            normalFormsWithin(
              mode,
              valueOf(term + top),
              limit + noArgumentLimit
            ) match
              case Bounded.Finished(withTop) =>
                Result
                  .diff(withTop.toSet, alone.toSet)(_ == _)
                  .log(s"under $mode")
              case other =>
                Result.failure.log(
                  s"under $mode the reading with top did not finish: $other"
                )
          case _ => Result.success
      )
    )
  }
