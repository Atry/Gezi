package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.weakhead.NoJitState

/** The law that a list's decode point is sound: on generated values filtered by
  * the lists of an element and applied to two generated cases,
  * `(x ∥ list_type e) a b`, the JIT with the natives on
  * (`NativesTesting.nativesOn`) throws on none and, wherever both finish, reads
  * no normal form tabling(weak_head) does not. It may read fewer: the decoded
  * list is above the filtered value in the term order
  * (`com.yang_bo.gezi.weakhead.ListCodec`, WHY A DECODED LIST STANDS FOR THE FILTERED
  * VALUE), so it drops the answers of a branch of the type that meets the
  * value's other constructor, such as `n ∥ c i t` applied to cases that agree.
  * The values are drawn half from the Scott cells `λn c. c i t` whose item i
  * may mention n, the nil case the decoding applies the value to, so that a
  * decoding keeps one of its own cases as an item. Its purpose is to catch a
  * decode point that takes such a decoded list for the filtered value, whose
  * reader then meets the decoding's neutral value and throws (as before the
  * check of `JitValues.mayHoldDecodingCase`), or reads another answer.
  */
class ListDecodingLawTest extends GeneratedProperties:

  // Measured 2026-11-22 on 2 CPUs (contest.slice, CPUs 10 and 11, nice 10), the 1-minute load 10 to 16 on 12: the
  // property's 20 samples took 5.5, 6.4, 7.9, 8.5 and 10.3 s over five runs, the natives' library read as its shared
  // fixture; the bound is 1.5 times the slowest rounded up. Each sample reads its term twice, the reference and the JIT
  // with the natives' library, and once more within the larger limit when one of them does not finish. With the check
  // of `JitValues.mayHoldDecodingCase` turned off, 20 samples threw `NeutralValueNotOpened` in four runs of four.
  // FIXME: the suite is to be made fast (https://github.com/Atry/private-overlay/issues/1925).
  override val munitTimeout = scala.concurrent.duration.Duration(16, "s")

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => NativesTesting.nativesOn, _ => evaluator)

  private lazy val evaluator = Jit(
    NativesTesting.configurationOf(NativesTesting.nativesOn)
  )

  private lazy val nil = JitTesting.libraryTerm("nil")
  private lazy val cons = JitTesting.libraryTerm("cons")
  private lazy val zero = JitTesting.libraryTerm("zero")
  private lazy val listType = JitTesting.libraryTerm("list_type")

  private def leaves: Vector[Term] = Vector(nil, zero, Term.λ(y => y))

  /** A small closed term over the leaves. */
  private def small: Gen[Term] =
    HoasGenerators.closedTermOver(leaves).resize(hedgehog.Size(8))

  /** A Scott cell `λn c. c i t`: its item one of n, a term mentioning n or a
    * closed term, its tail nil or a cell of a closed item.
    */
  private def cell: Gen[Term] =
    for
      item <- Gen.element1[Term => Term](
        n => n,
        n => Term.λ(_ => n),
        _ => zero,
        n => cons(n)(nil)
      )
      closedItem <- small
      tail <- Gen.element1[Term](nil, cons(closedItem)(nil))
      mentions <- Gen.boolean
    yield Term.λ(n =>
      Term.λ(c => c(if mentions then item(n) else closedItem)(tail))
    )

  private def values: Gen[Term] = Gen.choice1(cell, small)

  property(
    "a list's decode point reads no normal form tabling(weak_head) does not",
    _.copy(testLimit = 20)
  ) {
    for
      value <- values.forAll
      element <- Gen
        .element1[Term](Term.λ(y => y), JitTesting.libraryTerm("nat_type"))
        .forAll
      nilCase <- small.forAll
      consCase <- Gen
        .element1[Term](
          Term.λ(h => Term.λ(_ => h)),
          Term.λ(_ => Term.λ(t => t))
        )
        .forAll
    yield
      val root = JitTesting.termInstruction(
        (value ∥ listType(element))(nilCase)(consCase)
      )
      val compared = JitTesting.comparison(
        JitTesting.normalFormsQuestion(evaluator, root),
        20000,
        NoJitState,
        cacheDropped = true
      )
      compared.disagreement match
        case Some((answers, expected))
            if !answers.toSet.subsetOf(expected.toSet) =>
          Result.failure.log(
            s"${com.yang_bo.gezi.frontend.ReadableText.printedNameless(root).text}: the JIT read $answers where tabling(weak_head) read $expected"
          )
        case _ => Result.success
  }
