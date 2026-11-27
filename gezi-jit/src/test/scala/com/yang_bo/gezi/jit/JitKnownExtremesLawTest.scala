package com.yang_bo.gezi.jit

import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.λ
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.EvaluatorTesting
import com.yang_bo.gezi.weakhead.KnownExtremes
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.ReadingConfiguration
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.weakhead.WeakHead

/** The JIT reads a listed extreme of ⊑_O as the reference, tabling(weak_head),
  * does: under the known extremes that list top as a greatest term and Ω as a
  * least one, the JIT's parallel sets of a term are tabling(weak_head)'s, on
  * the terms of the weak head's own laws of the extremes
  * (`com.yang_bo.gezi.weakhead.ParallelSetLawTest`): top and Ω beside, inside, applied to
  * and in a choice with a generated closed term. Its purpose is to catch the
  * JIT evaluating a listed extreme, which it did before: top read a lambda head
  * under the JIT and none under the weak head, and Ω applied to anything gave
  * no empty parallel set.
  */
class JitKnownExtremesLawTest extends GeneratedProperties:

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  private def top: Term =
    λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))(λ(z => λ(x => z ∥ x)))

  private def known: KnownExtremes =
    KnownExtremes(
      Vector(Defunctionalization.pure(top.deBruijnTerm(Map.empty))),
      Vector(Defunctionalization.pure(omega.deBruijnTerm(Map.empty)))
    )

  private lazy val encoding: StorageEncoding =
    BackendFacts
      .of(
        LibraryFiles.compiled(
          "tests/library_fixtures/no_knowledge.lambdalattice",
          Vector.empty
        )
      )
      .storageEncoding

  private given encoding.type = encoding

  /** A JIT over no knowledge: the extremes are the reading's, not the
    * library's.
    */
  private lazy val jit: Jit[encoding.type] =
    Jit(
      JitConfiguration.of[encoding.type](
        encoding,
        instanceTable = false,
        com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => jit)

  private val limit: Long = 20000

  /** The parallel sets of the value under the mode and the configuration,
    * within the limit and under the known extremes.
    */
  private def headsWithin(
      mode: Mode,
      configuration: ReadingConfiguration[encoding.type],
      value: com.yang_bo.gezi.ir.Value[encoding.type]
  ): Bounded[Vector[com.yang_bo.gezi.weakhead.ParallelSet[encoding.type]]] =
    WeakHead
      .heads(mode, value)
      .collected
      .result(ReadingState.knowing(limit, known, configuration)) match
      case Computed.Done(heads, _) => Bounded.Finished(heads)
      case Computed.Stopped(after) => EvaluatorTesting.stopped(after)

  /** The JIT's answers are tabling(weak_head)'s where both finish within the
    * limit; a term either reader does not finish proves nothing either way.
    */
  private def agrees(term: Term, label: String): Result =
    val value = JitTesting.termValue[encoding.type](term)
    (
      headsWithin(Mode.Jit, jit.readingConfiguration, value),
      headsWithin(
        Mode.TablingWeakHead,
        JitTesting.referenceConfiguration(jit),
        value
      )
    ) match
      case (Bounded.Finished(byJit), Bounded.Finished(byWeakHead)) =>
        Result.diff(byJit.toSet, byWeakHead.toSet)(_ == _).log(label)
      case _ => Result.success

  property(
    "the JIT reads a known top and a known bottom as the weak head does"
  ) {
    for term <- HoasGenerators.closedTerm.forAll
    yield Result.all(
      List(
        agrees(top, "top"),
        agrees(top + term, "top + m"),
        agrees(top ∥ term, "top ∥ m"),
        agrees(top(term), "top m"),
        agrees(term ∥ top, "m ∥ top"),
        agrees(omega, "bottom"),
        agrees(omega ∥ term, "bottom ∥ m"),
        agrees(term ∥ omega, "m ∥ bottom"),
        agrees(omega(term), "bottom m"),
        agrees(omega + term, "bottom + m")
      )
    )
  }
