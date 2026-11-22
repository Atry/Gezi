package gezi.jit

import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.standardlibrary.LibraryFiles
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting.plainHeadsWithin
import gezi.weakhead.EvaluatorTesting.valueOf
import gezi.weakhead.KnownExtremes
import gezi.weakhead.Mode

/** The JIT reads a listed extreme of ⊑_O as the reference,
  * tabling(weak_head), does:
  * under
  * the known extremes that list top as a greatest term and Ω as a least one, the
  * JIT's parallel sets of a term are tabling(weak_head)'s, on the terms of the weak
  * head's own laws of the extremes (`gezi.weakhead.ParallelSetLawTest`):
  * top and Ω beside, inside, applied to and in a choice with a generated closed
  * term. Its purpose is to catch the JIT evaluating a listed extreme, which it
  * did before: top read a lambda head under the JIT and none under the weak
  * head, and Ω applied to anything gave no empty parallel set.
  */
class JitKnownExtremesLawTest extends GeneratedProperties:

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  private def top: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))(λ(z => λ(x => z ∥ x)))

  private def known: KnownExtremes = KnownExtremes(Vector(valueOf(top)), Vector(valueOf(omega)))

  /** A JIT over no knowledge: the extremes are the reading's, not the
    * library's.
    */
  private lazy val jit: Jit =
    Jit(JitConfiguration.of(BackendFacts.of(LibraryFiles.compiled("tests/library_fixtures/no_knowledge.lambdalattice", Vector.empty)), instanceTable = false))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => jit)

  private val limit: Long = 20000

  /** The JIT's answers are tabling(weak_head)'s where both finish within the
    * limit; a term either reader does not finish proves nothing either way.
    */
  private def agrees(term: Term, label: String): Result =
    val value = valueOf(term)
    (plainHeadsWithin(Mode.Jit(jit), value, limit, known), plainHeadsWithin(Mode.TablingWeakHead, value, limit, known)) match
      case (Bounded.Finished(byJit), Bounded.Finished(byWeakHead)) =>
        Result.diff(byJit.toSet, byWeakHead.toSet)(_ == _).log(label)
      case _ => Result.success

  property("the JIT reads a known top and a known bottom as the weak head does") {
    for term <- HoasGenerators.closedTerm.forAll
    yield Result.all(List(
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
    ))
  }
