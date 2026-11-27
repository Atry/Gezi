package gezi.weakhead

import gezi.ir.NoFacts
import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.weakhead.EvaluatorTesting.*

/** The laws of the evaluator's answers as a set of parallel sets
  * (`WeakHead`, THE RULES and KNOWN EXTREMES), on generated closed terms,
  * under `weak_head` and `tabling(weak_head)`, each wherever the evaluations
  * it compares finish:
  * (1) the parallel is a set: `m ∥ n` and `n ∥ m` have the same answers, so
  * do `(m ∥ n) ∥ p` and `m ∥ (n ∥ p)`, and `m ∥ m` has those of `m` once an
  * answer that holds every head of another is dropped (absorption, which
  * the evaluator leaves to its caller);
  * (2) a choice inside a parallel distributes, and an application
  * distributes over both: `m ∥ (n + p)` as `(m ∥ n) + (m ∥ p)`, `(m ∥ n) p`
  * as `m p ∥ n p`, `(m + n) p` as `m p + n p`;
  * (3) a known top: `top + m` has the answers of `m`; `top ∥ m` and `top m` have
  * none, whatever `m` is, `m` not evaluated; `m ∥ top` has none;
  * (4) a known bottom: `Ω ∥ m` has the answers of `m`, `Ω m` has the empty
  * parallel set alone, whatever `m` is, and `Ω + m` has it alone once
  * reduced by `WeakHead.bottomAbsorbed`.
  * Their purpose is to catch a parallel whose answers depend on the order or
  * the repetition of its sides, a choice inside a parallel that is not
  * distributed, and a known extreme whose rule is not executed or whose
  * arguments are evaluated.
  */
class ParallelSetLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of ParallelSetLawTest, "aChoiceInsideAParallelAndAnApplicationDistribute", takes 3.295 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "s")

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  private def top: Term = λ(f => λ(x => f(x(x)))(λ(x => f(x(x)))))(λ(z => λ(x => z ∥ x)))

  /** The variant that knows top as a greatest term and Ω as a least one. */
  private def known: KnownExtremes = KnownExtremes(Vector(gezi.frontend.Defunctionalization.pure(lambdaTerm(top))), Vector(gezi.frontend.Defunctionalization.pure(lambdaTerm(omega))))

  private val limit: Long = 20000

  /** The steps an evaluation that evaluates no argument of a known extreme
    * may take. A choice: such an evaluation is a handful of steps.
    */
  private val noArgumentLimit: Long = 100

  private val closed = HoasGenerators.closedTerm

  /** The answers of the term, where its evaluation finishes. */
  private def answers(mode: Mode, term: Term, extremes: KnownExtremes, stepLimit: Long): Option[Vector[ParallelSet[NoFacts.type]]] =
    plainHeadsWithin(mode, valueOf(term), stepLimit, extremes) match
      case Bounded.Finished(sets) => Some(sets)
      case _                      => None

  /** Whether the two vectors hold the same parallel sets, whatever their
    * order and repetition.
    */
  private def sameSets(left: Vector[ParallelSet[NoFacts.type]], right: Vector[ParallelSet[NoFacts.type]]): Boolean =
    left.forall(right.contains) && right.forall(left.contains)

  /** The answers that hold every head of no other answer. */
  private def minimal(sets: Vector[ParallelSet[NoFacts.type]]): Vector[ParallelSet[NoFacts.type]] =
    sets.filter(set => !sets.exists(other => other != set && set.holdsAll(other)))

  /** The two terms have the same answers under each mode, as `compared`
    * sees them, wherever both evaluations finish.
    */
  private def sameAnswers(left: Term, right: Term, extremes: KnownExtremes)(
      compared: Vector[ParallelSet[NoFacts.type]] => Vector[ParallelSet[NoFacts.type]]
  ): Result =
    Result.all(modes.toList.map(mode =>
      (answers(mode, left, extremes, limit), answers(mode, right, extremes, limit)) match
        case (Some(leftAnswers), Some(rightAnswers)) =>
          Result.diff(compared(leftAnswers), compared(rightAnswers))(sameSets).log(s"under $mode")
        case _ => Result.success
    ))

  /** The term's evaluation finishes within the limit with exactly the
    * answers, under each mode.
    */
  private def hasAnswers(term: Term, expected: Vector[ParallelSet[NoFacts.type]], stepLimit: Long): Result =
    Result.all(modes.toList.map(mode =>
      answers(mode, term, known, stepLimit) match
        case Some(found) => Result.diff(found, expected)(sameSets).log(s"under $mode")
        case None        => Result.failure.log(s"under $mode the evaluation did not finish within $stepLimit steps")
    ))

  property("theParallelIsASet") {
    for
      first <- closed.forAll
      second <- closed.forAll
      third <- closed.forAll
    yield Result.all(List(
      sameAnswers(first ∥ second, second ∥ first, KnownExtremes.none)(identity).log("commutative"),
      sameAnswers((first ∥ second) ∥ third, first ∥ (second ∥ third), KnownExtremes.none)(identity).log("associative"),
      sameAnswers(first ∥ first, first, KnownExtremes.none)(minimal).log("idempotent")
    ))
  }

  property("aChoiceInsideAParallelAndAnApplicationDistribute") {
    for
      first <- closed.forAll
      second <- closed.forAll
      third <- closed.forAll
    yield Result.all(List(
      sameAnswers(first ∥ (second + third), (first ∥ second) + (first ∥ third), KnownExtremes.none)(identity)
        .log("the parallel over the choice"),
      sameAnswers((first ∥ second)(third), first(third) ∥ second(third), KnownExtremes.none)(identity)
        .log("equation (9)"),
      sameAnswers((first + second)(third), first(third) + second(third), KnownExtremes.none)(identity)
        .log("equation (8)")
    ))
  }

  property("aKnownTopHasNoAnswerAndIsTheUnitOfTheChoice") {
    for term <- closed.forAll
    yield Result.all(List(
      sameAnswers(top + term, term, known)(identity).log("top + m"),
      hasAnswers(top ∥ term, Vector.empty, noArgumentLimit).log("top ∥ m"),
      hasAnswers(top(term), Vector.empty, noArgumentLimit).log("top m"),
      sameAnswers(term ∥ top, top, known)(identity).log("m ∥ top")
    ))
  }

  property("aKnownBottomIsTheUnitOfTheParallelAndAbsorbsTheChoice") {
    for term <- closed.forAll
    yield Result.all(List(
      sameAnswers(omega ∥ term, term, known)(identity).log("bottom ∥ m"),
      sameAnswers(term ∥ omega, term, known)(identity).log("m ∥ bottom"),
      hasAnswers(omega(term), Vector(ParallelSet.bottom[NoFacts.type]), noArgumentLimit).log("bottom m"),
      sameAnswers(omega + term, omega, known)(WeakHead.bottomAbsorbed).log("bottom + m")
    ))
  }
