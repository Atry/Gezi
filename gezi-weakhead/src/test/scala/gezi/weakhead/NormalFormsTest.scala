package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import gezi.weakhead.EvaluatorTesting.*
import gezi.weakhead.oldcorpora.ScottDataType
import gezi.weakhead.oldcorpora.ScottDecoding
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of `gezi/tests/normal_forms.plt`: the normal-form reader on
  * the weak-head evaluator: a Böhm tree read through neutral values, η-contracted, built on the
  * canonical thunk IR; on pure closed terms it reads the normal form of the
  * independent reference normaliser, in both modes, and a closed βη normal
  * form reads as its own thunk IR; a choice reads the normal forms of its
  * members, a parallel the ones both sides read; a reduction problem reads
  * its expected tree. Every run is bounded by a budget of steps.
  */
class NormalFormsTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))
  private def k: Term = λ(x => λ(_ => x))
  private def kStar: Term = λ(_ => λ(y => y))

  /** Both modes read exactly the normal forms of the expected terms, as a set.
    */
  private def reads(term: Term, expected: Vector[Term]): Unit =
    val expectedTerms = expected.map(lambdaTerm).toSet
    assertEquals(surfaceNormalForms(Mode.WeakHead, term), expectedTerms)
    assertEquals(surfaceNormalForms(Mode.TablingWeakHead, term), expectedTerms)

  /** The normal form read is the thunk IR the front end makes of its own
    * readback.
    */
  private def canonical(normalForm: Configured[NoFacts.type]): Unit =
    assert(Configured.same(Defunctionalization.thunkInstruction[NoFacts.type](instructionTerm(normalForm)), normalForm))

  private def numeral(count: Int): Term =
    λ(f => λ(x => (0 until count).foldLeft(x)((body, _) => f(body))))

  test("combinatorsReadTheirNormalForms") {
    reads(λ(x => x), Vector(λ(i => i)))
    reads(k, Vector(k))
    reads(λ(s => λ(t => λ(u => s(u)(t(u)))))(k)(k), Vector(λ(i => i)))
    reads(λ(a => a)(λ(x => λ(y => y(x)))), Vector(λ(x => λ(y => y(x)))))
  }

  /** \f. \x. f x is the identity by the η rule; \x. y x inside a body
    * contracts to y.
    */
  test("abstractionsAreEtaContracted") {
    reads(λ(f => λ(x => f(x))), Vector(λ(i => i)))
    reads(λ(y => λ(z => z(λ(x => y(x))))), Vector(λ(y => λ(z => z(y)))))
    reads(λ(f => λ(x => λ(y => f(x)(y)))), Vector(λ(i => i)))
  }

  test("churchArithmeticReadsNumerals") {
    reads(numeral(2)(numeral(2)), Vector(numeral(4)))
    reads(λ(m => λ(n => λ(f => λ(x => m(f)(n(f)(x))))))(numeral(3))(numeral(2)), Vector(numeral(5)))
  }

  test("aClosedSubtermUnderABinderIsAFilling") {
    reads(λ(x => x(λ(y => y))), Vector(λ(z => z(λ(i => i)))))
    val value = valueOf(λ(a => a)(λ(x => x(λ(y => y)))))
    val normalForms = finishedValue(normalFormsWithin(Mode.WeakHead, value, smallTermLimit))
    assert(sameInstructions(normalForms, Vector(instructionOf(λ(x => x(λ(y => y)))))))
    normalForms.foreach(canonical)
  }

  test("aChoiceReadsTheNormalFormsOfItsMembers") {
    reads(choice(k, kStar, λ(x => x)), Vector(k, kStar, λ(x => x)))
    reads(λ(f => choice(f, f(λ(i => i)))), Vector(λ(i => i), λ(f => f(λ(i => i)))))
  }

  /** The product law: (\x. x x) (K + K*) = \y. K + \y. K* + \y. y, the mixed
    * \y. K* among them, as the formal definition of the calculus has it.
    */
  test("aChoiceInAnArgumentReadsMixedNormalForms") {
    reads(λ(x => x(x))(choice(k, kStar)), Vector(λ(_ => k), λ(_ => kStar), λ(y => y)))
  }

  test("aParallelReadsWhatBothSidesRead") {
    reads(k ∥ choice(k, kStar), Vector(k))
    reads(choice(k, λ(x => x)) ∥ choice(λ(x => x), kStar), Vector(λ(i => i)))
    reads(k ∥ kStar, Vector.empty)
    reads(λ(x => (λ(a => a) ∥ λ(b => b))(x)), Vector(λ(i => i)))
  }

  /** A parallel inside a spine is read out at that spine's depth. */
  test("aParallelUnderBindersReadsOutAtItsDepth") {
    reads(λ(f => λ(x => x((λ(y => y) ∥ λ(z => z))(f)))), Vector(λ(f => λ(x => x(f)))))
    reads(λ(f => λ(x => f(λ(y => y) ∥ λ(_ => x)))), Vector.empty)
  }

  /** Tabled, the reading of K + Omega finishes within 100,000 steps (the
    * Prolog test's 100,000 inferences) with K alone; untabled, any finite
    * budget is exceeded (the Prolog test's 1,000,000 inferences, 1,000,000
    * steps here), the untabled machine re-entering Omega.
    */
  test("theTabledModeReadsBesideATermWithNoHead") {
    val value = valueOf(choice(k, omega))
    assert(finishedInstructions(normalFormsWithin(Mode.TablingWeakHead, value, 100000), Vector(instructionOf(k))))
    assertEquals(normalFormsWithin(Mode.WeakHead, value, 1000000), Bounded.Exceeded)
  }

  /** On the pure closed term, `agreed` when the reference normalises it
    * within 200,000 steps and the reader, in each mode within the same
    * 200,000, reads that normal form and no other, in the canonical IR;
    * `noReferenceNormalForm(...)` when the reference does not normalise it in
    * time, and then whatever the reader reads in time is checked canonical.
    */
  private def crossChecked(term: DeBruijnTerm): String =
    val value = Values.ofInstruction(Defunctionalization.thunkInstruction(term)(using gezi.ir.NoFacts), Set.empty)
    val expected = Reference.normalFormWithin(term, 200000)
    val untabled = normalFormsWithin(Mode.WeakHead, value, 200000)
    val tabled = normalFormsWithin(Mode.TablingWeakHead, value, 200000)
    expected match
      case Bounded.Finished(normalForm) =>
        val untabledNormalForms = finishedValue(untabled)
        assertEquals(untabledNormalForms.map(instructionTerm), Vector(normalForm))
        assert(sameBounded(tabled, untabled))
        untabledNormalForms.foreach(canonical)
        "agreed"
      case _ =>
        untabled match
          case Bounded.Finished(normalForms) => normalForms.foreach(canonical)
          case _                             => ()
        s"noReferenceNormalForm(${outcomeName(untabled)}, ${outcomeName(tabled)})"

  private def outcomeName(bounded: Bounded[?]): String = bounded match
    case Bounded.Finished(_)         => "Finished"
    case Bounded.Exceeded            => "Exceeded"
    case Bounded.Exhausted(resource) => s"Exhausted($resource)"

  /** 50 random closed pure applications of about 24 nodes from a fixed seed;
    * the counts of the verdicts are printed, and at least one term must
    * agree, so that the check is not vacuous.
    */
  test("theReaderAgreesWithTheReferenceOnRandomTerms") {
    val verdicts = draws(50, 20261010L)(randomApplication(24, _)).map(crossChecked)
    println(s"random normal-form verdicts: ${clumpedCounts(verdicts)}")
    assert(verdicts.contains("agreed"))
  }

  /** 2000 random closed β normal forms of about 20 nodes from a fixed seed,
    * the ones with an η redex left out: the reader reads each as exactly its
    * own thunk IR, in both modes, each within 2,000,000 steps (the Prolog
    * test's 2,000,000 inferences). The counts are printed, and some term must
    * be checked, so that the check is not vacuous.
    */
  test("aNormalFormReadsAsItsOwnInstruction") {
    val verdicts = draws(2000, 20261011L)(randomNormalForm(20, 0, _)).map(term =>
      if etaContracted(term) then
        val instruction = Defunctionalization.thunkInstruction(term)(using gezi.ir.NoFacts)
        val value = Values.ofInstruction(instruction, Set.empty)
        assert(finishedInstructions(normalFormsWithin(Mode.WeakHead, value, 2000000), Vector(instruction)))
        assert(finishedInstructions(normalFormsWithin(Mode.TablingWeakHead, value, 2000000), Vector(instruction)))
        "readAsItself"
      else "etaRedexLeftOut"
    )
    println(s"random normal forms: ${clumpedCounts(verdicts)}")
    assert(verdicts.contains("readAsItself"))
  }

  /** The program of reduction_fibonacci_twenty reads, under
    * tabling(weak_head) and within the problem's own limit of 10 seconds as a
    * budget of steps (`Reading.budgetSteps`, 20,000,000 steps; the Prolog
    * test turned the same seconds into 300,000,000 inferences and read in
    * 260,238; the Scala reading takes 3,319 steps), exactly the
    * canonical term of its expected tree, the binary numeral of fib(20) =
    * 6765. The program is interned, as contest_reduction:program_root/2
    * interns it.
    */
  test("aReductionProblemReadsItsExpectedTree") {
    val program = Defunctionalization.thunkInstruction[NoFacts.type](lambdaTerm(ReductionPrograms.fibonacciProgram(20)))
    val normalForms = finishedValue(
      normalFormsWithin(Mode.TablingWeakHead, gezi.ir.Value.of(program), Reading.budgetSteps(10))
    )
    val expected = lambdaTerm(
      ScottDecoding.treeSurface(ScottDataType.Binary, ScottDecoding.binaryTree(ReductionPrograms.referenceFibonacci(20)))
    )
    assertEquals(normalForms.map(instructionTerm), Vector(expected))
  }
