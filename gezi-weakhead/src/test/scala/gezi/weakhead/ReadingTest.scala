package gezi.weakhead

import gezi.ir.NoFacts

import gezi.weakhead.EvaluatorTesting.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of `gezi/tests/reading.plt`: readings and their observers on a head
  * that is a parallel: the evaluator leaves a parallel unevaluated, so the
  * judge's witness and the contest's verdict read it out, both sides evaluated
  * and compared. A parallel reads out as the witness, or decodes to a value,
  * only when both sides do; a side with no head reads out nothing. Every run is
  * bounded by a budget of steps. The tests of one suite share their tables, and
  * a suite starts from an empty store.
  */
class ReadingTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  /** The judge's ending of one test under the mode, a suite of its own, within
    * 1,000,000 steps (the Prolog test's 1,000,000 inferences).
    */
  private def claimEnding(mode: Mode, test: Term): Ending =
    Judge.claimsAnswered(mode, Vector(test), 1000000) match
      case Vector((ending, _)) => ending
      case other               => fail(s"one test gave ${other.size} answers")

  /** The contest's verdict on the reading of the closed program under the mode
    * within 1,000,000 steps (the Prolog test's 1,000,000 inferences), its
    * intended answer a head of the value.
    */
  private def surfaceVerdict(
      mode: Mode,
      term: Term,
      intended: Intended
  ): Verdict =
    val root = valueOf(term)
    Judge.verdict(
      intended,
      Reading.termReading(
        mode,
        root,
        1000000,
        gezi.weakhead.ReadingConfiguration.withoutFacts
      )
    )

  private def trueTerm: Term = λ(t => λ(_ => t))
  private def falseTerm: Term = λ(_ => λ(f => f))

  private def unary(count: Int): Term = ReductionPrograms.unary(count)

  /** (\a. a ∥ \b. b) x = x ∥ x by (9): both sides read out as the witness. */
  test("aParallelOfWitnessesProvesTheClaim") {
    modes.foreach(mode =>
      assertEquals(
        (mode, claimEnding(mode, λ(x => (λ(a => a) ∥ λ(b => b))(x)))),
        (mode, Ending.Succeeded)
      )
      assertEquals(
        (
          mode,
          claimEnding(mode, λ(x => ((λ(a => a) ∥ λ(b => b)) ∥ λ(c => c))(x)))
        ),
        (mode, Ending.Succeeded)
      )
    )
  }

  /** (\a. a ∥ \b. \c. b) x = x ∥ \c. x: the right side's one head is no
    * witness, so the claim fails, finitely.
    */
  test("aParallelWhoseRightSideIsNoWitnessFails") {
    modes.foreach(mode =>
      assertEquals(
        (mode, claimEnding(mode, λ(x => (λ(a => a) ∥ λ(b => λ(_ => b)))(x)))),
        (mode, Ending.Failed)
      )
    )
  }

  /** (\a. a ∥ Ω) x: the right side has no head; untabled its evaluation does
    * not finish within the budget, any finite budget (1,000,000 steps), tabled
    * it finishes with no head.
    */
  test("aParallelWithASideWithoutHeadDoesNotProveTheClaim") {
    assertEquals(
      claimEnding(Mode.WeakHead, λ(x => (λ(a => a) ∥ omega)(x))),
      Ending.Stopped
    )
    assertEquals(
      claimEnding(Mode.TablingWeakHead, λ(y => (λ(b => b) ∥ omega)(y))),
      Ending.Failed
    )
  }

  /** The witness reading itself: a parallel head whose sides both reach the
    * witness reads out as found, within 100,000 steps (the Prolog test's
    * 100,000 inferences).
    */
  test("theWitnessReadingReadsAParallelOut") {
    val parallel = valueOf(λ(a => a) ∥ λ(b => b))
    val witness = NeutralValue(JudgeWitness, Vector.empty)
    modes.foreach(mode =>
      val readings = Reading.witnessReadings(
        mode,
        Vector(Value.Apply(parallel, witness)),
        witness,
        100000,
        gezi.weakhead.ReadingConfiguration.withoutFacts
      )
      assertEquals(
        (mode, readings.map(_.outcome)),
        (mode, Vector(WitnessOutcome.Found))
      )
    )
  }

  /** A suite keeps its tables from one test to the next (`Reading`'s THE
    * SUITE): under tabling(weak_head) the second reading of Omega's test finds
    * the first one's tables complete and spends fewer steps. The suite read
    * again starts from an empty store, so its first reading again spends more
    * than its second, which spends what the second spent before. The Prolog
    * test did not compare the first readings of the two suites, the first
    * reading of a SWI-Prolog process spending a few inferences more than a
    * later one; the Scala count has no such cost and the two first readings
    * spend the same, which is asserted too.
    */
  test("aSuiteKeepsItsTablesFromOneTestToTheNext") {
    val tests = Vector(λ(x => omega(x)), λ(y => omega(y)))
    val answers = Judge.claimsAnswered(Mode.TablingWeakHead, tests, 1000000)
    val Vector((firstEnding, firstSpent), (secondEnding, secondSpent)) =
      answers: @unchecked
    assertEquals((firstEnding, secondEnding), (Ending.Failed, Ending.Failed))
    assert(secondSpent < firstSpent, s"$secondSpent steps after $firstSpent")
    val again = Judge.claimsAnswered(Mode.TablingWeakHead, tests, 1000000)
    val Vector(
      (firstAgainEnding, firstAgainSpent),
      (secondAgainEnding, secondAgainSpent)
    ) = again: @unchecked
    assertEquals(
      (firstAgainEnding, secondAgainEnding),
      (Ending.Failed, Ending.Failed)
    )
    assert(
      secondAgainSpent < firstAgainSpent,
      s"$secondAgainSpent steps after $firstAgainSpent"
    )
    assertEquals(secondAgainSpent, secondSpent)
    assertEquals(firstAgainSpent, firstSpent)
  }

  /** A reading's head may be a parallel; the verdict reads it out. */
  test("theVerdictReadsAParallelHeadOut") {
    modes.foreach(mode =>
      assertEquals(
        (mode, surfaceVerdict(mode, trueTerm ∥ trueTerm, Intended.Truth(true))),
        (mode, Verdict.Matches)
      )
      assertEquals(
        (
          mode,
          surfaceVerdict(mode, trueTerm ∥ falseTerm, Intended.Truth(true))
        ),
        (mode, Verdict.Differs)
      )
      assertEquals(
        (
          mode,
          surfaceVerdict(
            mode,
            unary(2) ∥ λ(n => λ(_ => λ(s => s(n))))(unary(1)),
            Intended.Natural(2)
          )
        ),
        (mode, Verdict.Matches)
      )
    )
  }

  /** A parallel inside a value's body: \t. \f. t ∥ t chooses the parallel of
    * the true marker with itself.
    */
  test("theVerdictReadsAParallelInABodyOut") {
    modes.foreach(mode =>
      assertEquals(
        (
          mode,
          surfaceVerdict(mode, λ(t => λ(_ => t ∥ t)), Intended.Truth(true))
        ),
        (mode, Verdict.Matches)
      )
    )
  }
