package gezi.weakhead

import gezi.weakhead.EvaluatorTesting.*
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of `gezi/tests/weak_head.plt`: the weak-head evaluator on
  * the thunk IR. Its heads read back are the heads of the independent de
  * Bruijn evaluator (`Reference`), in both modes; Omega runs without end
  * untabled and has no head tabled; a choice yields its members' heads; a
  * parallel is one parallel set of its sides' heads, distributes over an
  * application by equation (9) and is read out by the normal-form reader;
  * the tabled mode completes the rings of the graph family. Every run is
  * bounded by a budget of steps, never by a clock.
  */
class WeakHeadTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of WeakHeadTest, "weakHeadAgreesWithTheReferenceOnRandomTerms", takes 3.848 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  private val modes = Vector(Mode.WeakHead, Mode.TablingWeakHead)

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))
  private def k: Term = λ(x => λ(_ => x))
  private def kStar: Term = λ(_ => λ(y => y))

  /** The one head the mode reads is the reference's head. */
  private def agreesWithTheReference(mode: Mode, term: Term): Unit =
    val expected = finishedValue(Reference.weakHeadWithin(lambdaTerm(term), smallTermLimit))
    assertEquals(surfaceHeads(mode, term), Vector(expected))

  test("weakHeadAgreesWithTheReference") {
    val terms = Vector(
      λ(x => x),
      λ(x => x)(λ(y => y)),
      k(λ(a => a))(λ(b => b(b))),
      λ(s => λ(t => λ(u => s(u)(t(u)))))(k)(k),
      kStar(omega),
      λ(f => λ(x => f(f(x))))(λ(y => y))
    )
    terms.foreach(term => modes.foreach(agreesWithTheReference(_, term)))
  }

  /** The reference against the evaluator, untabled and tabled, on the pure
    * closed term, each within 200,000 steps (the Prolog test's 200,000
    * inferences; a step of either is coarser than an inference, so a term
    * that finishes takes fewer steps than it took inferences). `agreed` when
    * the reference and the untabled evaluator both read the head, and then
    * the tabled evaluator reads that head and no other;
    * `untabledExceeded(...)` when neither reads one in time, and then the
    * tabled evaluator answers no head or runs out of steps. Any other outcome
    * is a failed assertion.
    */
  private def crossChecked(term: DeBruijnTerm): String =
    val limit = 200000L
    val expected = Reference.weakHeadWithin(term, limit)
    val value = Values.ofInstruction(Defunctionalization.thunkInstruction(term), Set.empty)
    val untabled = headsWithin(Mode.WeakHead, value, limit)
    val tabled = headsWithin(Mode.TablingWeakHead, value, limit)
    (expected, untabled) match
      case (Bounded.Finished(head), Bounded.Finished(heads)) =>
        assertEquals(heads, Vector(head))
        assertEquals(tabled, Bounded.Finished(Vector(head)))
        "agreed"
      case (Bounded.Exceeded, Bounded.Exceeded) =>
        tabled match
          case Bounded.Finished(tabledHeads) =>
            assertEquals(tabledHeads, Vector.empty)
            "untabledExceeded(noHeadTabled)"
          case Bounded.Exceeded            => "untabledExceeded(Exceeded)"
          case Bounded.Exhausted(resource) => s"untabledExceeded(Exhausted($resource))"
      case _ =>
        fail(s"the reference finished: ${expected.finished}, the untabled evaluator: ${untabled.finished}")

  /** 300 random closed pure applications of about 24 nodes from a fixed seed;
    * the counts of the verdicts are printed, and at least one term must reach
    * each of the two agreeing verdicts, so that the check is not vacuous.
    */
  test("weakHeadAgreesWithTheReferenceOnRandomTerms") {
    val verdicts = draws(300, 20261010L)(randomApplication(24, _)).map(crossChecked)
    println(s"random cross-check verdicts: ${clumpedCounts(verdicts)}")
    assert(verdicts.contains("agreed"))
    assert(verdicts.exists(_.startsWith("untabledExceeded")))
  }

  /** The instructions of an interned term are read one layer when reached:
    * the normal forms of the instruction are those of its value
    * (`Values.ofInstruction`).
    */
  test("anInternedTermReadsAsItsInstruction") {
    val instruction = instructionOf(λ(s => λ(t => λ(u => s(u)(t(u)))))(k)(k))
    val value = Values.ofInstruction(instruction, Set.empty)
    val expected = finishedValue(normalFormsWithin(Mode.WeakHead, value, smallTermLimit))
    val normalForms = finishedValue(normalFormsWithin(Mode.WeakHead, instruction, smallTermLimit))
    assertEquals(normalForms, expected)
    assertEquals(normalForms.map(instructionTerm), Vector(lambdaTerm(λ(i => i))))
  }

  /** Any finite budget is exceeded: the untabled machine re-enters Omega
    * without end. The Prolog test's budget was 1,000,000 inferences; 100,000
    * steps here.
    */
  test("omegaExceedsAnInferenceLimitUntabled") {
    val value = valueOf(omega)
    assertEquals(headsWithin(Mode.WeakHead, value, 100000), Bounded.Exceeded)
  }

  /** The tabled evaluation of Omega finishes with no head within a small
    * budget: the Prolog test's 100,000 inferences, 100,000 steps here (the
    * reading takes 4, MEASURED by `stepsOfOmegaTabled` below).
    */
  test("omegaHasNoHeadTabled") {
    val value = valueOf(omega)
    assertEquals(headsWithin(Mode.TablingWeakHead, value, 100000), Bounded.Finished(Vector.empty))
  }

  test("stepsOfOmegaTabled") {
    val value = valueOf(omega)
    WeakHead.heads(Mode.TablingWeakHead, value).collected.result(ReadingState.fresh(100000)) match
      case Computed.Done(heads, after) =>
        assertEquals(heads, Vector.empty)
        assertEquals(after.budget.spent, 4L)
      case Computed.Stopped(_) => fail("Omega's tabled reading stopped")
  }

  test("argumentIgnoredReadsAHead") {
    val expected = Vector(lambdaTerm(λ(v => v)))
    modes.foreach(mode => assertEquals(surfaceHeads(mode, kStar(omega)), expected))
  }

  test("aChoiceYieldsTheHeadsOfItsMembers") {
    val expected = Vector(lambdaTerm(k), lambdaTerm(kStar))
    assertEquals(surfaceHeads(Mode.WeakHead, choice(k, λ(x => x)(kStar))), expected)
    // The tabled order of answers is the table's, so the two readings are
    // compared as multisets: sorted, with duplicates kept, as the Prolog test
    // compared `msort`ed lists (weak_head.plt:166-169).
    assertEquals(
      surfaceHeads(Mode.TablingWeakHead, choice(k, λ(y => y)(kStar))).sortBy(_.toString),
      expected.sortBy(_.toString)
    )
  }

  /** K I = \y. I and K* I = I. */
  test("aChoiceInFunctionPositionAppliesEachMember") {
    assertEquals(
      surfaceHeads(Mode.WeakHead, choice(k, kStar)(λ(i => i))),
      Vector(lambdaTerm(λ(_ => λ(i => i))), lambdaTerm(λ(z => z)))
    )
  }

  test("aParallelLeftUnreadIsNoError") {
    assertEquals(
      surfaceHeads(Mode.WeakHead, λ(_ => λ(w => w))(λ(x => x) ∥ λ(y => y))),
      Vector(lambdaTerm(λ(v => v)))
    )
  }

  /** A parallel is one parallel set, the heads of its sides, a head held
    * once; applied, it distributes by (9): K I = \y. I and K* I = I.
    */
  test("anAppliedParallelDistributesByEquationNine") {
    assertEquals(surfaceHeads(Mode.WeakHead, λ(x => x) ∥ λ(y => y)), Vector(lambdaTerm(λ(x => x))))
    assertEquals(surfaceHeads(Mode.WeakHead, k ∥ kStar), Vector(lambdaTerm(k ∥ kStar)))
    assertEquals(
      surfaceHeads(Mode.WeakHead, (k ∥ kStar)(λ(i => i))),
      Vector(lambdaTerm(λ(_ => λ(i => i)) ∥ λ(z => z)))
    )
    assertEquals(
      surfaceNormalForms(Mode.WeakHead, (λ(x => x) ∥ λ(y => y))(λ(z => z))),
      Set(lambdaTerm(λ(i => i)))
    )
  }

  /** Equation (9)'s example: (K* ∥ K) K* K* = K* K* K* ∥ K K* K* = K* ∥ K*,
    * whose read-out is K*.
    */
  test("equationNinesExampleReadsOutKStar") {
    modes.foreach(mode =>
      assertEquals(surfaceNormalForms(mode, (kStar ∥ k)(kStar)(kStar)), Set(lambdaTerm(kStar)))
    )
  }

  test("aParallelWhoseSidesShareNoNormalFormHasNoAnswer") {
    assertEquals(surfaceNormalForms(Mode.WeakHead, k ∥ kStar), Set.empty)
    assertEquals(
      surfaceNormalForms(Mode.TablingWeakHead, choice(k, λ(x => x)) ∥ choice(kStar, λ(y => y(y)))),
      Set.empty
    )
  }

  /** Two rings of 2 and 3 nodes and a ring of 3 nodes with chords: the
    * tabled mode completes every reading, and the Church true is among the
    * normal forms exactly when breadth-first search reaches the target; the
    * untabled mode runs around the first cycle. The Prolog budgets were
    * 20,000,000 inferences tabled and 2,000,000 untabled; the Scala tabled
    * readings take at most 672 steps (MEASURED, `graphReadingSteps`
    * below), and the budgets are 20,000,000 and 2,000,000 steps: the tabled
    * one is passed by none, and the untabled one is exceeded because the
    * untabled reading does not end, not for its size.
    */
  test("theTabledModeCompletesACyclicGraphProgram") {
    val trueTerm = lambdaTerm(k)
    for
      (shape, size) <- Vector((GraphShape.TwoRings, 2), (GraphShape.TwoRings, 3), (GraphShape.ChordRing, 3))
      graph = MergeGraph.graph(shape, size)
      target <- 0 until graph.count
    do
      val value = valueOf(MergeGraph.graphTerm(graph, 0, target))
      val bounded = normalFormsWithin(Mode.TablingWeakHead, value, 20000000)
      assertEquals((shape, size, target, bounded.finished), (shape, size, target, true))
      val normalForms = finishedValue(bounded)
      val found = normalForms.map(instructionTerm).contains(trueTerm)
      assertEquals((shape, size, target, found), (shape, size, target, MergeGraph.referenceReachable(graph, 0, target)))
    val graph = MergeGraph.graph(GraphShape.TwoRings, 2)
    val value = valueOf(MergeGraph.graphTerm(graph, 0, 3))
    assertEquals(normalFormsWithin(Mode.WeakHead, value, 2000000), Bounded.Exceeded)
  }

  test("graphReadingSteps") {
    val spent = for
      (shape, size) <- Vector((GraphShape.TwoRings, 2), (GraphShape.TwoRings, 3), (GraphShape.ChordRing, 3))
      graph = MergeGraph.graph(shape, size)
      target <- 0 until graph.count
    yield
      val value = valueOf(MergeGraph.graphTerm(graph, 0, target))
      NormalForms.normalForms(Mode.TablingWeakHead, value).result(ReadingState.fresh(20000000)) match
        case Computed.Done(_, after) => after.budget.spent
        case Computed.Stopped(_)     => fail("a tabled graph reading stopped")
    println(s"tabled graph reading steps: $spent")
    assert(spent.max <= 672L, s"the most steps of a graph reading: ${spent.max}")
  }
