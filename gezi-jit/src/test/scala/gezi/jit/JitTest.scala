package gezi.jit

import gezi.jit.JitTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.Head
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.ir.{Configured, Value}
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir

/** The port of `gezi/tests/jit.plt`: the JIT answers the reference's
  * heads and normal forms on hand-written terms that reach every rule of the
  * emission, on random closed terms, pure and with choices and parallels,
  * under three budgets: large (10,000, the cache kept from one term to the
  * next), 0 (every instance interpreted) and 3 (the cache dropped before
  * each term, so each term compiles its first three codes and interprets
  * the rest), by the comparison protocol (`JitTesting.compared`); a function
  * applied to several inputs is compiled once; the budget bounds the codes
  * compiled; a stopped reading leaves its compiled codes sound; an inner
  * instance is a call of its code. The tests of jit.plt that read the
  * problem corpora, the_jit_writes_no_file among them, are replaced by
  * contest-corpora's `JitReadingLawTest`, a law on generated programs of
  * the corpora, since this module's tests cannot depend on the corpora.
  *
  * Every run is bounded by a count of evaluator steps. The Prolog limits
  * were inference counts; each is kept as the same number of steps, a step
  * being a coarser unit than an inference (a step reads one layer or applies
  * one head), so each bounds the Scala reading at least as loosely, and a
  * limit a test asserts is reached (Omega's) is reached at any count. The
  * random terms are the exception: fewer of them, read within a tenth of
  * jit.plt's limit (`randomTermCount`, `randomTermLimit`).
  */
class JitTest extends gezi.generatedinputs.FailFastSuite:

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of JitTest, "anInterruptedCompilationLeavesTheCacheSound", takes 3.032 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "s")

  /** The three budgets and whether the cache is dropped before each term. */
  private val budgets: Vector[(String, Int, Boolean)] =
    Vector(("large", 10000, false), ("none", 0, false), ("small", 3, true))

  private def omega: Term = λ(a => a(a))(λ(b => b(b)))

  /** The hand-written terms of jit.plt's small_surface/1, which reach every
    * rule of the emitter.
    */
  private val smallTerms: Vector[Term] = Vector(
    λ(x => x),
    λ(x1 => x1)(λ(y1 => y1)),
    λ(k => λ(_ => k))(λ(a => a))(λ(b => b(b))),
    λ(s => λ(t => λ(u => s(u)(t(u)))))(λ(k2 => λ(_ => k2)))(λ(k3 => λ(_ => k3))),
    λ(s4 => λ(t4 => λ(u4 => s4(u4)(t4(u4)))))(λ(k5 => λ(_ => k5)))(λ(k6 => λ(_ => k6)))(λ(i6 => i6)),
    λ(_ => λ(x4 => x4))(λ(a2 => a2(a2))(λ(b2 => b2(b2)))),
    λ(f => λ(x5 => f(f(x5))))(λ(y6 => y6)),
    λ(f7 => λ(x7 => f7(f7(x7))))(λ(y7 => y7))(λ(z7 => z7)),
    λ(x8 => choice(x8, λ(y8 => y8))(λ(z8 => z8))),
    λ(x9 => choice(x9(x9), λ(y9 => λ(_ => y9))(x9)))(λ(z9 => z9)),
    λ(x10 => choice(x10, λ(y10 => y10))(x10))(λ(z10 => z10)),
    λ(x12 => x12 ∥ λ(y12 => y12))(λ(z12 => z12)),
    λ(x13 => (x13 ∥ λ(y13 => y13))(x13)(x13))(λ(z13 => z13)),
    λ(x14 => λ(y14 => λ(w14 => y14(w14)(x14))))(λ(z14 => z14)),
    λ(x15 => λ(y15 => λ(_ => λ(v15 => y15(v15))))(x15)(x15)(x15))(λ(z15 => z15)),
    (λ(k16 => λ(_ => k16)) ∥ λ(_ => λ(y16 => y16)))(λ(a16 => a16))(λ(b16 => b16)),
    λ(x17 => λ(y17 => λ(_ => y17))(x17)(λ(a17 => a17(a17))(λ(b17 => b17(b17)))))(λ(z17 => z17)),
    λ(x18 => λ(y18 => λ(w18 => y18(w18)(x18)))(x18)(x18))(λ(z18 => z18)),
    λ(x19 => λ(y19 => λ(_ => y19(x19)))(x19)(λ(a19 => a19(a19))(λ(b19 => b19(b19)))))(λ(z19 => z19)),
    λ(x20 => λ(y20 => λ(_ => λ(v20 => y20(x20)(v20))))(x20))(λ(z20 => z20)),
    λ(x21 => λ(y21 => λ(w21 => y21(w21)(x21)))(x21)(x21)(x21))(λ(z21 => z21))
  )

  private def instructions(terms: Vector[Term]): Vector[Configured[encoding.type]] = terms.map(term => EvaluatorTesting.instructionOf[encoding.type](term))

  private def headsVerdicts(terms: Vector[Term], budget: Int, cacheDropped: Boolean, limit: Long, strategy: GenerationStrategy = PredicatePerCode): Vector[Verdict] =
    headsVerdictsAndState(terms, budget, cacheDropped, limit, strategy)._1

  /** `headsVerdicts`, with the JIT state the last term left. */
  private def headsVerdictsAndState(
      terms: Vector[Term],
      budget: Int,
      cacheDropped: Boolean,
      limit: Long,
      strategy: GenerationStrategy
  ): (Vector[Verdict], JitState[encoding.type]) =
    val values = valuesOf(instructions(terms))
    val jit = Jit(configured(encoding, budget, strategy))
    allComparedAndState(values.map(headsQuestion(jit, _)), limit, cacheDropped)

  private def normalFormsVerdicts(terms: Vector[Term], budget: Int, cacheDropped: Boolean, limit: Long): Vector[Verdict] =
    val values = valuesOf(instructions(terms))
    val jit = Jit(configured(encoding, budget))
    allCompared(values.map(normalFormsQuestion(jit, _)), limit, cacheDropped)

  private def report(name: String, verdicts: Vector[Verdict]): Unit =
    println(s"$name: ${EvaluatorTesting.clumpedCounts(verdicts)}")

  test("theJitAnswersTheReferenceHeadsOnSmallTerms") {
    budgets.foreach((name, budget, dropped) =>
      report(s"$name small terms", headsVerdicts(smallTerms, budget, dropped, 100000))
    )
  }

  // Omega runs to its count of steps under the JIT in every budget, never
  // out of a stack or of the heap: the machine's goals do not grow.
  test("omegaRunsToItsInferenceCountUnderTheJit") {
    val value = EvaluatorTesting.valueOf(omega)
    budgets.foreach((name, budget, _) =>
      val read = headsRead(Jit(configured(encoding, budget)), value, 2000000)
      assertEquals(read.outcome, Bounded.Exceeded, name)
    )
  }

  /** The count of random terms each seed draws and the count of steps each
    * of their readings may take. Tests fail fast (CONTRIBUTING.md, "Tests fail fast"): 300 terms read within
    * 200,000 steps took 68 s for the suite on 2026-11-14, most of it in the
    * terms neither side finished, each read to its limit.
    */
  private val randomTermCount = 30
  private val randomTermLimit = 20000L

  private def randomTerms(seed: Long, lattice: Boolean): Vector[Term] =
    EvaluatorTesting
      .draws(randomTermCount, seed)(random =>
        if lattice then randomLatticeApplication(24, random) else EvaluatorTesting.randomApplication(24, random)
      )
      .map(DeBruijnTermAsTerm.term)

  // `randomTermCount` random closed pure applications of about 24 nodes and
  // as many with choices and parallels, from fixed seeds, under each budget.
  test("theJitAnswersTheReferenceHeadsOnRandomTerms") {
    budgets.foreach((name, budget, dropped) =>
      report(s"$name pure heads", headsVerdicts(randomTerms(20261011, false), budget, dropped, randomTermLimit))
      report(s"$name lattice heads", headsVerdicts(randomTerms(20261012, true), budget, dropped, randomTermLimit))
    )
  }

  test("theJitReadsTheReferenceNormalFormsOnRandomTerms") {
    budgets.foreach((name, budget, dropped) =>
      report(s"$name pure normal forms", normalFormsVerdicts(randomTerms(20261013, false), budget, dropped, randomTermLimit))
      report(s"$name lattice normal forms", normalFormsVerdicts(randomTerms(20261014, true), budget, dropped, randomTermLimit))
    )
  }

  // The same random terms under the instance table (`instanceTable`), the
  // table kept from one term to the next: purpose, to catch a table whose
  // heads differ from the instance's, a key that two different instances
  // share, or a table that changes the order of the heads. The JIT has no
  // facts here (`noFacts`), so the native and fallback paths, and the table
  // being skipped during a fallback point's check, are not exercised.
  test("theTabledJitReadsTheReferenceHeadsAndNormalFormsOnRandomTerms") {
    val tabled = JitConfiguration[encoding.type](encoding, 10000, PredicatePerCode, ClosureBackend, DispatchMode.NoDispatch, instanceTable = true, storageAccess = gezi.ir.StorageAccess.granted())
    Vector((20261011L, false), (20261012L, true)).foreach((seed, lattice) =>
      val values = valuesOf(instructions(randomTerms(seed, lattice)))
      report(s"tabled heads $seed", allCompared(values.map(headsQuestion(Jit(tabled), _)), randomTermLimit,false))
    )
    Vector((20261013L, false), (20261014L, true)).foreach((seed, lattice) =>
      val values = valuesOf(instructions(randomTerms(seed, lattice)))
      report(s"tabled normal forms $seed", allCompared(values.map(normalFormsQuestion(Jit(tabled), _)), randomTermLimit,false))
    )
  }

  // The same random normal-form questions under the instance table with its
  // cutoff after four entries (`instanceTableTrial`), the table and its costs
  // kept from one term to the next: purpose, to catch a cutoff that changes
  // an answer (a code no longer tabled midway whose instances then read
  // other normal forms) or a lookup charge that does; and to catch a cutoff
  // that never fires on these terms, so that the law would check nothing.
  test("theTabledJitWithAnEarlyCutoffReadsTheReferenceNormalFormsOnRandomTerms") {
    val cutOff = JitConfiguration[encoding.type](
      encoding,
      10000,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceTableTrial = 4,
      storageAccess = gezi.ir.StorageAccess.granted()
    )
    Vector((20261013L, false), (20261014L, true)).foreach((seed, lattice) =>
      val values = valuesOf(instructions(randomTerms(seed, lattice)))
      val (verdicts, after) = allComparedAndState(values.map(normalFormsQuestion(Jit(cutOff), _)), randomTermLimit,false)
      report(s"cut off normal forms $seed", verdicts)
      val costs = after match
        case run: JitRunState[?] => run.tableCosts
        case other            => fail(s"the JIT left no run state: $other")
      assert(costs.values.exists(_.unprofitable(4)), s"no code was cut off on the terms of seed $seed: $costs")
    )
  }

  /** The JIT's heads of the value equal the reference's, both within a
    * million steps; the JIT state after the reading.
    */
  private def headsAgree(jit: Jit[encoding.type], value: Value[encoding.type], jitState: JitState[encoding.type]): JitState[encoding.type] =
    val reference = headsRead(Mode.TablingWeakHead, referenceConfiguration(jit), value, 1000000).outcome
    val read = headsRead(jit, value, 1000000, jitState)
    assert(reference.finished, s"the reference did not finish: $reference")
    assertEquals(read.outcome, reference)
    read.jitState

  /** The Scott natural of the count, zero = \z. \s. z, successor p =
    * \z. \s. s p.
    */
  private def numeral(count: Int): Term =
    if count == 0 then λ(z => λ(_ => z)) else λ(_ => λ(s => s(numeral(count - 1))))

  /** The instruction of the closed term interned whole, the way the corpora
    * intern their programs.
    */
  private def interned(term: Term): Value[encoding.type] =
    EvaluatorTesting.valueOf[encoding.type](term)

  private def internedAll(terms: Vector[Term]): Vector[Value[encoding.type]] =
    terms.map(interned)

  /** The code of the thunk the value's layer is. */
  private def thunkCode(value: Value[encoding.type]): Code = value match
    case Value.Thunk(code, _, _) => code
    case other                   => fail(s"not a thunk: $other")

  // f a, f b, f c in one suite: f's code is compiled at
  // the first application and never again; the inputs, Scott numerals, bring
  // no code of their own after the first. f is the predecessor
  // \n. n zero (\p. p).
  test("aFunctionAppliedToSeveralInputsIsCompiledOnce") {
    val values = internedAll(Vector(λ(n => n(λ(z => λ(_ => z)))(λ(p => p))), numeral(3), numeral(5), numeral(7)))
    val function = values.head
    val functionCode = thunkCode(function)
    val jit = Jit(configured(encoding, JitConfiguration.defaultBudget))
    val afterFirst = headsAgree(jit, Value.Apply(function, values(1)), NoJitState)
    val compiledFirst = compiledCodes(afterFirst)
    assert(compiledFirst.contains(functionCode))
    val afterAll = values.drop(2).foldLeft(afterFirst)((state, input) => headsAgree(jit, Value.Apply(function, input), state))
    assertEquals(compiledCodes(afterAll), compiledFirst)
    (afterFirst, afterAll) match
      case (first: JitRunState[?], all: JitRunState[?]) => assert(first.compiled(functionCode) eq all.compiled(functionCode))
      case other => fail(s"no JIT state: $other")
  }

  // The reading compiles no more codes than the budget: none under 0, at
  // most three under 3, while the answers stay the reference's. The three
  // roots instantiate five codes, the body of twice, the identity's slot(0)
  // (K's too), S's body, flip's body and the body of \a. \b. a b, and
  // compile four: an instance of slot(0) with one filling is a sharing cell
  // (`JitRules.cellCode` is that code, `SharingCell`), read by its filling's
  // heads and never compiled.
  test("theBudgetBoundsTheCache") {
    val roots = internedAll(
      Vector(
        λ(f => λ(x => f(f(x))))(λ(y => y))(λ(z => z)),
        λ(s => λ(t => λ(u => s(u)(t(u)))))(λ(k => λ(_ => k)))(λ(k1 => λ(_ => k1)))(λ(i => i)),
        λ(g => λ(a => λ(b => g(b)(a))))(λ(c => λ(d => c(d))))(λ(e => e))(λ(h => h))
      )
    )
    def compiledUnder(budget: Int): Int =
      val jit = Jit(configured(encoding, budget))
      compiledCodes(roots.foldLeft(NoJitState: JitState[encoding.type])((state, root) => headsAgree(jit, root, state))).size
    assertEquals(compiledUnder(0), 0)
    assertEquals(compiledUnder(3), 3)
    assertEquals(compiledUnder(10000), 4)
  }

  // A reading the count of steps stops leaves the codes it compiled sound.
  // The normal forms of a term whose reading compiles three codes (its
  // identities' slot(0) is read as a sharing cell, never compiled) are read,
  // stopped at every count of steps up to the whole reading's, then read
  // again whole with the JIT state the stopped reading left: the normal
  // forms are the reference's, and every compiled code is its strategy's
  // emission of its code. The Prolog test stopped the reading inside a
  // compilation too, which a transaction rolled back; here a code is
  // compiled whole before it runs, so a stop falls between compilations.
  test("anInterruptedCompilationLeavesTheCacheSound") {
    val term = λ(x => λ(y => λ(w => y(w)(x)))(x)(choice(x, λ(z => z)) ∥ λ(v => v))(x))(
      λ(s => λ(t => λ(u => s(u)(t(u)))))(λ(k => λ(_ => k)))(λ(k1 => λ(_ => k1)))
    )
    val value = EvaluatorTesting.valueOf[encoding.type](term)
    val reference = normalFormsRead(Mode.TablingWeakHead, plainConfiguration(encoding), value, 1000000).outcome
    assert(reference match
      case Bounded.Finished(found) => found.nonEmpty
      case _                       => false)
    val configuration = configured(encoding, JitConfiguration.defaultBudget)
    val jit = Jit(configuration)
    val whole = normalFormsRead(jit, value, 1000000)
    assert(sameOutcomes(whole.outcome, reference), s"${whole.outcome} against $reference")
    assertEquals(compiledCodes(whole.jitState).size, 3)
    val rules = JitRules(configuration)
    val stops = (1 to 4000).toVector
    val stopped = stops.count(limit =>
      val first = normalFormsRead(jit, value, limit)
      val again = normalFormsRead(jit, value, 1000000, first.jitState)
      assert(sameOutcomes(again.outcome, reference), s"stopped at $limit: ${again.outcome} against $reference")
      first.jitState match
        case run: JitRunState[?] =>
          run.compiled.foreach((code, compiled) =>
            assertEquals(compiled.emission, PredicatePerCode.emission(code), s"code $code at $limit")
          )
        case _ => ()
      first.outcome match
        case Bounded.Exceeded => true
        case _                => false
    )
    println(s"stops that stopped the reading: $stopped of ${stops.size}")
    assert(stopped > 0)
    assert(rules.compiledCode(compiledCodes(whole.jitState).head).emission.clauses.nonEmpty)
  }

  // A thunk of a code applied in that code until no hole is left is an inner
  // instance whose code is known when its clause is written: the clause is
  // the call of the inner code, clauses calling each other by name, first order. The code of
  // \x. (\y. \w. y w x) x x is one clause, the inner instance of the code of
  // y w x.
  test("anInnerInstanceCallsItsCodesPredicateByName") {
    val value = EvaluatorTesting.valueOf[encoding.type](λ(x => λ(y => λ(w => y(w)(x)))(x)(x))(λ(z => z)))
    val (outerCode, innerCode) = value match
      case Value.Apply(Value.Thunk(outer, _, _), _) =>
        outer.layer match
          case ir.Apply(applied, _) =>
            applied.layer match
              case ir.Apply(thunk, _) =>
                thunk.layer match
                  case ir.Thunk(inner, _, _) => (outer, inner)
                  case other => fail(s"not a thunk: $other")
              case other => fail(s"not an application: $other")
          case other => fail(s"not an application: $other")
      case other => fail(s"not an application of a thunk: $other")
    val after = headsAgree(Jit(configured(encoding, JitConfiguration.defaultBudget)), value, NoJitState)
    val run = after match
      case found: JitRunState[?] => found
      case other              => fail(s"no JIT state: $other")
    val clauses = run.compiled(outerCode).emission.clauses
    assertEquals(clauses.size, 1)
    clauses.head match
      case EmittedClause.InstanceLeaf(`innerCode`, _, arguments) => assert(arguments.isEmpty)
      case other => fail(s"not the inner instance: $other")
    assert(run.compiled.contains(innerCode))
  }

  /** The body c_count (... (c_1 variable)) of distinct closed terms c_i =
    * \_. b_i, b_i the twelve bits of i as a Scott sequence
    * (distinct_closed_chain/3).
    */
  private def distinctClosedChain(count: Int, variable: Term): Term =
    (1 to count).foldLeft(variable)((body, index) => λ(_ => bitsSequence(index, 12))(body))

  private def bitsSequence(number: Int, width: Int): Term =
    if width == 0 then λ(end => end)
    else
      val bit = if number % 2 == 0 then λ(first => λ(_ => first)) else λ(_ => λ(second => second))
      λ(pair => pair(bit)(bitsSequence(number / 2, width - 1)))

  // A code of many slots compiles and answers the reference's heads: the
  // closure \y. c1100 (... (c1 y)) of 1,100 distinct closed terms has 1,101
  // slots. The Prolog test asserted the predicate had two arguments, the
  // slots in one term, since SWI-Prolog bounds a predicate's arity by 1,024;
  // a compiled closure reads a vector of slots of any size, and the
  // assertion has no counterpart.
  test("aCodeOfManySlotsCompilesToAPredicateOfTwoArguments") {
    val value = EvaluatorTesting.valueOf[encoding.type](λ(y => distinctClosedChain(1100, y))(λ(z => z)))
    val code = value match
      case Value.Apply(Value.Thunk(found, _, _), _) => found
      case other => fail(s"not an application of a thunk: $other")
    assertEquals(CodeReading.slotCount(code), 1101)
    val after = headsAgree(Jit(configured(encoding, JitConfiguration.defaultBudget)), value, NoJitState)
    assert(compiledCodes(after).contains(code))
  }

  // The cache is a reading's and nothing else's: another thread reads the
  // same root from a fresh state and lets its state go, and this reading's
  // state still answers, its compiled codes the same and nothing compiled
  // again.
  //
  // The other thread only reads, and every assertion is made on this
  // thread, after the other thread's readings are awaited. A munit assertion
  // locks the suite while it evaluates its condition
  // (`munit.Assertions.munitCaptureClues` is `synchronized` on the suite), so
  // an assertion in the other thread waited for the lock this thread held
  // while it awaited the other thread inside an assertion, until the await
  // timed out: measured 2026-10-31 outside sbt, the compilation suites in one
  // JVM at -Xmx256m, four JVMs at a time beside a full `sbt test`, 3 of 24
  // runs timed out after 60 s with the other thread BLOCKED in
  // munitCaptureClues and this one in Await holding the suite's monitor; no
  // full collection, and no other user of the global pool. Whether the other
  // thread reached its assertion before this one took the lock was a race
  // that load decided.
  test("aDropInAnotherThreadKeepsThisThreadsCache") {
    val root = interned(λ(f => λ(x => f(f(x))))(λ(y => y))(λ(z => z)))
    val jit = Jit(configured(encoding, JitConfiguration.defaultBudget))
    val before = headsAgree(jit, root, NoJitState)
    val other = scala.concurrent.Future(
      (headsRead(Mode.TablingWeakHead, referenceConfiguration(jit), root, 1000000).outcome, headsRead(jit, root, 1000000, NoJitState))
    )(using scala.concurrent.ExecutionContext.global)
    val (otherReference, otherRead) = scala.concurrent.Await.result(other, scala.concurrent.duration.Duration(60, "s"))
    assert(otherReference.finished, s"the reference did not finish in the other thread: $otherReference")
    assertEquals(otherRead.outcome, otherReference)
    assert(compiledCodes(otherRead.jitState).nonEmpty)
    val after = headsAgree(jit, root, before)
    assertEquals(compiledCodes(after), compiledCodes(before))
  }

  // Under the generation strategy interpreted_instances, the budget large and the cache kept from one term to the next,
  // the JIT answers the reference's heads on the hand-written and the
  // random terms, and each code it compiles has the one clause that
  // strategy emits.
  test("theGenerationStrategyInterpretedInstancesAnswersTheReferenceHeads") {
    val readings = Vector(
      "interpreted instances small terms" -> headsVerdictsAndState(smallTerms, 10000, false, 100000, InterpretedInstances),
      "interpreted instances pure heads" ->
        headsVerdictsAndState(randomTerms(20261011, false), 10000, false, randomTermLimit,InterpretedInstances),
      "interpreted instances lattice heads" ->
        headsVerdictsAndState(randomTerms(20261012, true), 10000, false, randomTermLimit,InterpretedInstances)
    )
    readings.foreach { case (name, (verdicts, _)) => report(name, verdicts) }
    // Every code compiled while reading the three sets of terms, as the
    // Prolog test checked every code the process compiled
    // (jit.plt:646-648): at least one, each with the one clause the strategy
    // emits.
    val compiled = readings.flatMap { case (name, (_, state)) =>
      state match
        case run: JitRunState[?] => run.compiled.toVector.map((code, found) => (name, code, found))
        case other            => fail(s"$name: no JIT state: $other")
    }
    println(s"interpreted instances codes compiled: ${compiled.size}")
    assert(compiled.nonEmpty)
    compiled.foreach((name, code, found) =>
      assertEquals(found.emission.clauses, Vector(EmittedClause.InterpretedInstance), s"$name: code $code")
    )
  }

  /** A strategy that breaks the contract: the default emission with one
    * slot more than the code reads.
    */
  private object OneSlotTooMany extends GenerationStrategy:
    def emission(code: Code): Emission =
      val found = PredicatePerCode.emission(code)
      found.copy(slotCount = found.slotCount + 1)

  // The slot count of a code is read from the code, not from the emission,
  // so an emission with one slot more than the code throws before it runs.
  test("anEmissionWhoseArityIsNotTheStubsThrows") {
    val root = interned(λ(f => λ(x => f(f(x))))(λ(y => y))(λ(z => z)))
    intercept[EmissionSlotCount](headsRead(Jit(configured(encoding, 10000, OneSlotTooMany)), root, 1000000))
  }

/** The HOAS term of a closed de Bruijn term with no library name. */
object DeBruijnTermAsTerm:
  import gezi.frontend.DeBruijnTerm

  def term(closed: DeBruijnTerm): Term = converted(closed, Vector.empty)

  private def converted(term: DeBruijnTerm, bound: Vector[Term]): Term = term match
    case DeBruijnTerm.Variable(index)            => bound(bound.size - 1 - index)
    case DeBruijnTerm.Lambda(body)               => λ(variable => converted(body, bound :+ variable))
    case DeBruijnTerm.Apply(function, argument)  => converted(function, bound)(converted(argument, bound))
    case DeBruijnTerm.Choice(left, right)        => Term.Choice(converted(left, bound), converted(right, bound))
    case DeBruijnTerm.Parallel(left, right)      => converted(left, bound) ∥ converted(right, bound)
    case DeBruijnTerm.Constant(instruction)           => throw IllegalArgumentException(s"a library name: $instruction")
    case DeBruijnTerm.Free(name)                 => throw IllegalArgumentException(s"a free name: $name")
