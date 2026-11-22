package gezi.jit

import gezi.saturation.StopSignal
import gezi.jit.JitTesting.compiledCodes
import gezi.strategies.BaselineRounds
import gezi.jit.JitTesting.counts
import gezi.jit.NativesTesting.consNative
import gezi.jit.NativesTesting.falseNative
import gezi.jit.NativesTesting.nilNative
import gezi.jit.NativesTesting.normalFormLimit
import gezi.jit.NativesTesting.successorNative
import gezi.jit.NativesTesting.trueNative
import gezi.jit.NativesTesting.normalFormsSpent
import gezi.weakhead.Bounded
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.Value
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.StandardLibrary
import gezi.strategies.DispatchDecision
import gezi.strategies.DispatchStrategies
import gezi.strategies.DispatchStrategy
import gezi.strategies.FixpointReport
import gezi.strategies.NativeRouteCompilation
import gezi.strategies.Round
import gezi.strategies.Schedule
import gezi.strategies.StrategyTesting
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.hotspot.Cache
import gezi.hotspot.baselines.BaselineCaches
import gezi.saturation.End
import gezi.ir.Instruction

/** The port of `gezi/tests/native_route_compilation.plt`, whose file
  * comment this follows: a program over the library terms of
  * `JitTesting.libraryTermsFile`, each a member read by projection, goes through
  * the front end, its occurrences tagged, and a schedule of
  * `gezi.strategies.NativeRouteCompilation` (the type check, which puts
  * the typed version beside each application of HM's rule, then the
  * erasure of the tags, or, for a program beyond HM, a round with the beta
  * rule on the program's closures before them); the framework's entry
  * (`StrategyDispatch.dispatched`) runs the schedule and refines its output,
  * and the JIT reads the refined term under the strategy's mode, the
  * strategy `fallback` unless a test says otherwise. The library is the
  * Prolog test's, compiled with the Prolog backend's checks (naturals as big
  * integers, booleans as truth values, double and even as natives). Each
  * program's normal forms under the JIT are the reference's reading of the
  * program as written, and the run decodes nothing.
  *
  * Departures from the Prolog:
  *
  *   - The programs are written in the HOAS,
  *     their library terms closed instructions (`JitTesting.libraryTerm`),
  *     so no name is resolved; the knowledge of a round is a round of the
  *     rounds fixture (`StrategyTesting.round`).
  *   - A reading is bounded by `NativesTesting.normalFormLimit`, 2,000,000
  *     evaluator steps, where the Prolog test read within 10,000,000
  *     inferences.
  *   - The Prolog process kept one store, one strategy cache and one JIT
  *     cache for the whole file; here a run starts from an empty dispatch
  *     cache and no JIT state (`Suite.fresh`), except where a test threads
  *     them from one run to the next, as the tests of costs and of one
  *     function's tests do. No assertion
  *     of the Prolog test reads what an earlier test compiled.
  *   - The tests of costs (`the_runs_check_costs_an_element_do_not_grow`,
  *     `a_recursive_functions_run_costs_a_level_do_not_grow` and
  *     `a_closures_naturals_run_costs_a_successor_do_not_grow`) count the
  *     reading's evaluator steps, a deterministic count, where the Prolog
  *     counted SWI-Prolog's inferences of the same reading; as there, the
  *     compilation is not counted.
  *
  * The strategy `strict` is declared here as an entry would declare one
  * (jit.pl, DISPATCH STRATEGIES; a backend may drop the input that is not
  * specialized and report an error): at a fallback point whose check does not hold it rejects the
  * operand. The baseline offers no rejecting strategy
  * (`gezi.strategies.DispatchStrategies`).
  */
class NativeRouteCompilationTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of NativeRouteCompilationTest, "theRunsCheckCostsAnElementDoNotGrow", takes 56.781 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(90, "s")

  /** The library, its facts, the type check's round, the three schedules and the two configurations, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => facts,
      _ => typeCheckKnowledge,
      _ => hindleyMilnerSchedule,
      _ => beyondSchedule,
      _ => costSchedule,
      _ => fallbackConfiguration,
      _ => strictConfiguration
    )

  /** The native route's library with the Prolog backend, the one field of
    * tests/library_fixtures/native_route_with_prolog_backend.lambdalattice,
    * checked by the backend.
    */
  private lazy val library: StandardLibrary =
    LibraryFiles.compiled("tests/library_fixtures/native_route_with_prolog_backend.lambdalattice", Vector(BackendChecks))

  private lazy val facts = BackendFacts.of(library)

  /** The knowledge of the type check, the rounds fixture's
    * `prolog_backend_type_check`: the HM lemmas in the zero universe, with
    * the schemes of native_types' names, the schemes of native_arithmetic's,
    * and the Prolog backend's shapes, whose candidacies write the typed
    * versions.
    */
  private lazy val typeCheckKnowledge: Instruction = StrategyTesting.round("prolog_backend_type_check")

  /** The budget of each round is 6,000 instances, the Prolog test's:
    * measured there 2026-10-29, the largest round, the type check of the
    * fold of successor twice over successor^64 zero, reaches its fixed point
    * at 3,910, linear in the program; the type check of even (double^64
    * (successor zero)) at 1,606.
    */
  private lazy val hindleyMilnerSchedule: Vector[Round] =
    BaselineRounds.nativeRouteSchedule(library, typeCheckKnowledge, 6000)

  private lazy val beyondSchedule: Vector[Round] =
    NativeRouteCompilation.beyondHindleyMilnerSchedule(
      library.index,
      BaselineRounds.lemmas(library, StrategyTesting.round("closure_application")),
      BaselineRounds.lemmas(library, typeCheckKnowledge),
      BaselineRounds.lemmas(library, StrategyTesting.round("occurrence_erasure")),
      6000,
      BaselineRounds.modules
    )

  /** The schedule of the tests of costs, each round within 20,000
    * instances, the Prolog test's: measured there 2026-10-30, the type check
    * reaches its fixed point at 5,268 instances on the numeral of 128,
    * 15,379 on the list of 128, 18,426 on the same list ending in
    * `cons false nil`, 8,126 on `successor` applied to the list of 128
    * zeros, and 5,172 on the count of successor^128 zero.
    */
  private lazy val costSchedule: Vector[Round] =
    BaselineRounds.nativeRouteSchedule(library, typeCheckKnowledge, 20000)

  private val fallback: DispatchStrategy = DispatchStrategies.fallback

  private val strict: DispatchStrategy = DispatchStrategy("strict", DispatchDecision.Rejected)

  /** One configuration of the JIT for each dispatch strategy, built once:
    * a JIT state is read under the configuration it was built under.
    */
  private lazy val fallbackConfiguration = configurationOf(fallback)

  private lazy val strictConfiguration = configurationOf(strict)

  private def configurationOf(dispatch: DispatchStrategy): JitConfiguration =
    JitConfiguration(facts, JitConfiguration.defaultBudget, PredicatePerCode, ClosureBackend, DispatchMode.Dispatch(dispatch), instanceTable = false)

  private def configuration(dispatch: DispatchStrategy): JitConfiguration =
    if dispatch == strict then strictConfiguration else fallbackConfiguration

  // ---- the library terms, members of JitTesting.libraryTermsFile ----

  private val zero = JitTesting.libraryTerm("zero")
  private val successor = JitTesting.libraryTerm("successor")
  private val nil = JitTesting.libraryTerm("nil")
  private val cons = JitTesting.libraryTerm("cons")
  private val falseName = JitTesting.libraryTerm("false")
  private val trueName = JitTesting.libraryTerm("true")
  private val konstant = JitTesting.libraryTerm("konstant")
  private val compose = JitTesting.libraryTerm("compose")
  private val natFold = JitTesting.libraryTerm("nat_fold")
  private val listFold = JitTesting.libraryTerm("list_fold")
  private val booleanNot = JitTesting.libraryTerm("boolean_not")
  private val fixpoint = JitTesting.libraryTerm("fixpoint")
  private val double = JitTesting.libraryTerm("double")
  private val even = JitTesting.libraryTerm("even")

  // ---- the runs ----

  /** What the runs of a test share, threaded from one run to the next as
    * the Prolog process kept them: the cache service, which the runs read
    * and write in place, and the JIT state.
    */
  private final case class Suite(cache: Cache, jitState: JitState)

  private object Suite:
    def fresh: Suite = Suite(BaselineCaches.provider(), NoJitState)

  /** What a run of a compiled program read: its normal forms, sorted by
    * text; the decodings, the calls of each native called and the steps of
    * the reading; the codes the reading compiled and the runs of a schedule
    * the dispatch took.
    */
  private final case class Run(
      answers: Vector[Instruction],
      decodings: Long,
      calls: Map[NativeName, Long],
      steps: Long,
      codesCompiled: Int,
      typings: Int
  )

  /** The tagged program interned (`program_instruction/3`, its tagged
    * part), with the suite unchanged.
    */
  private def programInput(suite: Suite, program: Term): (Suite, Instruction) =
    (suite, StrategyTesting.programInput(library, program))

  /** Each round of the schedule on the input reaches its fixed point, read
    * from a run of the schedule of its own, since the dispatch keeps no
    * report.
    */
  private def roundsReachTheirFixedPoints(schedule: Vector[Round], input: Instruction): Unit =
    Schedule.run(library.index, Vector(input), schedule, StopSignal.NeverStopped).records.foreach(record =>
      record.report match
        case FixpointReport(End.FixedPoint(_)) => ()
        case other                            => fail(s"a round of the schedule ended $other")
    )

  /** The tagged input compiled under the strategy of the dispatch strategy
    * and the schedule and read under its mode, from the suite
    * (`dispatched_run/3`): the run finishes. The suite after.
    */
  private def dispatchedRun(suite: Suite, dispatch: DispatchStrategy, schedule: Vector[Round], input: Instruction): (Suite, Run) =
    val Dispatched(refined, _, scheduleRan) =
      StrategyDispatch.dispatched(CompilationStrategy(dispatch, schedule), input, facts, suite.cache, StopSignal.NeverStopped)
    val read = normalFormsSpent(
      Mode.Jit(Jit(configuration(dispatch))),
      refined,
      normalFormLimit,
      suite.jitState
    )
    val answers = read.outcome match
      case Bounded.Finished(found) => found
      case other                   => fail(s"the compiled run did not finish: $other")
    val before = counts(suite.jitState)
    val after = counts(read.jitState)
    val calls = after.callsByNative.collect {
      case (native, count) if count > before.callsOf(native) => native -> (count - before.callsOf(native))
    }
    val run = Run(
      answers,
      after.decodings - before.decodings,
      calls,
      read.steps,
      compiledCodes(read.jitState).size - compiledCodes(suite.jitState).size,
      if scheduleRan then 1 else 0
    )
    (Suite(suite.cache, read.jitState), run)

  /** The program compiled under the strategy of the dispatch strategy and
    * the schedule, each round reaching its fixed point, and run under its
    * mode (`compiled_run/6`).
    */
  private def compiledRun(dispatch: DispatchStrategy, schedule: Vector[Round], program: Term): Run =
    val (suite, input) = programInput(Suite.fresh, program)
    roundsReachTheirFixedPoints(schedule, input)
    dispatchedRun(suite, dispatch, schedule, input)._2

  /** The outcome of the program as written, neither tagged nor typed, read
    * under the mode within the reading's limit (`as_written_outcome/4`).
    */
  private def asWrittenOutcome(mode: Mode, program: Term): Bounded[Vector[Instruction]] =
    val input = JitTesting.termInstruction(program)
    normalFormsSpent(mode, input, normalFormLimit).outcome

  /** The normal forms of the program as written under the reference's
    * reading, tabling(weak_head) (`reference_answers/2`).
    */
  private def referenceAnswers(program: Term): Vector[Instruction] =
    asWrittenOutcome(Mode.TablingWeakHead, program) match
      case Bounded.Finished(found) => found
      case other                   => fail(s"the reference did not finish: $other")

  /** The program's compiled run reads the reference's normal forms of the
    * program as written, decodes nothing and calls at least one native
    * (`compiled_like_the_reference/3`).
    */
  private def compiledLikeTheReference(schedule: Vector[Round], program: Term): Run =
    val run = compiledRun(fallback, schedule, program)
    assertEquals(run.answers, referenceAnswers(program))
    assertEquals(run.decodings, 0L)
    assert(run.calls.nonEmpty, "the run called no native")
    run

  /** The program's compiled run reads the reference's normal forms of the
    * expected program and decodes nothing, while the reference reads no
    * answer of the program as written within its count under
    * tabling(weak_head) (`compiled_beyond_the_reference/4`).
    */
  private def compiledBeyondTheReference(schedule: Vector[Round], program: Term, expected: Term): Run =
    val run = compiledRun(fallback, schedule, program)
    assertEquals(run.answers, referenceAnswers(expected))
    assertEquals(run.decodings, 0L)
    assert(!asWrittenOutcome(Mode.TablingWeakHead, program).finished, "the reference read the program under tabling")
    run

  /** The steps of the JIT's reading of the program compiled under
    * `fallback` and the schedule, interned into the suite and run from it
    * (`run_inferences/3`, counting steps). The suite after.
    */
  private def runSteps(suite: Suite, schedule: Vector[Round], program: Term): (Suite, Long) =
    val (withInput, input) = programInput(suite, program)
    val (after, run) = dispatchedRun(withInput, fallback, schedule, input)
    (after, run.steps)

  /** The steps of the runs at the sizes 8, 32 and 128 cost each element no
    * more from 32 to 128 than from 8 to 32, after a run at 4 (the Prolog
    * tests' `Before is (Middle - Small) / 24, After is (Large - Middle) / 96,
    * After =< Before`).
    */
  private def runCostsDoNotGrow(label: String, schedule: Vector[Round], program: Int => Term): Unit =
    val (warm, _) = runSteps(Suite.fresh, schedule, program(4))
    val (afterSmall, small) = runSteps(warm, schedule, program(8))
    val (afterMiddle, middle) = runSteps(afterSmall, schedule, program(32))
    val (_, large) = runSteps(afterMiddle, schedule, program(128))
    val before = (middle - small).toDouble / 24
    val after = (large - middle).toDouble / 96
    println(s"$label: $small, $middle and $large steps at 8, 32 and 128")
    assert(after <= before, s"$label: $small, $middle and $large steps at 8, 32 and 128")

  // ---- the programs ----

  private def numeral(size: Int): Term = (1 to size).foldLeft(zero)((value, _) => successor(value))

  /** double applied the count times to the base. */
  private def doubles(count: Int, base: Term): Term = (1 to count).foldLeft(base)((value, _) => double(value))

  /** The size copies of the element consed onto the tail. */
  private def listEnding(size: Int, element: Term, tail: Term): Term =
    (1 to size).foldLeft(tail)((list, _) => cons(element)(list))

  /** First-order data of the family at the size (`data_value/3`):
    * successor^size zero; the list of size copies of `successor zero`; the
    * same list ending in `cons false nil`, which HM rejects; and
    * `successor` applied to the list of size zeros, which HM rejects.
    */
  private def dataValue(family: String, size: Int): Term = family match
    case "numerals"                 => numeral(size)
    case "lists"                    => listEnding(size, successor(zero), nil)
    case "list_ending_in_a_boolean" => listEnding(size, successor(zero), cons(falseName)(nil))
    case "successor_of_a_list"      => successor(listEnding(size, zero, nil))
    case other                      => fail(s"no family $other")

  /** A function the program defines by fixpoint, the count of the
    * successors of its argument, applied to successor^size zero
    * (`recursive_count/2`).
    */
  private def recursiveCount(size: Int): Term =
    fixpoint(λ(self => λ(t => t(zero)(λ(u => successor(self(u)))))))(numeral(size))

  /** The closure \y. successor^size y applied to zero (`closure_chain/2`). */
  private def closureChain(size: Int): Term =
    λ(variable => (1 to size).foldLeft(variable)((body, _) => successor(body)))(zero)

  /** The program beyond HM: a closure parameter used at nat -> nat and at
    * boolean -> boolean, its argument the identity closure.
    */
  private val beyondHindleyMilnerProgram: Term =
    λ(g => natFold(g(falseName))(booleanNot)(g(successor(zero))))(λ(x => x))

  /** The same use of a closure parameter, around the parity of double^size
    * (successor zero).
    */
  private def beyondBothProgram(size: Int): Term =
    λ(g => booleanNot(g(even(g(doubles(size, successor(zero)))))))(λ(x => x))

  /** A pair of the two values, written as the program's own closure. */
  private def pair(first: Term, second: Term): Term = λ(x => λ(y => λ(q => q(x)(y))))(first)(second)

  private val rejectedPrograms: Vector[Term] = Vector(
    cons(successor(zero))(cons(falseName)(nil)),
    successor(cons(zero)(nil)),
    booleanNot(cons(trueName)(nil)),
    booleanNot(natFold(zero)(successor)(successor(zero))),
    natFold(zero)(trueName)(successor(zero))
  )

  /** Programs of the coverage table of tests/native_route.plt (deleted with
    * the old e-graph) with lists, closures and polymorphic names used at two
    * types (`covered_program/1`).
    */
  private val coveredPrograms: Vector[Term] = Vector(
    listFold(zero)(konstant(successor))(cons(zero)(nil)),
    cons(cons(successor(zero))(nil))(cons(nil)(nil)),
    λ(f => λ(a => f(f(a))))(successor)(zero),
    λ(outer => λ(inner => λ(a => outer(inner(a)))))(successor)(successor)(zero),
    listFold(nil)(λ(head => λ(accumulated => cons(successor(head))(accumulated))))(cons(zero)(nil)),
    λ(x => x)(successor)(λ(y => y)(zero)),
    cons(konstant(successor(zero))(successor(zero)))(cons(konstant(successor(zero))(successor))(nil)),
    natFold(zero)(successor)(successor(successor(zero)))
  )

  /** Programs nominal HM types through a Maybe: a Maybe of a list and a
    * Maybe of a boolean, whose just is successor's term
    * (`strict_rejected_typed_program/1` of the Prolog tests, which a
    * rejecting strategy threw on).
    */
  private val maybePrograms: Vector[Term] = Vector(
    successor(cons(zero)(nil))(nil)(λ(items => cons(zero)(items))),
    successor(falseName)(trueName)(booleanNot)
  )

  // ---- the tests ----

  test("numerals") {
    Vector(1, 2, 8).foreach(size => compiledLikeTheReference(hindleyMilnerSchedule, numeral(size)))
  }

  // The fold of successor twice over n is 2n, and the run builds every
  // successor in the representation: successor's native is called for the
  // literal's size and the steps' 2 size.
  test("theFoldOfAComposition") {
    Vector(1, 4, 16).foreach { size =>
      val program = natFold(zero)(compose(successor)(successor))(numeral(size))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"size $size")
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(successorNative), Some(3L * size), s"size $size")
      assertEquals(run.answers, referenceAnswers(numeral(2 * size)), s"size $size")
    }
  }

  // A fold's value given to a typed constructor, the step a library
  // function or a closure of the program that applies successor to the
  // recursive value: successor's native is called for the literal's size and
  // the steps' 2 size; the outer one takes its library term's head, its operand a
  // decode point not yet represented (a constructor is not strict in its
  // field, `Jit.nativeAppliedHeads`).
  test("aFoldUnderATypedConstructor") {
    for
      size <- Vector(1, 4, 16)
      step <- Vector(compose(successor)(successor), λ(x => successor(successor(x))))
    do
      val program = successor(natFold(zero)(step)(numeral(size)))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"size $size")
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(successorNative), Some(3L * size), s"size $size")
  }

  // A fold whose step is double, a library term the backend binds to the native
  // natural_double: the run calls natural_double once a step, decodes
  // nothing and reads the reference's normal forms.
  test("aFoldWhoseStepIsDouble") {
    Vector(2, 4, 8).foreach { size =>
      val program = even(natFold(successor(zero))(double)(numeral(size)))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"size $size")
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(NativeName.Function("natural_double")), Some(size.toLong), s"size $size")
    }
  }

  test("booleans") {
    Vector(
      booleanNot(trueName),
      booleanNot(booleanNot(trueName)),
      booleanNot(booleanNot(booleanNot(falseName)))
    ).foreach(program => compiledLikeTheReference(hindleyMilnerSchedule, program))
  }

  test("programsWithListsAndClosures") {
    coveredPrograms.foreach(program => compiledLikeTheReference(hindleyMilnerSchedule, program))
  }

  // A list HM types runs in the representation of the lists of naturals:
  // the typed constructors build every cell with cons's native, list_fold takes
  // the list apart in the representation, and the run decodes nothing.
  test("aListRunsInItsRepresentation") {
    Vector(4, 8).foreach { size =>
      val program = listFold(zero)(λ(_ => λ(length => successor(length))))(dataValue("lists", size))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"size $size")
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(consNative), Some(size.toLong), s"size $size")
      assertEquals(run.calls.get(nilNative), Some(1L), s"size $size")
    }
  }

  // A fold whose step has two parameters builds every cell of its result in
  // the representation of the lists of naturals: cons's native 2n times over n
  // zeros, n for the input and n for the result.
  test("aFoldWithAStepOfTwoParametersBuildsItsCellsNatively") {
    Vector(4, 8).foreach { size =>
      val program = listFold(nil)(λ(head => λ(tail => cons(successor(head))(tail))))(listEnding(size, zero, nil))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"size $size")
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(consNative), Some(2L * size), s"size $size")
    }
  }

  // Every cell of these lists HM types is built by cons's native (the Prolog
  // test's comment says why each cell is a candidate).
  test("theCellsOfListsHindleyMilnerTypesAreBuiltNatively") {
    val one = successor(zero)
    Vector(
      cons(one)(cons(zero)(nil)) -> 2L,
      cons(zero)(cons(one)(nil)) -> 2L,
      cons(zero)(cons(zero)(cons(zero)(cons(one)(nil)))) -> 4L,
      cons(nil)(cons(cons(one)(nil))(nil)) -> 3L,
      cons(cons(trueName)(nil))(cons(cons(falseName)(nil))(nil)) -> 4L,
      cons(cons(one)(nil))(cons(cons(one)(nil))(nil)) -> 4L,
      cons(cons(zero)(cons(one)(nil)))(nil) -> 3L,
      cons(nil)(cons(cons(zero)(cons(one)(nil)))(nil)) -> 4L,
      listFold(nil)(λ(items => λ(lengths => cons(listFold(zero)(λ(_ => λ(length => successor(length))))(items))(lengths))))(
        cons(cons(one)(nil))(cons(cons(zero)(cons(zero)(nil)))(nil))
      ) -> 7L
    ).zipWithIndex.foreach { case ((program, cells), index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"program $index")
      assertEquals(run.decodings, 0L, s"program $index")
      assertEquals(run.calls.get(consNative), Some(cells), s"program $index")
    }
  }

  // Programs HM rejects, compiled by the schedule of the programs HM types:
  // the refinement's fallback points keep the untyped versions beside the
  // typed ones, and the run reads the reference's normal forms.
  test("programsHindleyMilnerRejects") {
    rejectedPrograms.zipWithIndex.foreach((program, index) =>
      assertEquals(compiledRun(fallback, hindleyMilnerSchedule, program).answers, referenceAnswers(program), s"program $index")
    )
  }

  // Programs HM types over data of their own: each reads the reference's
  // normal forms, decodes nothing and computes its fields in the
  // representation, by the native named.
  test("programsOverTheirOwnDataComputeTheirFieldsNatively") {
    Vector(
      λ(p => p(λ(a => λ(_ => a))))(pair(successor(zero), zero)) -> successorNative,
      λ(p => p(λ(a => λ(b => natFold(a)(successor)(b)))))(pair(successor(zero), successor(successor(zero)))) -> successorNative,
      successor(successor(zero))(zero)(λ(v => successor(v))) -> successorNative,
      λ(x => λ(l => λ(_ => l(x))))(successor(zero))(λ(v => successor(v)))(λ(_ => zero)) -> successorNative,
      λ(a => λ(x => λ(b => λ(_ => λ(n => n(a)(x)(b))))))(λ(leaf => λ(_ => leaf)))(successor(zero))(λ(leaf => λ(_ => leaf)))(zero)(
        λ(_ => λ(v => λ(_ => successor(v))))
      ) -> successorNative,
      λ(p => p(λ(a => λ(_ => a))))(pair(cons(successor(zero))(nil), nil)) -> consNative
    ).foreach((program, native) =>
      assert(compiledLikeTheReference(hindleyMilnerSchedule, program).calls.contains(native), native.toString)
    )
  }

  // Programs HM types that compute inside a closure's body: the contracts
  // at the closure's boundary and the checks of the fallback points in the
  // body reach the natives named.
  test("programsComputingInAClosuresBodyRunNatively") {
    Vector(
      λ(f => f(successor(zero)))(λ(x => natFold(x)(successor)(successor(successor(zero))))) -> successorNative,
      λ(g => g(g(zero)))(λ(x => successor(successor(x)))) -> successorNative,
      λ(f => cons(f(zero))(nil))(λ(x => successor(x))) -> consNative,
      λ(f => f(cons(successor(zero))(cons(zero)(nil))))(λ(items => listFold(zero)(λ(_ => λ(n => successor(n))))(items))) ->
        successorNative,
      λ(f => f(f(trueName)))(λ(b => booleanNot(b))) -> falseNative
    ).foreach((program, native) =>
      assert(compiledLikeTheReference(hindleyMilnerSchedule, program).calls.contains(native), native.toString)
    )
  }

  // A value beside infinite data it never demands: the fallback points of
  // the typed versions are read only where the run demands them.
  test("infiniteDataNeverDemanded") {
    Vector(
      konstant(successor(zero))(fixpoint(λ(y => successor(y)))),
      konstant(successor(zero))(fixpoint(λ(zeros => cons(zero)(zeros))))
    ).foreach(program => compiledLikeTheReference(hindleyMilnerSchedule, program))
  }

  /** The list of ones without end and the stream of the naturals from 1,
    * whose heads the program reads.
    */
  private val listsWithoutEnd: Vector[Term] = Vector(
    listFold(zero)(λ(head => λ(_ => head)))(fixpoint(λ(ones => cons(successor(zero))(ones)))),
    listFold(zero)(λ(head => λ(_ => head)))(fixpoint(λ(f => λ(n => cons(n)(f(successor(n))))))(successor(zero)))
  )

  // Infinite data the run demands, in programs HM types: the check of a
  // fallback point that meets the reading of its own operand again takes
  // the untyped path, and the lists without end are built one cell at a
  // time.
  test("infiniteDataDemanded") {
    (Vector(
      fixpoint(λ(y => successor(y)))(zero)(λ(_ => zero)),
      fixpoint(λ(y => successor(successor(y))))(zero)(λ(p => p(zero)(λ(_ => zero))))
    ) ++ listsWithoutEnd).zipWithIndex.foreach { (program, index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"program $index")
      assertEquals(run.decodings, 0L, s"program $index")
    }
  }

  // A list without end whose head the run reads is built one cell at a
  // time, under `fallback` and `strict` alike: cons's native and
  // successor's native called once each, and no check fails.
  test("aListWithoutEndIsBuiltOneCellAtATime") {
    for
      (program, index) <- listsWithoutEnd.zipWithIndex
      dispatch <- Vector(fallback, strict)
    do
      val run = compiledRun(dispatch, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"program $index under ${dispatch.name}")
      assertEquals(run.decodings, 0L, s"program $index under ${dispatch.name}")
      assertEquals(run.calls.get(consNative), Some(1L), s"program $index under ${dispatch.name}")
      assertEquals(run.calls.get(successorNative), Some(1L), s"program $index under ${dispatch.name}")
  }

  // Under the strategy `strict` these programs, which HM types, run as
  // under `fallback`: every check of a fallback point the run meets holds.
  test("strictRunsTheProgramsHindleyMilnerTypes") {
    (Vector(
      successor(successor(zero)),
      natFold(zero)(compose(successor)(successor))(successor(zero)),
      successor(natFold(zero)(compose(successor)(successor))(successor(zero))),
      successor(natFold(zero)(λ(x => successor(successor(x))))(successor(zero))),
      booleanNot(booleanNot(trueName)),
      cons(successor(zero))(cons(zero)(nil))
    ) ++ coveredPrograms).zipWithIndex.foreach { (program, index) =>
      val run = compiledRun(strict, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"program $index")
      assertEquals(run.decodings, 0L, s"program $index")
    }
  }

  // Programs HM types through a Maybe whose just is successor's term run
  // under `strict` and read the reference's normal forms: HM types them, so
  // they run (CONTRIBUTING.md, "Ordinary programs compile as a native typed compiler compiles them"),
  // and of the types their terms admit the program chooses the one the whole
  // program has (CONTRIBUTING.md, "Several types or encodings are options, never a cost"). Its purpose is to catch a typing that
  // picks the naturals for the Maybe and throws at the check of a fallback
  // point, which this test asked for until 2026-11-19.
  // FIXME (2026-11-19): under `strict` a program https://github.com/Atry/private-overlay/issues/2044
  // whose terms admit several native types is still rejected when the typing picks one the whole program
  // does not have. MEASURED on 2026-11-18: which of these programs run depends on the spelling of the
  // noinline marker `generic` alone (four spellings equal to the identity by the β rule, each a leaf the
  // e-graph cannot see into, flip them), so the typing is decided by a tie; that the tie is the extraction's
  // order among equal costs is inferred, not verified. MEASURED on 2026-11-21, with the marker's key
  // spelled "$generic": both Maybe programs throw
  // (program 1 typed_version_domains([big_integer])), and boolean_not (nat_fold zero successor
  // (successor zero)), below, runs; with "__generic" the Maybe of a list and that program threw. The tests
  // stay as the vision asks and are marked as expected failures, as the current spelling decides, until the
  // typing chooses the type the whole program has.
  maybePrograms.zipWithIndex.foreach { (program, index) =>
    val name = s"strictRunsTheProgramsHindleyMilnerTypesThroughAMaybe: program $index"
    test(munit.TestOptions(name).fail) {
      assertEquals(compiledRun(strict, hindleyMilnerSchedule, program).answers, referenceAnswers(program))
    }
  }

  test("fallbackRunsTheProgramsHindleyMilnerTypesThroughAMaybe") {
    maybePrograms.zipWithIndex.foreach { (program, index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assertEquals(run.answers, referenceAnswers(program), s"program $index")
      assertEquals(run.decodings, 0L, s"program $index")
    }
  }

  // Under `strict`, a run that meets a fallback point whose check does not
  // hold throws the domain error (the Prolog test's comment says which
  // filter each program meets).
  test("strictRejectsAValueOutsideATypedVersionDomain") {
    Vector(
      successor(cons(zero)(nil)),
      booleanNot(cons(trueName)(nil)),
      cons(successor(zero))(cons(falseName)(nil))
    ).foreach(program => intercept[TypedVersionDomain](compiledRun(strict, hindleyMilnerSchedule, program)))
  }

  // Programs HM rejects whose terms admit a native type read the reference's
  // normal forms under `strict` too (CONTRIBUTING.md, "Several types or encodings are options, never a cost": a
  // program HM rejects for having several feasible types is not rejected here): in
  // boolean_not (nat_fold zero successor (successor zero)) the conflict puts
  // boolean_type and nat_type in one class.
  // Their purpose is to catch a typing that rejects such a program.
  test("strictRunsAFoldOfTrueHindleyMilnerRejects") {
    val program = natFold(zero)(trueName)(successor(zero))
    assertEquals(compiledRun(strict, hindleyMilnerSchedule, program).answers, referenceAnswers(program))
  }

  // FIXME: runs only by the tie the Maybe programs above record; with the marker key "__generic" it threw https://github.com/Atry/private-overlay/issues/1945
  // typed_version_domains([boolean]).
  test("strictRunsTheNegationOfAFoldHindleyMilnerRejects") {
    val program = booleanNot(natFold(zero)(successor)(successor(zero)))
    assertEquals(compiledRun(strict, hindleyMilnerSchedule, program).answers, referenceAnswers(program))
  }

  /** The runs of a schedule and the codes the JIT compiled for the test
    * nat_fold zero (compose successor successor) applied to successor^size
    * zero, compiled under `fallback` and run from the suite
    * (`function_test_costs/4`). The suite after.
    */
  private def functionTestCosts(suite: Suite, size: Int): (Suite, Int, Int) =
    val (withInput, input) = programInput(suite, natFold(zero)(compose(successor)(successor))(numeral(size)))
    val (after, run) = dispatchedRun(withInput, fallback, hindleyMilnerSchedule, input)
    (after, run.typings, run.codesCompiled)

  // Plan principles 157 and 158 (jit_strategies.pl, THE TEST IS THE UNIT):
  // the tests f a, f b and f c of one f each run the schedule once, and only
  // the first compiles f's codes; a test met again runs no schedule.
  test("theTestsOfOneFunctionCompileItOnce") {
    val (afterFirst, firstTypings, firstCodes) = functionTestCosts(Suite.fresh, 2)
    val (afterSecond, secondTypings, secondCodes) = functionTestCosts(afterFirst, 3)
    val (afterThird, thirdTypings, thirdCodes) = functionTestCosts(afterSecond, 5)
    val (_, againTypings, againCodes) = functionTestCosts(afterThird, 3)
    println(s"codes compiled: $firstCodes, $secondCodes, $thirdCodes and $againCodes")
    assert(firstCodes > 0)
    assertEquals(Vector(firstTypings, secondTypings, thirdTypings, againTypings), Vector(1, 1, 1, 0))
    assertEquals(Vector(secondCodes, thirdCodes, againCodes), Vector(0, 0, 0))
  }

  // The run-time check of first-order data costs each element no more from
  // size 32 to 128 than from 8 to 32, on data HM types and on data it
  // rejects, after a run at size 4 has compiled the family's codes, and
  // each family's largest reaches its fixed point within the budget of each
  // round, 20,000 instances.
  test("theRunsCheckCostsAnElementDoNotGrow") {
    Vector("numerals", "lists", "list_ending_in_a_boolean", "successor_of_a_list").foreach { family =>
      val (suite, largest) = programInput(Suite.fresh, dataValue(family, 128))
      roundsReachTheirFixedPoints(costSchedule, largest)
      runCostsDoNotGrow(family, costSchedule, dataValue(family, _))
    }
  }

  // The run of a function the program defines by fixpoint costs each level
  // no more from 32 to 128 than from 8 to 32, after a run at 4 has compiled
  // its codes, reads the reference's normal form and decodes nothing.
  test("aRecursiveFunctionsRunCostsALevelDoNotGrow") {
    val (suite, largest) = programInput(Suite.fresh, recursiveCount(128))
    roundsReachTheirFixedPoints(costSchedule, largest)
    runCostsDoNotGrow("recursive count", costSchedule, recursiveCount)
    val run = compiledRun(fallback, costSchedule, recursiveCount(8))
    assertEquals(run.answers, referenceAnswers(recursiveCount(8)))
    assertEquals(run.decodings, 0L)
  }

  /** Purpose: catch the instance table changing the answers now that it
    * tables instances read inside a fallback point's check, readings that
    * cut a recurring operand included. Each program compiled under the
    * fallback dispatch reads the same normal forms with the instance table
    * as without it; the readings must cut some operand, or the law says
    * nothing about that case. The reading with the table is given twice the
    * steps: the table costs a constant factor more steps, not a higher order
    * (tablambda's algorithms, which set the time complexity).
    * MEASURED 2026-11-19 on beyondBothProgram at sizes 2, 4 and 8 under the
    * markers spelled as tags: 11,734, 53,934 and 1,199,470 steps without the
    * table, 19,547, 89,895 and 2,000,135 with it, 1.67 times each; at size 8
    * the reading with it ran out of the same 2,000,000 steps.
    */
  stoppableTest("theInstanceTableInsideFallbackChecksLeavesTheAnswers") { stopped =>
    val untabled = fallbackConfiguration
    val tabled =
      JitConfiguration(untabled.facts, untabled.budget, untabled.strategy, untabled.backend, untabled.dispatch, instanceTable = true)
    val programs = Vector(1, 4, 8).flatMap(size =>
      Vector(recursiveCount(size), closureChain(size), familyProgram("fold", size), familyProgram("doubles", size), numeral(size))
    ) ++ Vector(
      beyondHindleyMilnerProgram,
      beyondBothProgram(8),
      fixpoint(λ(y => successor(y)))(zero)(λ(_ => zero)),
      fixpoint(λ(y => successor(successor(y))))(zero)(λ(p => p(zero)(λ(_ => zero))))
    ) ++ listsWithoutEnd
    val cuts = programs.map { program =>
      val (_, input) = programInput(Suite.fresh, program)
      val Dispatched(refined, _, _) =
        StrategyDispatch.dispatched(CompilationStrategy(fallback, hindleyMilnerSchedule), input, facts, Suite.fresh.cache, StopSignal.completedWith(stopped))
      val withoutTable = normalFormsSpent(Mode.Jit(Jit(untabled)), refined, normalFormLimit)
      val withTable = normalFormsSpent(Mode.Jit(Jit(tabled)), refined, 2 * normalFormLimit)
      assertEquals(withTable.outcome, withoutTable.outcome, program.toString)
      withTable.jitState match
        case run: JitRunState => run.cuts
        case other            => fail(s"no JIT state after the reading: $other")
    }
    println(s"instance table inside checks: ${programs.size} programs, cuts ${cuts.mkString(", ")}")
    assert(cuts.exists(_ > 0), "no reading cut an operand")
  }

  // The run of a natural that a closure builds, (\y. successor^size y)
  // zero, costs each successor no more from 32 to 128 than from 8 to 32,
  // after a run at 4 has compiled its codes; the run at 8 calls
  // successor's native 8 times and decodes nothing.
  test("aClosuresNaturalsRunCostsASuccessorDoNotGrow") {
    runCostsDoNotGrow("closure chain", costSchedule, closureChain)
    val run = compiledRun(fallback, costSchedule, closureChain(8))
    assertEquals(run.answers, referenceAnswers(closureChain(8)))
    assertEquals(run.decodings, 0L)
    assertEquals(run.calls.get(successorNative), Some(8L))
  }

  /** The program of the family at the size: `fold`, the fold of successor
    * twice over successor^size zero; `doubles`, even of double^size
    * (successor zero) (`family_program/3`).
    */
  private def familyProgram(family: String, size: Int): Term = family match
    case "fold"    => natFold(zero)(compose(successor)(successor))(numeral(size))
    case "doubles" => even(doubles(size, successor(zero)))
    case other     => fail(s"no family $other")

  /** The instances of the two rounds of the program of the family at the
    * size, each reaching its fixed point (`compilation_instances/3`).
    */
  private def compilationInstances(family: String, size: Int): Int =
    val (suite, input) = programInput(Suite.fresh, familyProgram(family, size))
    val scheduled = Schedule.run(library.index, Vector(input), hindleyMilnerSchedule, StopSignal.NeverStopped)
    scheduled.records.map(_.report) match
      case Vector(FixpointReport(End.FixedPoint(typeCheck)), FixpointReport(End.FixedPoint(erasure))) =>
        typeCheck + erasure
      case reports => fail(s"the rounds reported $reports")

  /** From size 4 to 16 to 64, the instances each added element costs do
    * not grow (the Prolog test measured 500, 1,196 and 3,980 instances for
    * the fold, 58 a successor over each span, and 233, 521 and 1,673 for the
    * doubles, 24 a double).
    */
  private def instancesDoNotGrow(family: String): Unit =
    val small = compilationInstances(family, 4)
    val middle = compilationInstances(family, 16)
    val large = compilationInstances(family, 64)
    val before = (middle - small).toDouble / 12
    val after = (large - middle).toDouble / 48
    assert(after <= before, s"$family: $small, $middle and $large instances at 4, 16 and 64")

  test("theCompilationsInstancesASuccessorCostsDoNotGrow") {
    instancesDoNotGrow("fold")
  }

  test("theCompilationsInstancesADoubleCostsDoNotGrow") {
    instancesDoNotGrow("doubles")
  }

  // The natives double and even agree with their library terms on small
  // naturals, and the run calls them.
  test("theNativesAgreeWithTheirLibraryTerms") {
    Vector(
      double(numeral(3)) -> NativeName.Function("natural_double"),
      even(numeral(3)) -> NativeName.Function("natural_even"),
      even(double(successor(zero))) -> NativeName.Function("natural_even")
    ).foreach((program, native) =>
      assert(compiledLikeTheReference(hindleyMilnerSchedule, program).calls.contains(native), native.toString)
    )
  }

  // Beyond HM: the closure parameter g is used at nat -> nat and at
  // boolean -> boolean; the round with the beta rule reduces each
  // application of the identity closure, and the type check reads the
  // reduct. The run calls natives of the naturals and of the booleans.
  test("beyondHindleyMilner") {
    val run = compiledLikeTheReference(beyondSchedule, beyondHindleyMilnerProgram)
    assert(run.calls.contains(successorNative), s"${run.calls}")
    assert(run.calls.contains(trueNative) || run.calls.contains(falseNative), s"${run.calls}")
  }

  // Beyond weak head reduction: whether double^n (successor zero) is even,
  // and its successor, by the natives double and even. At n = 8 the
  // reference agrees; at n = 64 it reads neither answer, the compiled run
  // calls natural_double 64 times and natural_even once.
  test("beyondWeakHead") {
    val small = doubles(8, successor(zero))
    compiledLikeTheReference(hindleyMilnerSchedule, even(small))
    compiledLikeTheReference(hindleyMilnerSchedule, even(successor(small)))
    val power = doubles(64, successor(zero))
    val run = compiledBeyondTheReference(hindleyMilnerSchedule, even(power), trueName)
    assertEquals(run.calls.get(NativeName.Function("natural_double")), Some(64L))
    assertEquals(run.calls.get(NativeName.Function("natural_even")), Some(1L))
    compiledBeyondTheReference(hindleyMilnerSchedule, even(successor(power)), falseName)
  }

  // Beyond both: the closure parameter of the program beyond HM used around
  // the parity of double^n (successor zero), compiled by the beta round and
  // the type check of the reduct; at n = 8 the reference agrees, at n = 64
  // it reads no answer.
  test("beyondHindleyMilnerAndWeakHead") {
    compiledLikeTheReference(beyondSchedule, beyondBothProgram(8))
    val run = compiledBeyondTheReference(beyondSchedule, beyondBothProgram(64), falseName)
    assertEquals(run.calls.get(NativeName.Function("natural_double")), Some(64L))
    assertEquals(run.calls.get(NativeName.Function("natural_even")), Some(1L))
  }
