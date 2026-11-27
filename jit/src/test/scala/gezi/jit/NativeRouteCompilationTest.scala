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
import gezi.ir.Value
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
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.TermConstruction
import gezi.strategies.BaselineModules
import gezi.strategies.CountedExtractor
import gezi.strategies.RoundModules
import gezi.strategies.StandardIndexer
import gezi.strategies.StandardSaturator
import gezi.standardlibrary.StandardLibraryIndex
import gezi.frontend.ReadableText
import gezi.standardlibrary.SplitMix
import gezi.weakhead.EvaluatorTesting
import snapshot4s.generated.snapshotConfig

/** The port of `gezi/tests/native_route_compilation.plt`, whose file comment
  * this follows: a program over the library terms of
  * `JitTesting.libraryTermsFile`, each a member read by projection, goes
  * through the front end, its occurrences tagged, and a schedule of
  * `gezi.strategies.NativeRouteCompilation` (the type check, which puts the
  * typed version beside each application of HM's rule, then the erasure of the
  * tags, or, for a program beyond HM, a round with the beta rule on the
  * program's closures before them); the framework's entry
  * (`StrategyDispatch.dispatched`) runs the schedule and refines its output,
  * and the JIT reads the refined term under the strategy's mode, the strategy
  * `fallback` unless a test says otherwise. The library is the Prolog test's,
  * compiled with the Prolog backend's checks (naturals as big integers,
  * booleans as truth values, double and even as natives). Each program's normal
  * forms under the JIT are the reference's reading of the program as written,
  * and the run decodes nothing.
  *
  * Departures from the Prolog:
  *
  *   - The programs are written in the HOAS, their library terms closed
  *     instructions (`JitTesting.libraryTerm`), so no name is resolved; the
  *     knowledge of a round is a round of the rounds fixture
  *     (`StrategyTesting.round`).
  *   - A reading is bounded by `NativesTesting.normalFormLimit`, 2,000,000
  *     evaluator steps, where the Prolog test read within 10,000,000
  *     inferences.
  *   - The Prolog process kept one store, one strategy cache and one JIT cache
  *     for the whole file; here a run starts from an empty dispatch cache and
  *     no JIT state (`Suite.fresh`), except where a test threads them from one
  *     run to the next, as the tests of costs and of one function's tests do.
  *     No assertion of the Prolog test reads what an earlier test compiled.
  *   - The tests of costs (`the_runs_check_costs_an_element_do_not_grow`,
  *     `a_recursive_functions_run_costs_a_level_do_not_grow` and
  *     `a_closures_naturals_run_costs_a_successor_do_not_grow`) count the
  *     reading's evaluator steps, a deterministic count, where the Prolog
  *     counted SWI-Prolog's inferences of the same reading; as there, the
  *     compilation is not counted.
  *
  * The strategy `strict` is declared here as an entry would declare one
  * (jit.pl, DISPATCH STRATEGIES; a backend may drop the input that is not
  * specialized and report an error): at a fallback point whose check does not
  * hold it rejects the operand. The baseline offers no rejecting strategy
  * (`gezi.strategies.DispatchStrategies`).
  */
class NativeRouteCompilationTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of NativeRouteCompilationTest, "theRunsCheckCostsAnElementDoNotGrow", takes 56.781 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(90, "s")

  /** The library, its facts, the type check's round, the three schedules and
    * the two configurations, forced before the first test and not charged to it
    * (FailFastSuite).
    */
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
    LibraryFiles.compiled(
      "tests/library_fixtures/native_route_with_prolog_backend.lambdalattice",
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  /** A program of the library's configuration, written in the HOAS. */
  private type Program = TermOf[Configured[encoding.type]]

  private lazy val index: StandardLibraryIndex[encoding.type] =
    encoding.operations.index

  /** The knowledge of the type check, the rounds fixture's
    * `prolog_backend_type_check`: the HM lemmas in the zero universe, with the
    * schemes of native_types' names, the schemes of native_arithmetic's, and
    * the Prolog backend's shapes, whose candidacies write the typed versions.
    */
  private lazy val typeCheckKnowledge: Configured[NoFacts.type] =
    StrategyTesting.round("prolog_backend_type_check")

  /** The budget of each round is 6,000 instances, the Prolog test's: measured
    * there 2026-10-29, the largest round, the type check of the fold of
    * successor twice over successor^64 zero, reaches its fixed point at 3,910,
    * linear in the program; the type check of even (double^64 (successor zero))
    * at 1,606.
    */
  private lazy val hindleyMilnerSchedule: Vector[Round[encoding.type]] =
    nativeRouteSchedule(6000)

  /** The round modules of the library's configuration: the baseline's
    * saturator, extractor, lemma encoding, indexer, backend and orientation
    * compiler, the rounds writing back as written.
    */
  private lazy val modules: RoundModules[encoding.type] =
    RoundModules[encoding.type](
      StandardSaturator[encoding.type](_),
      CountedExtractor[encoding.type](
        NativeRouteCompilation.extraction,
        BaselineModules.table[encoding.type]
      ),
      BaselineRounds.modules.lemmaEncoding,
      StandardIndexer.of[encoding.type],
      BaselineRounds.modules.backend,
      BaselineRounds.modules.orientationCompiler,
      TermConstruction(encoding)
    )

  /** The type check of the knowledge and the erasure of the occurrence tags,
    * each round within the budget.
    */
  private def nativeRouteSchedule(budget: Int): Vector[Round[encoding.type]] =
    NativeRouteCompilation.nativeRouteSchedule[encoding.type](
      index,
      BaselineRounds.lemmas(library, typeCheckKnowledge),
      BaselineRounds
        .lemmas(library, StrategyTesting.round("occurrence_erasure")),
      budget,
      modules
    )

  private lazy val beyondSchedule: Vector[Round[encoding.type]] =
    NativeRouteCompilation.beyondHindleyMilnerSchedule[encoding.type](
      index,
      BaselineRounds
        .lemmas(library, StrategyTesting.round("closure_application")),
      BaselineRounds.lemmas(library, typeCheckKnowledge),
      BaselineRounds
        .lemmas(library, StrategyTesting.round("occurrence_erasure")),
      6000,
      modules
    )

  /** The schedule of the tests of costs, each round within 21,000 instances:
    * measured 2026-11-22 on the branch of the refutation lemmas, the type check
    * reaches its fixed point at 5,553 instances on the numeral of 128 (1,425 at
    * 32), 15,153 on the list of 128 (3,825), 20,319 on the same list ending in
    * `cons false nil` (5,199) and 8,037 on `successor` applied to the list of
    * 128 zeros (2,085): linear in the size, about 158 instances an element on
    * the largest, the refutation and repulsion lemmas' constant factor over the
    * 18,426 the Prolog test measured there on 2026-10-30.
    */
  private lazy val costSchedule: Vector[Round[encoding.type]] =
    nativeRouteSchedule(21000)

  private val fallback: DispatchStrategy = DispatchStrategies.fallback

  private val strict: DispatchStrategy =
    DispatchStrategy("strict", DispatchDecision.Rejected)

  /** One configuration of the JIT for each dispatch strategy, built once: a JIT
    * state is read under the configuration it was built under.
    */
  private lazy val fallbackConfiguration = configurationOf(fallback)

  private lazy val strictConfiguration = configurationOf(strict)

  private def configurationOf(
      dispatch: DispatchStrategy
  ): JitConfiguration[encoding.type] =
    JitConfiguration[encoding.type](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.Dispatch(dispatch),
      instanceTable = false,
      storageAccess = gezi.ir.StorageAccess.granted()
    )

  private def configuration(
      dispatch: DispatchStrategy
  ): JitConfiguration[encoding.type] =
    if dispatch == strict then strictConfiguration else fallbackConfiguration

  // ---- the library terms, members of JitTesting.libraryTermsFile ----

  private val zero = JitTesting.libraryTerm[encoding.type]("zero")
  private val successor = JitTesting.libraryTerm[encoding.type]("successor")
  private val nil = JitTesting.libraryTerm[encoding.type]("nil")
  private val cons = JitTesting.libraryTerm[encoding.type]("cons")
  private val falseName = JitTesting.libraryTerm[encoding.type]("false")
  private val trueName = JitTesting.libraryTerm[encoding.type]("true")
  private val konstant = JitTesting.libraryTerm[encoding.type]("konstant")
  private val compose = JitTesting.libraryTerm[encoding.type]("compose")
  private val natFold = JitTesting.libraryTerm[encoding.type]("nat_fold")
  private val listFold = JitTesting.libraryTerm[encoding.type]("list_fold")
  private val booleanNot = JitTesting.libraryTerm[encoding.type]("boolean_not")
  private val fixpoint = JitTesting.libraryTerm[encoding.type]("fixpoint")
  private val double = JitTesting.libraryTerm[encoding.type]("double")
  private val even = JitTesting.libraryTerm[encoding.type]("even")
  private val natType = JitTesting.libraryTerm[encoding.type]("nat_type")

  // ---- the runs ----

  /** What the runs of a test share, threaded from one run to the next as the
    * Prolog process kept them: the cache service, which the runs read and write
    * in place, and the JIT state.
    */
  private final case class Suite(
      cache: Cache,
      jitState: JitState[encoding.type]
  )

  private object Suite:
    def fresh: Suite = Suite(BaselineCaches.provider(), NoJitState)

  /** What a run of a compiled program read: its normal forms, sorted by text;
    * the decodings, the calls of each native called and the steps of the
    * reading; the codes the reading compiled and the runs of a schedule the
    * dispatch took; the representations of the storages the refined term holds,
    * values the specialized spelling computed in their representation when the
    * term was built.
    */
  private final case class Run(
      answers: Vector[Configured[encoding.type]],
      decodings: Long,
      calls: Map[NativeName, Long],
      steps: Long,
      codesCompiled: Int,
      typings: Int,
      stored: Set[Representation[JitValue[encoding.type]]]
  )

  /** The representations of the storages the term holds, its DAG walked once, a
    * storage a leaf.
    */
  private def storedRepresentations(
      term: Configured[encoding.type]
  ): Set[Representation[JitValue[encoding.type]]] =
    @scala.annotation.tailrec
    def walked(
        pending: List[Configured[encoding.type]],
        seen: Set[Configured[encoding.type]],
        found: Set[Representation[JitValue[encoding.type]]]
    ): Set[Representation[JitValue[encoding.type]]] = pending match
      case Nil                                 => found
      case head :: rest if seen.contains(head) => walked(rest, seen, found)
      case head :: rest if gezi.ir.NativeStorage.stored(head.representation) =>
        val representation = StorageOf
          .typed[encoding.type](head.representation)
          .map(_.representation)
          .toSet
        walked(rest, seen + head, found ++ representation)
      case head :: rest =>
        val children = if head.opaque then Nil
        else
          head.layer match
            case gezi.ir.Apply(function, argument) => List(function, argument)
            case gezi.ir.Parallel(left, right)     => List(left, right)
            case gezi.ir.Choice(left, right)       => List(left, right)
            case gezi.ir.Thunk(_, _, fillings)     => fillings.toList
            case _                                 => Nil
        walked(children ++ rest, seen + head, found)
    walked(List(term), Set.empty, Set.empty)

  /** The tagged program interned (`program_instruction/3`, its tagged part),
    * with the suite unchanged.
    */
  private def programInput(
      suite: Suite,
      program: Program
  ): (Suite, Configured[encoding.type]) =
    (suite, StrategyTesting.programInputIn[encoding.type](library, program))

  /** Each round of the schedule on the input reaches its fixed point, read from
    * a run of the schedule of its own, since the dispatch keeps no report.
    */
  private def roundsReachTheirFixedPoints(
      schedule: Vector[Round[encoding.type]],
      input: Configured[encoding.type]
  ): Unit =
    Schedule
      .run(index, Vector(input), schedule, StopSignal.NeverStopped)
      .records
      .foreach(record =>
        record.report match
          case FixpointReport(End.FixedPoint(_)) => ()
          case other => fail(s"a round of the schedule ended $other")
      )

  /** The tagged input compiled under the strategy of the dispatch strategy and
    * the schedule and read under its mode, from the suite (`dispatched_run/3`):
    * the run finishes. The suite after.
    */
  private def dispatchedRun(
      suite: Suite,
      dispatch: DispatchStrategy,
      schedule: Vector[Round[encoding.type]],
      input: Configured[encoding.type]
  ): (Suite, Run) =
    val dispatched =
      StrategyDispatch.dispatched[encoding.type](
        CompilationStrategy[encoding.type](dispatch, schedule),
        input,
        encoding,
        suite.cache,
        StopSignal.NeverStopped
      )
    val (refined, scheduleRan) = (dispatched.refined, dispatched.scheduleRan)
    val read = normalFormsSpent(
      Jit(configuration(dispatch)),
      Value.of(refined),
      normalFormLimit,
      suite.jitState
    )
    val answers = read.outcome match
      case Bounded.Finished(found) => found
      case other => fail(s"the compiled run did not finish: $other")
    val before = counts(suite.jitState)
    val after = counts(read.jitState)
    val calls = after.callsByNative.collect {
      case (native, count) if count > before.callsOf(native) =>
        native -> (count - before.callsOf(native))
    }
    val run = Run(
      answers,
      after.decodings - before.decodings,
      calls,
      read.steps,
      compiledCodes(read.jitState).size - compiledCodes(suite.jitState).size,
      if scheduleRan then 1 else 0,
      storedRepresentations(refined)
    )
    (Suite(suite.cache, read.jitState), run)

  /** The program compiled under the strategy of the dispatch strategy and the
    * schedule, each round reaching its fixed point, and run under its mode
    * (`compiled_run/6`).
    */
  private def compiledRun(
      dispatch: DispatchStrategy,
      schedule: Vector[Round[encoding.type]],
      program: Program
  ): Run =
    val (suite, input) = programInput(Suite.fresh, program)
    roundsReachTheirFixedPoints(schedule, input)
    dispatchedRun(suite, dispatch, schedule, input)._2

  /** The outcome of the program as written, neither tagged nor typed, read
    * under the mode within the reading's limit (`as_written_outcome/4`).
    */
  private def asWrittenOutcome(
      mode: Mode,
      program: Program
  ): Bounded[Vector[Configured[encoding.type]]] =
    normalFormsSpent(
      mode,
      JitTesting.plainConfiguration(encoding),
      JitTesting.termValue(program),
      normalFormLimit
    ).outcome

  /** The normal forms of the program as written under the reference's reading,
    * tabling(weak_head) (`reference_answers/2`).
    */
  private def referenceAnswers(
      program: Program
  ): Vector[Configured[encoding.type]] =
    asWrittenOutcome(Mode.TablingWeakHead, program) match
      case Bounded.Finished(found) => found
      case other => fail(s"the reference did not finish: $other")

  /** The program's compiled run reads the reference's normal forms of the
    * program as written, decodes nothing and computes in a representation: it
    * calls at least one native, or its refined term holds a storage the
    * specialized spelling made when the term was built, a constructor's native
    * called there (`compiled_like_the_reference/3`).
    */
  private def compiledLikeTheReference(
      schedule: Vector[Round[encoding.type]],
      program: Program
  ): Run =
    val run = compiledRun(fallback, schedule, program)
    assert(JitTesting.sameTerms(run.answers, referenceAnswers(program)))
    assertEquals(run.decodings, 0L)
    assert(
      run.calls.nonEmpty || run.stored.nonEmpty,
      "the run called no native and its refined term holds no storage"
    )
    run

  /** The program's compiled run reads the reference's normal forms of the
    * expected program and decodes nothing, while the reference reads no answer
    * of the program as written within its count under tabling(weak_head)
    * (`compiled_beyond_the_reference/4`).
    */
  private def compiledBeyondTheReference(
      schedule: Vector[Round[encoding.type]],
      program: Program,
      expected: Program
  ): Run =
    val run = compiledRun(fallback, schedule, program)
    assert(JitTesting.sameTerms(run.answers, referenceAnswers(expected)))
    assertEquals(run.decodings, 0L)
    assert(
      !asWrittenOutcome(Mode.TablingWeakHead, program).finished,
      "the reference read the program under tabling"
    )
    run

  /** The steps of the JIT's reading of the program compiled under `fallback`
    * and the schedule, interned into the suite and run from it
    * (`run_inferences/3`, counting steps). The suite after.
    */
  private def runSteps(
      suite: Suite,
      schedule: Vector[Round[encoding.type]],
      program: Program
  ): (Suite, Long) =
    val (withInput, input) = programInput(suite, program)
    val (after, run) = dispatchedRun(withInput, fallback, schedule, input)
    (after, run.steps)

  /** The steps of the runs at the sizes 8, 32 and 128 cost each element no more
    * from 32 to 128 than from 8 to 32, after a run at 4 (the Prolog tests'
    * `Before is (Middle - Small) / 24, After is (Large - Middle) / 96, After =<
    * Before`).
    */
  private def runCostsDoNotGrow(
      label: String,
      schedule: Vector[Round[encoding.type]],
      program: Int => Program
  ): Unit =
    val (warm, _) = runSteps(Suite.fresh, schedule, program(4))
    val (afterSmall, small) = runSteps(warm, schedule, program(8))
    val (afterMiddle, middle) = runSteps(afterSmall, schedule, program(32))
    val (_, large) = runSteps(afterMiddle, schedule, program(128))
    val before = (middle - small).toDouble / 24
    val after = (large - middle).toDouble / 96
    println(s"$label: $small, $middle and $large steps at 8, 32 and 128")
    assert(
      after <= before,
      s"$label: $small, $middle and $large steps at 8, 32 and 128"
    )

  // ---- the programs ----

  private def numeral(size: Int): Program =
    (1 to size).foldLeft(zero)((value, _) => successor(value))

  /** double applied the count times to the base. */
  private def doubles(count: Int, base: Program): Program =
    (1 to count).foldLeft(base)((value, _) => double(value))

  /** The size copies of the element consed onto the tail. */
  private def listEnding(size: Int, element: Program, tail: Program): Program =
    (1 to size).foldLeft(tail)((list, _) => cons(element)(list))

  /** First-order data of the family at the size (`data_value/3`):
    * successor^size zero; the list of size copies of `successor zero`; the same
    * list ending in `cons false nil`, which HM rejects; and `successor` applied
    * to the list of size zeros, which HM rejects.
    */
  private def dataValue(family: String, size: Int): Program = family match
    case "numerals"                 => numeral(size)
    case "lists"                    => listEnding(size, successor(zero), nil)
    case "list_ending_in_a_boolean" =>
      listEnding(size, successor(zero), cons(falseName)(nil))
    case "successor_of_a_list" => successor(listEnding(size, zero, nil))
    case other                 => fail(s"no family $other")

  /** A function the program defines by fixpoint, the count of the successors of
    * its argument, applied to successor^size zero (`recursive_count/2`).
    */
  private def recursiveCount(size: Int): Program =
    fixpoint(λ(self => λ(t => t(zero)(λ(u => successor(self(u)))))))(
      numeral(size)
    )

  /** The closure \y. successor^size y applied to zero (`closure_chain/2`). */
  private def closureChain(size: Int): Program =
    λ(variable => (1 to size).foldLeft(variable)((body, _) => successor(body)))(
      zero
    )

  /** The program beyond HM: a closure parameter used at nat -> nat and at
    * boolean -> boolean, its argument the identity closure.
    */
  private val beyondHindleyMilnerProgram: Program =
    λ(g => natFold(g(falseName))(booleanNot)(g(successor(zero))))(λ(x => x))

  /** The same use of a closure parameter, around the parity of double^size
    * (successor zero).
    */
  private def beyondBothProgram(size: Int): Program =
    λ(g => booleanNot(g(even(g(doubles(size, successor(zero)))))))(λ(x => x))

  /** A pair of the two values, written as the program's own closure. */
  private def pair(first: Program, second: Program): Program =
    λ(x => λ(y => λ(q => q(x)(y))))(first)(second)

  private val rejectedPrograms: Vector[Program] = Vector(
    cons(successor(zero))(cons(falseName)(nil)),
    successor(cons(zero)(nil)),
    booleanNot(cons(trueName)(nil)),
    booleanNot(natFold(zero)(successor)(successor(zero))),
    natFold(zero)(trueName)(successor(zero))
  )

  /** Programs of the coverage table of tests/native_route.plt (deleted with the
    * old e-graph) with lists, closures and polymorphic names used at two types
    * (`covered_program/1`).
    */
  private val coveredPrograms: Vector[Program] = Vector(
    listFold(zero)(konstant(successor))(cons(zero)(nil)),
    cons(cons(successor(zero))(nil))(cons(nil)(nil)),
    λ(f => λ(a => f(f(a))))(successor)(zero),
    λ(outer => λ(inner => λ(a => outer(inner(a)))))(successor)(successor)(zero),
    listFold(nil)(
      λ(head => λ(accumulated => cons(successor(head))(accumulated)))
    )(cons(zero)(nil)),
    λ(x => x)(successor)(λ(y => y)(zero)),
    cons(konstant(successor(zero))(successor(zero)))(
      cons(konstant(successor(zero))(successor))(nil)
    ),
    natFold(zero)(successor)(successor(successor(zero)))
  )

  /** Programs nominal HM types through a Maybe: a Maybe of a list and a Maybe
    * of a boolean, whose just is successor's term
    * (`strict_rejected_typed_program/1` of the Prolog tests, which a rejecting
    * strategy threw on).
    */
  private val maybePrograms: Vector[Program] = Vector(
    successor(cons(zero)(nil))(nil)(λ(items => cons(zero)(items))),
    successor(falseName)(trueName)(booleanNot)
  )

  // ---- the tests ----

  test("numerals") {
    Vector(1, 2, 8).foreach(size =>
      compiledLikeTheReference(hindleyMilnerSchedule, numeral(size))
    )
  }

  // The fold of successor twice over n is 2n, and the run builds every
  // successor in the representation: successor's native is called for the
  // literal's size and the steps' 2 size.
  test("theFoldOfAComposition") {
    Vector(1, 4, 16).foreach { size =>
      val program = natFold(zero)(compose(successor)(successor))(numeral(size))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"size $size"
      )
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(
        run.calls.get(successorNative),
        Some(3L * size),
        s"size $size"
      )
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(numeral(2 * size))),
        s"size $size"
      )
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
      step <- Vector(
        compose(successor)(successor),
        λ(x => successor(successor(x)))
      )
    do
      val program = successor(natFold(zero)(step)(numeral(size)))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"size $size"
      )
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(
        run.calls.get(successorNative),
        Some(3L * size),
        s"size $size"
      )
  }

  // A fold whose step is double, a library term the backend binds to the native
  // natural_double: the run calls natural_double once a step, decodes
  // nothing and reads the reference's normal forms.
  test("aFoldWhoseStepIsDouble") {
    Vector(2, 4, 8).foreach { size =>
      val program = even(natFold(successor(zero))(double)(numeral(size)))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"size $size"
      )
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(
        run.calls.get(NativeName.Function("natural_double")),
        Some(size.toLong),
        s"size $size"
      )
    }
  }

  test("booleans") {
    Vector(
      booleanNot(trueName),
      booleanNot(booleanNot(trueName)),
      booleanNot(booleanNot(booleanNot(falseName)))
    ).foreach(program =>
      compiledLikeTheReference(hindleyMilnerSchedule, program)
    )
  }

  test("programsWithListsAndClosures") {
    coveredPrograms.foreach(program =>
      compiledLikeTheReference(hindleyMilnerSchedule, program)
    )
  }

  // A list HM types runs in the representation of the lists of naturals:
  // the typed constructors build every cell with cons's native, list_fold takes
  // the list apart in the representation, and the run decodes nothing.
  // KNOWN FAILURE until step 8 of the native data structures (https://github.com/Atry/private-overlay/issues/2176): a
  // list whose cells the run builds one by one has, at each cell, a tail that is a fallback point not yet a storage, which
  // `Jit.tailOutcome` reads untyped (its FIXME), so cons's native makes no such cell and the strict dispatch throws
  // `TypedVersionDomain`; this test passed under the construction as written, deleted with the specialized spelling.
  test("aListRunsInItsRepresentation".fail) {
    Vector(4, 8).foreach { size =>
      val program = listFold(zero)(λ(_ => λ(length => successor(length))))(
        dataValue("lists", size)
      )
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"size $size"
      )
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(consNative), Some(size.toLong), s"size $size")
      assertEquals(run.calls.get(nilNative), Some(1L), s"size $size")
    }
  }

  // A fold whose step has two parameters builds every cell of its result in
  // the representation of the lists of naturals: cons's native 2n times over n
  // zeros, n for the input and n for the result.
  // KNOWN FAILURE until step 8 of the native data structures (https://github.com/Atry/private-overlay/issues/2176): a
  // list whose cells the run builds one by one has, at each cell, a tail that is a fallback point not yet a storage, which
  // `Jit.tailOutcome` reads untyped (its FIXME), so cons's native makes no such cell and the strict dispatch throws
  // `TypedVersionDomain`; this test passed under the construction as written, deleted with the specialized spelling.
  test("aFoldWithAStepOfTwoParametersBuildsItsCellsNatively".fail) {
    Vector(4, 8).foreach { size =>
      val program = listFold(nil)(
        λ(head => λ(tail => cons(successor(head))(tail)))
      )(listEnding(size, zero, nil))
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"size $size"
      )
      assertEquals(run.decodings, 0L, s"size $size")
      assertEquals(run.calls.get(consNative), Some(2L * size), s"size $size")
    }
  }

  // Every cell of these lists HM types is built by cons's native (the Prolog
  // test's comment says why each cell is a candidate).
  // KNOWN FAILURE until step 8 of the native data structures (https://github.com/Atry/private-overlay/issues/2176): a
  // list whose cells the run builds one by one has, at each cell, a tail that is a fallback point not yet a storage, which
  // `Jit.tailOutcome` reads untyped (its FIXME), so cons's native makes no such cell and the strict dispatch throws
  // `TypedVersionDomain`; this test passed under the construction as written, deleted with the specialized spelling.
  test("theCellsOfListsHindleyMilnerTypesAreBuiltNatively".fail) {
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
      listFold(nil)(
        λ(items =>
          λ(lengths =>
            cons(listFold(zero)(λ(_ => λ(length => successor(length))))(items))(
              lengths
            )
          )
        )
      )(
        cons(cons(one)(nil))(cons(cons(zero)(cons(zero)(nil)))(nil))
      ) -> 7L
    ).zipWithIndex.foreach { case ((program, cells), index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"program $index"
      )
      assertEquals(run.decodings, 0L, s"program $index")
      assertEquals(run.calls.get(consNative), Some(cells), s"program $index")
    }
  }

  // Programs HM rejects, compiled by the schedule of the programs HM types:
  // the refinement's fallback points keep the untyped versions beside the
  // typed ones, and the run reads the reference's normal forms.
  test("programsHindleyMilnerRejects") {
    rejectedPrograms.zipWithIndex.foreach((program, index) =>
      assert(
        JitTesting.sameTerms(
          compiledRun(fallback, hindleyMilnerSchedule, program).answers,
          referenceAnswers(program)
        ),
        s"program $index"
      )
    )
  }

  // Programs HM types over data of their own: each reads the reference's
  // normal forms, decodes nothing and computes its fields in the
  // representation, by the native named.
  test("programsOverTheirOwnDataComputeTheirFieldsNatively") {
    Vector(
      λ(p => p(λ(a => λ(_ => a))))(
        pair(successor(zero), zero)
      ) -> successorNative,
      λ(p => p(λ(a => λ(b => natFold(a)(successor)(b)))))(
        pair(successor(zero), successor(successor(zero)))
      ) -> successorNative,
      successor(successor(zero))(zero)(λ(v => successor(v))) -> successorNative,
      λ(x => λ(l => λ(_ => l(x))))(successor(zero))(λ(v => successor(v)))(
        λ(_ => zero)
      ) -> successorNative,
      λ(a => λ(x => λ(b => λ(_ => λ(n => n(a)(x)(b))))))(
        λ(leaf => λ(_ => leaf))
      )(successor(zero))(λ(leaf => λ(_ => leaf)))(zero)(
        λ(_ => λ(v => λ(_ => successor(v))))
      ) -> successorNative
    ).foreach((program, native) =>
      assert(
        compiledLikeTheReference(hindleyMilnerSchedule, program).calls
          .contains(native),
        native.toString
      )
    )
  }

  // KNOWN FAILURE until step 8 (https://github.com/Atry/private-overlay/issues/2176): a list built cell by cell has at
  // each cell a tail that is a fallback point not yet a storage, which `Jit.tailOutcome` reads untyped (its FIXME), so
  // cons's native makes no such cell, and the strict dispatch throws `TypedVersionDomain`.
  test(
    "programsOverTheirOwnDataComputeTheirFieldsNatively: a list in a pair".fail
  ) {
    val program =
      λ(p => p(λ(a => λ(_ => a))))(pair(cons(successor(zero))(nil), nil))
    assert(
      compiledLikeTheReference(hindleyMilnerSchedule, program).calls
        .contains(consNative),
      consNative.toString
    )
  }

  // Programs HM types that compute inside a closure's body: the contracts
  // at the closure's boundary and the checks of the fallback points in the
  // body reach the natives named.
  test("programsComputingInAClosuresBodyRunNatively") {
    Vector(
      λ(f => f(successor(zero)))(
        λ(x => natFold(x)(successor)(successor(successor(zero))))
      ) -> successorNative,
      λ(g => g(g(zero)))(λ(x => successor(successor(x)))) -> successorNative,
      λ(f => f(cons(successor(zero))(cons(zero)(nil))))(
        λ(items => listFold(zero)(λ(_ => λ(n => successor(n))))(items))
      ) ->
        successorNative
    ).foreach((program, native) =>
      assert(
        compiledLikeTheReference(hindleyMilnerSchedule, program).calls
          .contains(native),
        native.toString
      )
    )
    // not's typed closure holds false and true as the storages the specialized spelling makes at construction, their
    // constructors' natives called there, so the run computes in the booleans' representation with no call of its own.
    val negated = compiledLikeTheReference(
      hindleyMilnerSchedule,
      λ(f => f(f(trueName)))(λ(b => booleanNot(b)))
    )
    assert(negated.stored.contains(Representation.Truth), s"${negated.stored}")
  }

  // KNOWN FAILURE until step 8 (https://github.com/Atry/private-overlay/issues/2176): a list built cell by cell has at
  // each cell a tail that is a fallback point not yet a storage, which `Jit.tailOutcome` reads untyped (its FIXME), so
  // cons's native makes no such cell, and the strict dispatch throws `TypedVersionDomain`.
  test(
    "programsComputingInAClosuresBodyRunNatively: a cell the closure's body builds".fail
  ) {
    val program = λ(f => cons(f(zero))(nil))(λ(x => successor(x)))
    assert(
      compiledLikeTheReference(hindleyMilnerSchedule, program).calls
        .contains(consNative),
      consNative.toString
    )
  }

  // A value beside infinite data it never demands: the fallback points of
  // the typed versions are read only where the run demands them.
  test("infiniteDataNeverDemanded") {
    Vector(
      konstant(successor(zero))(fixpoint(λ(y => successor(y)))),
      konstant(successor(zero))(fixpoint(λ(zeros => cons(zero)(zeros))))
    ).foreach(program =>
      compiledLikeTheReference(hindleyMilnerSchedule, program)
    )
  }

  /** The list of ones without end and the stream of the naturals from 1, whose
    * heads the program reads.
    */
  private val listsWithoutEnd: Vector[Program] = Vector(
    listFold(zero)(λ(head => λ(_ => head)))(
      fixpoint(λ(ones => cons(successor(zero))(ones)))
    ),
    listFold(zero)(λ(head => λ(_ => head)))(
      fixpoint(λ(f => λ(n => cons(n)(f(successor(n))))))(successor(zero))
    )
  )

  // Infinite data the run demands, in programs HM types: the check of a
  // fallback point that meets the reading of its own operand again takes
  // the untyped path, and the lists without end are built one cell at a
  // time.
  test("infiniteDataDemanded") {
    (Vector(
      fixpoint(λ(y => successor(y)))(zero)(λ(_ => zero)),
      fixpoint(λ(y => successor(successor(y))))(zero)(
        λ(p => p(zero)(λ(_ => zero)))
      )
    ) ++ listsWithoutEnd).zipWithIndex.foreach { (program, index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"program $index"
      )
      assertEquals(run.decodings, 0L, s"program $index")
    }
  }

  // A list without end whose head the run reads is built one cell at a
  // time, under `fallback` and `strict` alike: cons's native and
  // successor's native called once each, and no check fails.
  // KNOWN FAILURE until step 8 of the native data structures (https://github.com/Atry/private-overlay/issues/2176): a
  // list whose cells the run builds one by one has, at each cell, a tail that is a fallback point not yet a storage, which
  // `Jit.tailOutcome` reads untyped (its FIXME), so cons's native makes no such cell and the strict dispatch throws
  // `TypedVersionDomain`; this test passed under the construction as written, deleted with the specialized spelling.
  test("aListWithoutEndIsBuiltOneCellAtATime".fail) {
    for
      (program, index) <- listsWithoutEnd.zipWithIndex
      dispatch <- Vector(fallback, strict)
    do
      val run = compiledRun(dispatch, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"program $index under ${dispatch.name}"
      )
      assertEquals(run.decodings, 0L, s"program $index under ${dispatch.name}")
      assertEquals(
        run.calls.get(consNative),
        Some(1L),
        s"program $index under ${dispatch.name}"
      )
      assertEquals(
        run.calls.get(successorNative),
        Some(1L),
        s"program $index under ${dispatch.name}"
      )
  }

  // A list whose items are lists without end, its own tail a literal or the
  // rest still to be computed, read to the head of its head: HM types it,
  // and under `strict` as under `fallback` the run reads the reference's
  // answer and throws no TypedVersionDomain. Derived before the run: no
  // decoding, since under the default construction every cell, inner and
  // outer, is built by cons's native from its item and its tail as given
  // (`tailOutcome`), and each fallback point's check reads that storage as a
  // value of the list's representation, with no decode point to read.
  // KNOWN FAILURE until step 8 of the native data structures (https://github.com/Atry/private-overlay/issues/2176): a
  // list whose cells the run builds one by one has, at each cell, a tail that is a fallback point not yet a storage, which
  // `Jit.tailOutcome` reads untyped (its FIXME), so cons's native makes no such cell and the strict dispatch throws
  // `TypedVersionDomain`; this test passed under the construction as written, deleted with the specialized spelling.
  test("aListOfListsWithoutEndRunsUnderBothDispatches".fail) {
    val inner = fixpoint(λ(ones => cons(successor(zero))(ones)))
    val headOfHead = listFold(zero)(
      λ(head => λ(_ => listFold(zero)(λ(item => λ(_ => item)))(head)))
    )
    for
      (outer, index) <- Vector(
        cons(inner)(nil),
        fixpoint(λ(rest => cons(inner)(rest)))
      ).zipWithIndex
      dispatch <- Vector(fallback, strict)
    do
      val program = headOfHead(outer)
      val run = compiledRun(dispatch, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"outer $index under ${dispatch.name}"
      )
      assertEquals(run.decodings, 0L, s"outer $index under ${dispatch.name}")
  }

  /** A program over a value the conversion of #2163 B1 concerns: a natural
    * written as constructors, a list of such naturals, or a natural that a
    * library function (double) builds, all small.
    */
  private def spellingProgram(random: SplitMix): (Program, SplitMix) =
    val (kind, afterKind) = random.between(0, 2)
    val (size, afterSize) = afterKind.between(0, 2)
    val natural = (1 to size).foldLeft(zero)((inner, _) => successor(inner))
    kind match
      case 0 => (natural, afterSize)
      case 1 =>
        (
          (1 to size + 1).foldLeft(nil)((rest, _) => cons(natural)(rest)),
          afterSize
        )
      case _ => (double(natural), afterSize)

  // The spellings HM's schedule extracts for values written in the program
  // and built by a library function, recorded, not expected: the schedule's
  // output and the term each dispatch's refinement makes of it, so that
  // #2167 records whether every layer is the unique spelling
  // C (f1 ∥ F1) … ∥ T (the hypothesis) or a field is left unfiltered,
  // filtered twice or spelled as a fallback point.
  test("theSpellingsHindleyMilnerExtracts") {
    val crossed = encoding.crossedAllFromNoFacts(JitTesting.libraryTerms.values)
    val known = ReadableText.KnownNames.Written[encoding.type](
      JitTesting.libraryTerms.map((name, term) => crossed(term) -> name)
    )
    val lines = EvaluatorTesting
      .draws(8, 20261124L)(spellingProgram)
      .zipWithIndex
      .map((program, index) =>
        val (suite, input) = programInput(Suite.fresh, program)
        val output = Schedule
          .run(
            index,
            Vector(input),
            hindleyMilnerSchedule,
            StopSignal.NeverStopped
          )
          .outputs match
          case Vector(found) => found
          case other         =>
            fail(s"the schedule of one program gave ${other.size} outputs")
        // A term holding storages is printed with each storage written out as its view `x ∥ T` (the display reading of `ReadableText`).
        def printed(term: Configured[encoding.type]): String =
          ReadableText.printedNameless(term, known).text
        val extracted =
          s"schedule output: ${printed(output)}" +: Vector(fallback, strict)
            .map(dispatch =>
              val dispatched =
                StrategyDispatch.dispatched[encoding.type](
                  CompilationStrategy[encoding.type](
                    dispatch,
                    hindleyMilnerSchedule
                  ),
                  input,
                  encoding,
                  suite.cache,
                  StopSignal.NeverStopped
                )
              s"${dispatch.name}: ${printed(dispatched.refined)}"
            )
        (Vector(
          index.toString,
          ReadableText.printedNameless(input, known).text
        ) ++ extracted).mkString("\t")
      )
    assertFileSnapshot(
      lines.mkString("\n") + "\n",
      "native-route/hindley-milner-spellings.txt"
    )
  }

  // Under the strategy `strict` these programs, which HM types, run as
  // under `fallback`: every check of a fallback point the run meets holds.
  (Vector(
    successor(successor(zero)),
    natFold(zero)(compose(successor)(successor))(successor(zero)),
    successor(natFold(zero)(compose(successor)(successor))(successor(zero))),
    successor(natFold(zero)(λ(x => successor(successor(x))))(successor(zero))),
    booleanNot(booleanNot(trueName)),
    cons(successor(zero))(cons(zero)(nil))
  ) ++ coveredPrograms).zipWithIndex.foreach { (program, index) =>
    val name = s"strictRunsTheProgramsHindleyMilnerTypes: program $index"
    // KNOWN FAILURE until step 8 (https://github.com/Atry/private-overlay/issues/2176): programs 5, 7, 10 and 12 build
    // their lists cell by cell, each tail a fallback point not yet a storage, which `Jit.tailOutcome` reads untyped, so
    // the strict dispatch throws `TypedVersionDomain` (its FIXME).
    test(if Set(5, 7, 10, 12).contains(index) then name.fail
    else munit.TestOptions(name)) {
      val run = compiledRun(strict, hindleyMilnerSchedule, program)
      assert(JitTesting.sameTerms(run.answers, referenceAnswers(program)))
      assertEquals(run.decodings, 0L)
    }
  }

  // Programs HM types through a Maybe whose just is successor's term run
  // under `strict` and read the reference's normal forms: HM types them, so
  // they run (CONTRIBUTING.md, "Ordinary programs compile as a native typed compiler compiles them"),
  // and of the types their terms admit the program chooses the one the whole
  // program has (CONTRIBUTING.md, "Several types or encodings are options, never a cost"). Its purpose is to catch a typing that
  // picks the naturals for the Maybe and throws at the check of a fallback
  // point, which this test asked for until 2026-11-19.
  maybePrograms.zipWithIndex.foreach { (program, index) =>
    val name =
      s"strictRunsTheProgramsHindleyMilnerTypesThroughAMaybe: program $index"
    test(name) {
      assert(
        JitTesting.sameTerms(
          compiledRun(strict, hindleyMilnerSchedule, program).answers,
          referenceAnswers(program)
        )
      )
    }
  }

  test("fallbackRunsTheProgramsHindleyMilnerTypesThroughAMaybe") {
    maybePrograms.zipWithIndex.foreach { (program, index) =>
      val run = compiledRun(fallback, hindleyMilnerSchedule, program)
      assert(
        JitTesting.sameTerms(run.answers, referenceAnswers(program)),
        s"program $index"
      )
      assertEquals(run.decodings, 0L, s"program $index")
    }
  }

  // Programs whose values' own structure refutes a typed version's candidacy
  // still have a type under the recursive types the baseline supports, so
  // under `strict` they run and read the reference's normal forms
  // (CONTRIBUTING.md, "Several types or encodings are options, never a
  // cost": only a program with no feasible type is rejected; "Soundness,
  // monotonicity, modularity, budgets": a missing native representation only
  // slows a program down). Their purpose is to catch a typing that keeps a
  // typed version whose candidacy is refuted and throws at its check.
  Vector(
    booleanNot(cons(trueName)(nil)),
    cons(successor(zero))(cons(falseName)(nil))
  ).zipWithIndex.foreach { (program, index) =>
    val name =
      s"strictRunsValuesWhoseStructureRefutesACandidacy: program $index"
    // KNOWN FAILURE until step 8 (https://github.com/Atry/private-overlay/issues/2176): program 1 builds its list cell by
    // cell, each tail a fallback point not yet a storage, which `Jit.tailOutcome` reads untyped, so the strict dispatch
    // throws `TypedVersionDomain` (its FIXME).
    test(if index == 1 then name.fail else munit.TestOptions(name)) {
      assert(
        JitTesting.sameTerms(
          compiledRun(strict, hindleyMilnerSchedule, program).answers,
          referenceAnswers(program)
        )
      )
    }
  }

  // Under `strict`, a run that meets a fallback point whose check does not
  // hold throws the domain error: a specialization written in the program,
  // successor applied to a list beside its typed version by nat_type,
  // refined as written with no round of typing. Its purpose is to catch
  // strict running a value outside a typed version's domain.
  test("strictRejectsAValueOutsideATypedVersionDomain") {
    val argument = cons(zero)(nil)
    val program = JitTesting.termInstruction(
      successor(argument) + (successor(argument ∥ natType) ∥ natType)
    )
    intercept[TypedVersionDomain](
      normalFormsSpent(
        Jit(configuration(strict)),
        Value.of(StandardRefinement.refined[encoding.type](encoding, program)),
        normalFormLimit
      )
    )
  }

  // Programs HM rejects whose terms admit a native type read the reference's
  // normal forms under `strict` too (CONTRIBUTING.md, "Several types or encodings are options, never a cost": a
  // program HM rejects for having several feasible types is not rejected here): in
  // boolean_not (nat_fold zero successor (successor zero)) the conflict puts
  // boolean_type and nat_type in one class.
  // Their purpose is to catch a typing that rejects such a program.
  test("strictRunsAFoldOfTrueHindleyMilnerRejects") {
    val program = natFold(zero)(trueName)(successor(zero))
    assert(
      JitTesting.sameTerms(
        compiledRun(strict, hindleyMilnerSchedule, program).answers,
        referenceAnswers(program)
      )
    )
  }

  // FIXME: runs only by a tie the extraction breaks by hash code (ContentOrder). nat_fold's step is
  // https://github.com/Atry/private-overlay/issues/1945
  // successor passed as a value, and successor's class holds two contracts, λx. s x + s (x ∥ A) ∥ A
  // with A nat_type or boolean_type, of one cost: the conflict merges the step's type classes, both
  // candidacies are refuted and every typed call is repelled, but a contract of a function used
  // unapplied is checked at no call (Production.repelledDomains reads a call's argument), so the
  // extraction keeps one by the tie. Under a hash that picks boolean_type, strict throws
  // typed_version_domains([boolean]).
  test("strictRunsTheNegationOfAFoldHindleyMilnerRejects") {
    val program = booleanNot(natFold(zero)(successor)(successor(zero)))
    assert(
      JitTesting.sameTerms(
        compiledRun(strict, hindleyMilnerSchedule, program).answers,
        referenceAnswers(program)
      )
    )
  }

  /** The runs of a schedule and the codes the JIT compiled for the test
    * nat_fold zero (compose successor successor) applied to successor^size
    * zero, compiled under `fallback` and run from the suite
    * (`function_test_costs/4`). The suite after.
    */
  private def functionTestCosts(suite: Suite, size: Int): (Suite, Int, Int) =
    val (withInput, input) = programInput(
      suite,
      natFold(zero)(compose(successor)(successor))(numeral(size))
    )
    val (after, run) =
      dispatchedRun(withInput, fallback, hindleyMilnerSchedule, input)
    (after, run.typings, run.codesCompiled)

  // Plan principles 157 and 158 (jit_strategies.pl, THE TEST IS THE UNIT):
  // the tests f a, f b and f c of one f each run the schedule once, and only
  // the first compiles f's codes; a test met again runs no schedule.
  test("theTestsOfOneFunctionCompileItOnce") {
    val (afterFirst, firstTypings, firstCodes) =
      functionTestCosts(Suite.fresh, 2)
    val (afterSecond, secondTypings, secondCodes) =
      functionTestCosts(afterFirst, 3)
    val (afterThird, thirdTypings, thirdCodes) =
      functionTestCosts(afterSecond, 5)
    val (_, againTypings, againCodes) = functionTestCosts(afterThird, 3)
    println(
      s"codes compiled: $firstCodes, $secondCodes, $thirdCodes and $againCodes"
    )
    assert(firstCodes > 0)
    assertEquals(
      Vector(firstTypings, secondTypings, thirdTypings, againTypings),
      Vector(1, 1, 1, 0)
    )
    assertEquals(Vector(secondCodes, thirdCodes, againCodes), Vector(0, 0, 0))
  }

  // The run-time check of first-order data costs each element no more from
  // size 32 to 128 than from 8 to 32, on data HM types and on data it
  // rejects, after a run at size 4 has compiled the family's codes, and
  // each family's largest reaches its fixed point within the budget of each
  // round, 20,000 instances.
  test("theRunsCheckCostsAnElementDoNotGrow") {
    Vector(
      "numerals",
      "lists",
      "list_ending_in_a_boolean",
      "successor_of_a_list"
    ).foreach { family =>
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
    assert(
      JitTesting.sameTerms(run.answers, referenceAnswers(recursiveCount(8)))
    )
    assertEquals(run.decodings, 0L)
  }

  /** Purpose: catch the instance table changing the answers now that it tables
    * instances read inside a fallback point's check, readings that cut a
    * recurring operand included. Each program compiled under the fallback
    * dispatch reads the same normal forms with the instance table as without
    * it; the readings must cut some operand, or the law says nothing about that
    * case. The reading with the table is given twice the steps: the table costs
    * a constant factor more steps, not a higher order (tablambda's algorithms,
    * which set the time complexity). MEASURED 2026-11-19 on beyondBothProgram
    * at sizes 2, 4 and 8 under the markers spelled as tags: 11,734, 53,934 and
    * 1,199,470 steps without the table, 19,547, 89,895 and 2,000,135 with it,
    * 1.67 times each; at size 8 the reading with it ran out of the same
    * 2,000,000 steps.
    */
  stoppableTest("theInstanceTableInsideFallbackChecksLeavesTheAnswers") {
    stopped =>
      val untabled = fallbackConfiguration
      val tabled =
        JitConfiguration[encoding.type](
          untabled.specializer,
          untabled.budget,
          untabled.strategy,
          untabled.backend,
          untabled.dispatch,
          instanceTable = true,
          storageAccess = gezi.ir.StorageAccess.granted()
        )
      val programs = Vector(1, 4, 8).flatMap(size =>
        Vector(
          recursiveCount(size),
          closureChain(size),
          familyProgram("fold", size),
          familyProgram("doubles", size),
          numeral(size)
        )
      ) ++ Vector(
        beyondHindleyMilnerProgram,
        beyondBothProgram(8),
        fixpoint(λ(y => successor(y)))(zero)(λ(_ => zero)),
        fixpoint(λ(y => successor(successor(y))))(zero)(
          λ(p => p(zero)(λ(_ => zero)))
        )
      ) ++ listsWithoutEnd
      val cuts = programs.map { program =>
        val (_, input) = programInput(Suite.fresh, program)
        val refined = Value.of(
          StrategyDispatch
            .dispatched[encoding.type](
              CompilationStrategy[encoding.type](
                fallback,
                hindleyMilnerSchedule
              ),
              input,
              encoding,
              Suite.fresh.cache,
              StopSignal.completedWith(stopped)
            )
            .refined
        )
        val withoutTable =
          normalFormsSpent(Jit(untabled), refined, normalFormLimit)
        val withTable =
          normalFormsSpent(Jit(tabled), refined, 2 * normalFormLimit)
        assert(
          JitTesting.sameOutcomes(withTable.outcome, withoutTable.outcome),
          program.toString
        )
        JitRunState
          .held(withTable.jitState, tabled)
          .map(_.cuts)
          .getOrElse(
            fail(s"no JIT state after the reading: ${withTable.jitState}")
          )
      }
      println(
        s"instance table inside checks: ${programs.size} programs, cuts ${cuts.mkString(", ")}"
      )
      assert(cuts.exists(_ > 0), "no reading cut an operand")
  }

  // The run of a natural that a closure builds, (\y. successor^size y)
  // zero, costs each successor no more from 32 to 128 than from 8 to 32,
  // after a run at 4 has compiled its codes; the run at 8 calls
  // successor's native 8 times and decodes nothing.
  test("aClosuresNaturalsRunCostsASuccessorDoNotGrow") {
    runCostsDoNotGrow("closure chain", costSchedule, closureChain)
    val run = compiledRun(fallback, costSchedule, closureChain(8))
    assert(JitTesting.sameTerms(run.answers, referenceAnswers(closureChain(8))))
    assertEquals(run.decodings, 0L)
    assertEquals(run.calls.get(successorNative), Some(8L))
  }

  /** The program of the family at the size: `fold`, the fold of successor twice
    * over successor^size zero; `doubles`, even of double^size (successor zero)
    * (`family_program/3`).
    */
  private def familyProgram(family: String, size: Int): Program = family match
    case "fold" => natFold(zero)(compose(successor)(successor))(numeral(size))
    case "doubles" => even(doubles(size, successor(zero)))
    case other     => fail(s"no family $other")

  /** The instances of the two rounds of the program of the family at the size,
    * each reaching its fixed point (`compilation_instances/3`).
    */
  private def compilationInstances(family: String, size: Int): Int =
    val (suite, input) = programInput(Suite.fresh, familyProgram(family, size))
    val scheduled = Schedule.run(
      library.index,
      Vector(input),
      hindleyMilnerSchedule,
      StopSignal.NeverStopped
    )
    scheduled.records.map(_.report) match
      case Vector(
            FixpointReport(End.FixedPoint(typeCheck)),
            FixpointReport(End.FixedPoint(erasure))
          ) =>
        typeCheck + erasure
      case reports => fail(s"the rounds reported $reports")

  /** From size 4 to 16 to 64, the instances each added element costs do not
    * grow (the Prolog test measured 500, 1,196 and 3,980 instances for the
    * fold, 58 a successor over each span, and 233, 521 and 1,673 for the
    * doubles, 24 a double).
    */
  private def instancesDoNotGrow(family: String): Unit =
    val small = compilationInstances(family, 4)
    val middle = compilationInstances(family, 16)
    val large = compilationInstances(family, 64)
    val before = (middle - small).toDouble / 12
    val after = (large - middle).toDouble / 48
    assert(
      after <= before,
      s"$family: $small, $middle and $large instances at 4, 16 and 64"
    )

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
      assert(
        compiledLikeTheReference(hindleyMilnerSchedule, program).calls
          .contains(native),
        native.toString
      )
    )
  }

  // Beyond HM: the closure parameter g is used at nat -> nat and at
  // boolean -> boolean; the round with the beta rule reduces each
  // application of the identity closure, and the type check reads the
  // reduct. The run calls successor's native, and its booleans are in their
  // representation: the typed boolean constants are the storages the
  // specialized spelling makes at construction, their constructors' natives
  // called there.
  test("beyondHindleyMilner") {
    val run =
      compiledLikeTheReference(beyondSchedule, beyondHindleyMilnerProgram)
    assert(run.calls.contains(successorNative), s"${run.calls}")
    assert(run.stored.contains(Representation.Truth), s"${run.stored}")
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
    val run =
      compiledBeyondTheReference(hindleyMilnerSchedule, even(power), trueName)
    assertEquals(
      run.calls.get(NativeName.Function("natural_double")),
      Some(64L)
    )
    assertEquals(run.calls.get(NativeName.Function("natural_even")), Some(1L))
    compiledBeyondTheReference(
      hindleyMilnerSchedule,
      even(successor(power)),
      falseName
    )
  }

  // Beyond both: the closure parameter of the program beyond HM used around
  // the parity of double^n (successor zero), compiled by the beta round and
  // the type check of the reduct; at n = 8 the reference agrees, at n = 64
  // it reads no answer.
  test("beyondHindleyMilnerAndWeakHead") {
    compiledLikeTheReference(beyondSchedule, beyondBothProgram(8))
    val run = compiledBeyondTheReference(
      beyondSchedule,
      beyondBothProgram(64),
      falseName
    )
    assertEquals(
      run.calls.get(NativeName.Function("natural_double")),
      Some(64L)
    )
    assertEquals(run.calls.get(NativeName.Function("natural_even")), Some(1L))
  }
