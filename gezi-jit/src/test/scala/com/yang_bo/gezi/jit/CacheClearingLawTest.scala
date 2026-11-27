package com.yang_bo.gezi.jit

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import com.yang_bo.gezi.strategies.BaselineRounds
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.jit.NativesTesting.normalFormsSpent
import com.yang_bo.gezi.strategies.DispatchStrategies
import com.yang_bo.gezi.strategies.StrategyTesting
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The clearing law (clearing a cache changes only cost, never an answer) on
  * the cache service of the baseline and `jit`'s namespace `DispatchCache`: a
  * point dispatched (`StrategyDispatch.dispatched`) under a strategy with a
  * service that the dispatches of other points and of the point itself filled,
  * each under a strategy drawn from three (the point's drawn apart from the one
  * it is checked under, at a drawn place among the others), gives the refined
  * term a dispatch with an empty service gives, and the JIT reads the same set
  * of normal forms of the two, each among those the weak-head reference reads
  * of the point. Its purpose is to catch a namespace whose entries change an
  * answer, not only its cost: a key that leaves out an input of what it
  * memoizes (the strategies differ in the schedule's budget and in the
  * refinement, so a key without either answers one strategy's term for
  * another's), or a value that is not the memo of a pure function of the term.
  * The inputs are closed terms of `HoasGenerators.openTermOver` of at most
  * twelve nodes over the native route library's terms
  * (`JitTesting.nativeRouteLeaves`), with the strategies drawn; the library is
  * `NativesTesting.nativesOn`, the Prolog backend's preset with
  * closure_application and occurrence_erasure, and the type check's round is
  * the rounds fixture's `prolog_backend_type_check`, the preset's type-check
  * round (native typing is enabled through the preset only). The drawn programs
  * are the point, and the other points dispatched before it into the filled
  * service.
  *
  * The two readings are compared as sets: the order of the normal forms is not
  * claimed to be independent of the order in which the dispatches met the
  * terms.
  */
class CacheClearingLawTest extends GeneratedProperties:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CacheClearingLawTest, "a filled cache service dispatches and reads what an empty one does", takes 8.287 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  /** The natives-on library, its facts, the type check's round, the strategies
    * with their schedule, the JIT and the generators' leaves, forced before the
    * first test and not charged to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => facts,
      _ => knowledge,
      _ => strategies,
      _ => jit,
      _ => JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts)
    )

  private lazy val library = NativesTesting.nativesOn

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val knowledge =
    StrategyTesting.round("prolog_backend_type_check")

  /** A refinement that gives the choice of the schedule's output with itself:
    * equal to the output by the idempotence of the choice, so it reads the same
    * normal forms, and always another term than the output, so that a key
    * without the refinement answers it for the baseline's refinement. (A
    * refinement that keeps the output gave the baseline's term on every
    * generated program tried, 60 of them, 2026-11-01, so a key without the
    * refinement passed with it.)
    */
  private object Doubled extends OutputRefinement:
    def refined[C <: NativeSpecializer & Singleton](
        specializer: StorageEncoding & C,
        output: Configured[C]
    )(using com.yang_bo.gezi.ir.StorageAccess): Configured[C] =
      specializer.choice(output, output)

  /** Three strategies of one dispatch strategy, so one JIT reads them all: the
    * schedule of 300 instances a round refined as the baseline refines, the
    * same schedule refined by `Doubled`, and its first round alone, the type
    * check without the erasure of the occurrence tags.
    */
  private lazy val strategies: Vector[CompilationStrategy[encoding.type]] =
    val schedule =
      BaselineRounds.nativeRouteSchedule[encoding.type](library, knowledge, 300)
    Vector(
      CompilationStrategy[encoding.type](DispatchStrategies.fallback, schedule),
      CompilationStrategy[encoding.type](
        DispatchStrategies.fallback,
        schedule,
        Doubled
      ),
      CompilationStrategy[encoding.type](
        DispatchStrategies.fallback,
        schedule.take(1)
      )
    )

  private lazy val jit =
    Jit(
      JitConfiguration[encoding.type](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.Dispatch(DispatchStrategies.fallback),
        instanceTable = false,
        storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )

  /** The steps a reading may take. A reading's heap grows linearly with its
    * steps: measured 2026-11-01 on `list_type list_type`, whose normal forms do
    * not end (568 of them in 50,000 weak-head steps), 38 MB live after 20,000
    * steps and 88 MB after 50,000, so that 200,000 steps exhausted the tests'
    * 256 MB heap. A generated program may be such a term.
    */
  private val limit: Long = 20000

  private def closedProgram: Gen[TermOf[Configured[NoFacts.type]]] =
    for
      nodes <- Gen.int(Range.linear(1, 12))
      open <- HoasGenerators.openTermOver(
        0,
        nodes,
        JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts)
      )
    yield open(Vector.empty)

  private def strategy: Gen[CompilationStrategy[encoding.type]] =
    Gen.int(Range.constant(0, 2)).map(strategies(_))

  /** The program interned and dispatched under the strategy with the service:
    * the input and the dispatch.
    */
  private def dispatched(
      program: TermOf[Configured[NoFacts.type]],
      strategy: CompilationStrategy[encoding.type],
      cache: Cache,
      stop: StopSignal
  ): (Configured[encoding.type], Dispatched[encoding.type]) =
    val inputWithoutFacts = StrategyTesting.programInput(library, program)
    val input = encoding.crossedAllFromNoFacts(Vector(inputWithoutFacts))(
      inputWithoutFacts
    )
    (
      input,
      StrategyDispatch
        .dispatched[encoding.type](strategy, input, encoding, cache, stop)
    )

  private def reading(
      dispatch: Dispatched[encoding.type]
  ): Bounded[Vector[Configured[encoding.type]]] =
    normalFormsSpent(jit, Value.of(dispatch.refined), limit, NoJitState).outcome

  stoppableProperty(
    "a filled cache service dispatches and reads what an empty one does",
    _.copy(testLimit = SuccessCount(5))
  ) { stopped =>
    for
      point <- closedProgram.forAll
      pointStrategy <- strategy.forAll
      earlierStrategy <- strategy.forAll
      others <- Gen
        .list(
          closedProgram.flatMap(program => strategy.map((program, _))),
          Range.linear(0, 1)
        )
        .forAll
      position <- Gen.int(Range.constant(0, others.size)).forAll
    yield
      val fillings = others
        .take(position) ++ ((point, earlierStrategy) :: others.drop(position))
      val filling = BaselineCaches.provider()
      fillings.foreach((program, programStrategy) =>
        dispatched(
          program,
          programStrategy,
          filling,
          StopSignal.completedWith(stopped)
        )
      )
      val (input, filled) = dispatched(
        point,
        pointStrategy,
        filling,
        StopSignal.completedWith(stopped)
      )
      val (_, empty) = dispatched(
        point,
        pointStrategy,
        BaselineCaches.provider(),
        StopSignal.completedWith(stopped)
      )
      val reference = normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        Value.of(input),
        limit
      ).outcome
      def amongReference(
          outcome: Bounded[Vector[Configured[encoding.type]]]
      ): Result = (outcome, reference) match
        case (Bounded.Finished(found), Bounded.Finished(expected)) =>
          Result
            .assert(
              found.forall(candidate =>
                expected.exists(Configured.same(candidate, _))
              )
            )
            .log(s"$found not among $expected")
        case _ => Result.success
      val (filledReading, emptyReading) = (reading(filled), reading(empty))
      Result.all(
        List(
          Result
            .assert(Configured.same(filled.refined, empty.refined))
            .log(
              "the filled service's refined term is not the one a dispatch computes"
            ),
          (filledReading, emptyReading) match
            case (
                  Bounded.Finished(filledFound),
                  Bounded.Finished(emptyFound)
                ) =>
              Result.diff(filledFound.toSet, emptyFound.toSet)(_ == _)
            case _ => Result.success
          ,
          amongReference(filledReading),
          amongReference(emptyReading)
        )
      )
  }
