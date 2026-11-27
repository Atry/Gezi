package com.yang_bo.gezi.jit

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import com.yang_bo.gezi.strategies.BaselineRounds
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.strategies.DispatchStrategies
import com.yang_bo.gezi.strategies.Schedule
import com.yang_bo.gezi.strategies.StrategyTesting
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The law of `CompilationStrategy.refinement`: the dispatch refines a test's
  * output by the strategy's refinement, so that a refinement that keeps the
  * output gives the schedule's output itself, and the dispatch cache keeps the
  * two refinements of one test apart. Its purpose is to catch a dispatch that
  * ignores the refinement an entry gave, or answers one refinement's term from
  * the cache for another. The inputs are closed terms of
  * `HoasGenerators.openTermOver` of at most twelve nodes over the native route
  * library's terms (`JitTesting.nativeRouteLeaves`); the library is
  * `NativesTesting.nativesOn`, the Prolog backend's preset with
  * closure_application and occurrence_erasure, and the type check's round is
  * the rounds fixture's `prolog_backend_type_check`, the preset's type-check
  * round (native typing is enabled through the preset only).
  */
class RefinementReplacementLawTest extends GeneratedProperties:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of RefinementReplacementLawTest, "the dispatch refines by the strategy's refinement", takes 14.979 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(25, "s")

  /** The natives-on library, its facts, the schedule and the generators'
    * leaves, forced before the first test and not charged to it
    * (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => facts,
      _ => schedule,
      _ => JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts)
    )

  private lazy val library = NativesTesting.nativesOn

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val schedule = BaselineRounds.nativeRouteSchedule[encoding.type](
    library,
    StrategyTesting.round("prolog_backend_type_check"),
    300
  )

  /** A refinement that keeps the output as it is. */
  private object Kept extends OutputRefinement:
    def refined[C <: NativeSpecializer & Singleton](
        specializer: StorageEncoding & C,
        output: Configured[C]
    )(using com.yang_bo.gezi.ir.StorageAccess): Configured[C] = output

  /** A generated closed program over the native route's library terms, closed
    * terms of no facts.
    */
  private def closedProgram: Gen[TermOf[Configured[NoFacts.type]]] =
    for
      nodes <- Gen.int(Range.linear(1, 12))
      open <- HoasGenerators.openTermOver(
        0,
        nodes,
        JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts)
      )
    yield open(Vector.empty)

  stoppableProperty(
    "the dispatch refines by the strategy's refinement",
    _.copy(testLimit = SuccessCount(10))
  ) { stopped =>
    for program <- closedProgram.forAll
    yield
      val inputWithoutFacts = StrategyTesting.programInput(library, program)
      val input = encoding.crossedAllFromNoFacts(Vector(inputWithoutFacts))(
        inputWithoutFacts
      )
      val Vector(output) = Schedule
        .run(
          encoding.operations.index,
          Vector(input),
          schedule,
          StopSignal.completedWith(stopped)
        )
        .outputs: @unchecked
      val kept = CompilationStrategy[encoding.type](
        DispatchStrategies.fallback,
        schedule,
        Kept
      )
      val cache = BaselineCaches.provider()
      val first = StrategyDispatch.dispatched[encoding.type](
        kept,
        input,
        encoding,
        cache,
        StopSignal.completedWith(stopped)
      )
      val standard = CompilationStrategy[encoding.type](
        DispatchStrategies.fallback,
        schedule
      )
      val second = StrategyDispatch.dispatched[encoding.type](
        standard,
        input,
        encoding,
        cache,
        StopSignal.completedWith(stopped)
      )
      val standardRefined = Refinement(encoding).refined(output)
      Result.all(
        List(
          Result.assert(Configured.same(first.refined, output)),
          Result.assert(Configured.same(second.refined, standardRefined)),
          Result.diff((first.scheduleRan, second.scheduleRan), (true, true))(
            _ == _
          )
        )
      )
  }
