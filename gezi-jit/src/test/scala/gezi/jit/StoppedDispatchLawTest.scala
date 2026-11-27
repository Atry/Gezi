package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.ir.{Configured, NoFacts}
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.hotspot.baselines.BaselineCaches
import gezi.strategies.BaselineRounds
import gezi.saturation.StopSignal
import gezi.strategies.DispatchStrategies
import gezi.strategies.StrategyTesting

/** The law of a stopped dispatch (judge record 4.4): a dispatch whose stop
  * signal asks for a stop from the start leaves `DispatchCache` as it was,
  * so that the next dispatch of the same test under the same strategy runs
  * its schedule. Its purpose is to catch a stopped schedule's output, which
  * depends on when the stop came and not on the key, written to the cache
  * and answered later as the test's refined term. The generated programs'
  * leaves are `JitTesting.nativeRouteLeaves`; the library is
  * `NativesTesting.nativesOn`, the Prolog backend's preset with
  * closure_application and occurrence_erasure, and the type check's round is
  * the rounds fixture's `prolog_backend_type_check`, the preset's type-check
  * round (native typing is enabled through the preset only).
  */
class StoppedDispatchLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of StoppedDispatchLawTest, "a stopped dispatch is not cached", takes 7.209 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, "s")

  /** The natives-on library, its facts, the strategy with its schedule and the generators' leaves, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => facts, _ => strategy, _ => JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts))

  private lazy val library = NativesTesting.nativesOn

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val strategy = CompilationStrategy[encoding.type](
    DispatchStrategies.fallback,
    BaselineRounds.nativeRouteSchedule[encoding.type](library, StrategyTesting.round("prolog_backend_type_check"), 300)
  )

  private object Requested extends StopSignal:
    def stopRequested: Boolean = true

  /** A generated closed program over the native route's library terms, closed terms of no facts. */
  private def closedProgram: Gen[TermOf[Configured[NoFacts.type]]] =
    for
      nodes <- Gen.int(Range.linear(1, 12))
      open <- HoasGenerators.openTermOver(0, nodes, JitTesting.nativeRouteLeaves[NoFacts.type](using NoFacts))
    yield open(Vector.empty)

  stoppableProperty("a stopped dispatch is not cached", _.copy(testLimit = SuccessCount(10))) { deadline =>
    for program <- closedProgram.forAll
    yield
      val inputWithoutFacts = StrategyTesting.programInput(library, program)
      val input = encoding.crossedAllFromNoFacts(Vector(inputWithoutFacts))(inputWithoutFacts)
      val cache = BaselineCaches.provider()
      val stopped = StrategyDispatch.dispatched[encoding.type](strategy, input, encoding, cache, Requested)
      val again = StrategyDispatch.dispatched[encoding.type](strategy, input, encoding, cache, StopSignal.completedWith(deadline))
      Result.all(
        List(
          Result.assert(stopped.scheduleRan).log("the stopped dispatch did not run its schedule"),
          Result.assert(again.scheduleRan).log("the dispatch after a stopped one was answered by the cache")
        )
      )
  }
