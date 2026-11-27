package com.yang_bo.gezi.jit

import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.jit.NativesTesting.*
import com.yang_bo.gezi.strategies.BaselineRounds
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.strategies.DispatchStrategies
import com.yang_bo.gezi.strategies.StrategyTesting
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches

/** The readings of `gezi/tests/loading.plt`'s test
  * `compiling_and_running_the_native_route_autoloads_nothing`
  * (`tests/loading_reads.pl`), whose compilation of the library
  * `com.yang_bo.gezi.standardlibrary.LoadingTest` checks: what a reading concludes depends
  * on its input and not on what ran before. The program is even (double
  * (successor zero)) on the native route's library, the Prolog backend's preset
  * with closure_application and occurrence_erasure
  * (`NativesTesting.presetsFile`; native typing is enabled through the preset
  * only), its library terms members of `JitTesting.libraryTermsFile`. The
  * reference reads it as written within a budget; the program is compiled on
  * the native route, the type check (the rounds fixture's
  * `prolog_backend_type_check`, the preset's type-check round) and the erasure
  * of `BaselineRounds.nativeRouteSchedule` and the refinement for the backend,
  * through `StrategyDispatch.dispatched` under the strategy `fallback`, and the
  * JIT reads the refined program within a budget that runs out partway and
  * within one its reading ends in; each reading is the same read first or after
  * other libraries were compiled and other terms read.
  */
class LoadingReadingsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of LoadingReadingsTest, "compilingAndRunningTheNativeRouteAutoloadsNothing", takes 24.828 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(40, "s")

  private def term[C <: NativeSpecializer & Singleton](key: String)(using
      C
  ): TermOf[Configured[C]] = JitTesting.libraryTerm[C](key)

  private def program[C <: NativeSpecializer & Singleton](using
      C
  ): TermOf[Configured[C]] =
    term[C]("even")(term[C]("double")(term[C]("successor")(term[C]("zero"))))

  /** The reference's reading of the program as written, the JIT's partway and
    * the JIT's whole of the program compiled and refined, on a library compiled
    * now, and the steps of the JIT's whole reading. Each round of the schedule
    * is within 500 instances, the Prolog test's.
    */
  private def readings(
      stop: StopSignal
  ): (Bounded[?], Bounded[?], Bounded[?], Long) =
    val library = LibraryFiles.compiled(presetsFile, Vector(BackendChecks))
    val encoding = BackendFacts.of(library).storageEncoding
    given encoding.type = encoding
    val reference = normalFormsSpent(
      Mode.TablingWeakHead,
      JitTesting.plainConfiguration(encoding),
      JitTesting.termValue(program[encoding.type]),
      normalFormLimit
    )
    val schedule = BaselineRounds.nativeRouteSchedule[encoding.type](
      library,
      StrategyTesting.round("prolog_backend_type_check"),
      500
    )
    val input = StrategyTesting
      .programInputIn[encoding.type](library, program[encoding.type])
    val Dispatched(refined, _, _) = StrategyDispatch.dispatched[encoding.type](
      CompilationStrategy(DispatchStrategies.fallback, schedule),
      input,
      encoding,
      BaselineCaches.provider(),
      stop
    )
    val jit = Jit(
      JitConfiguration.of[encoding.type](
        encoding,
        instanceTable = false,
        com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )
    val whole = normalFormsSpent(jit, refined, normalFormLimit)
    val partway = normalFormsSpent(jit, refined, whole.steps / 2)
    (reference.outcome, partway.outcome, whole.outcome, whole.steps)

  stoppableTest("compilingAndRunningTheNativeRouteAutoloadsNothing") {
    stopped =>
      val first = readings(StopSignal.completedWith(stopped))
      assert(first._1.finished, s"the reference: ${first._1}")
      assertEquals(first._2, Bounded.Exceeded)
      assertEquals(first._3, first._1)
      LibraryFiles.compiled(
        "tests/library_fixtures/prelude_guard_laws.lambdalattice",
        Vector(BackendChecks)
      )
      val encoding = nativesOnEncoding
      given encoding.type = encoding
      normalFormsSpent(
        Jit(configurationOf(encoding)),
        JitTesting
          .termValue(
            term[encoding.type]("successor")(
              term[encoding.type]("zero")
            ) ∥ term[encoding.type]("nat_type")
          ),
        normalFormLimit
      )
      assertEquals(readings(StopSignal.completedWith(stopped)), first)
  }
