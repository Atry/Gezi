package gezi.standardlibrary

/** The port of what `gezi/tests/loading.plt` checks about Gezi: what a
  * computation concludes depends on its input and not on what the process ran
  * before (`gezi/prolog/gezi/loading.pl`, THE COUNTS LOAD NO CODE). In
  * SWI-Prolog the hazard was code loaded by the autoloader inside a count of
  * inferences; the JVM loads no code into a count of steps, and a compiled
  * library is a value of its inputs.
  *
  * Of the Prolog test
  * `compiling_and_running_the_native_route_autoloads_nothing`, the compilation
  * of the native route's library, the Prolog backend's preset (its backend and
  * the native typing of the types it represents) with closure_application and
  * occurrence_erasure, is checked here (native typing is enabled through the
  * preset only): compiled first in a process, or after other libraries were
  * compiled, it is the same value. The rest of that test, the readings, is
  * `gezi.jit.LoadingReadingsTest` in the module `jit`, which `standardlibrary`
  * does not depend on: the reference reads `even (double (successor zero))`
  * within a budget, the program compiled on the native route reads within a
  * budget that runs out partway and within one the reading ends in, each the
  * same whatever ran before.
  *
  * The two other tests of the Prolog file check SWI-Prolog's autoloader by
  * cross-referencing the Prolog sources, and have no counterpart: the test
  * table says so.
  */
class LoadingTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of LoadingTest, "compilingAndRunningTheNativeRouteAutoloadsNothing", takes 19.865 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(30, "s")

  /** The file of the native route's knowledge, the choice of the Prolog
    * backend's preset with closure_application and occurrence_erasure, the one
    * field of its tuple.
    */
  private val presetsFile = "tests/library_fixtures/presets.lambdalattice"

  private def nativeRouteLibrary: StandardLibrary =
    LibraryFiles.compiled(presetsFile, Vector.empty)

  test("compilingAndRunningTheNativeRouteAutoloadsNothing") {
    val first = nativeRouteLibrary
    LibraryFiles.compiled(
      "tests/library_fixtures/prelude_guard_laws.lambdalattice",
      Vector.empty
    )
    LibraryFiles.compiled(
      "tests/library_fixtures/opacity.lambdalattice",
      Vector.empty
    )
    assertEquals(nativeRouteLibrary, first)
  }
