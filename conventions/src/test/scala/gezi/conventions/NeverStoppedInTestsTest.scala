package gezi.conventions

import java.nio.file.Files

/** The test sources that name `StopSignal.NeverStopped`.
  *
  * Purpose: a test that hands `NeverStopped` to a computation gives the
  * deadline of `FailFastSuite` nothing to complete, so an overrunning test
  * keeps the computation running on its thread until the JVM exits
  * (CONTRIBUTING.md, "Tests fail fast"). A test takes its signal from
  * `stoppableTest`. A source that still names `NeverStopped` is listed here
  * with the reason; the list shrinks as the tests are converted, and a source
  * not listed fails.
  */
object NeverStoppedInTestsCheck:

  private val reasonNeverStoppedIsSubject =
    "the test is a law about the NeverStopped signal itself"

  /** The sources allowed to name `NeverStopped`, by path under the build's
    * root, each with its reason.
    */
  val listed: Map[String, String] =
    Map(
      "conventions/src/test/scala/gezi/conventions/NeverStoppedInTestsTest.scala" -> "this check names the symbol it bans",
      "weakhead/src/test/scala/gezi/weakhead/BudgetStopLawTest.scala" -> reasonNeverStoppedIsSubject,
      "jit/src/test/scala/gezi/jit/JitNativesTest.scala" ->
        ("FIXME: `compiledFixtures` is a lazy value shared by many tests, computed once per JVM as a `sharedFixtures` entry " + // https://github.com/Atry/private-overlay/issues/2030
          "under `NeverStopped`, so the fixture's deadline does not stop it (it is to take the fixture's signal); " +
          "`nativesRunOnTheRefinedX2` is the entry of a child JVM, " +
          "a top-level owner with no test"),
      "jit/src/test/scala/gezi/jit/NativeRouteCompilationTest.scala" ->
        ("FIXME: `roundsReachTheirFixedPoints`, `dispatchedRun` and `compilationInstances` are called through eight more helpers " + // https://github.com/Atry/private-overlay/issues/2030
          "by about thirty tests; their signal is to be threaded through those helpers")
    )

  private def isTestSupport(path: String): Boolean =
    path.contains("/src/test/scala/") || path.startsWith(
      "interface-laws/src/main/scala/"
    )

  /** The test sources that name `NeverStopped` and are not listed, each
    * `path:number: text`.
    */
  def problems(sources: Vector[(String, String)]): Vector[String] =
    sources
      .filter((path, _) => isTestSupport(path) && !listed.contains(path))
      .flatMap((path, text) =>
        val code = ScalaSources.commentsBlanked(text).split('\n').toVector
        val lines = text.split('\n').toVector
        lines.zipWithIndex.collect {
          case (line, index)
              if code(index).contains("StopSignal.NeverStopped") =>
            s"$path:${index + 1}: ${line.trim}"
        }
      )

  /** The listed sources that no longer name `NeverStopped`: their entries are
    * deleted.
    */
  def staleEntries(sources: Vector[(String, String)]): Vector[String] =
    val naming = sources.collect {
      case (path, text)
          if ScalaSources
            .commentsBlanked(text)
            .contains("StopSignal.NeverStopped") =>
        path
    }.toSet
    listed.keys.filterNot(naming.contains).toVector.sorted

class NeverStoppedInTestsTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => ScalaSources.texts)

  private def sources = ScalaSources.texts

  test("no test source names NeverStopped unless it is listed with a reason") {
    assert(sources.nonEmpty, "no Scala source found")
    val found = NeverStoppedInTestsCheck.problems(sources)
    assert(found.isEmpty, found.mkString("\n"))
  }

  test("every listed source still names NeverStopped") {
    val stale = NeverStoppedInTestsCheck.staleEntries(sources)
    assert(stale.isEmpty, stale.mkString("\n"))
  }
