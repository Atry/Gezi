package gezi.warts

import dotty.tools.dotc.Main
import dotty.tools.dotc.reporting.Diagnostic
import dotty.tools.dotc.reporting.Reporter
import java.nio.file.Files
import java.nio.file.Paths
import snapshot4s.generated.snapshotConfig

/** Purpose: each custom wart reports its planted violation and passes its
  * clean site, so a wart that stops matching its symbol, or starts matching
  * a clean site, is caught. Each wart's two sources (test resources
  * `planted/<Wart>/planted.scala` and `clean.scala`, not Scala sources of
  * this build, so that no other check reads their planted violations) are
  * compiled by the Scala compiler with WartRemover's plugin and that wart
  * alone, and the compiler's diagnostics are the snapshot. The sources are
  * hand-written because a violation is the thing under test; a generated
  * input would have to be generated from the wart's own definition.
  *
  * The compiler runs in this test JVM (`dotty.tools.dotc.Main.process`),
  * one compilation per wart, with the options a child JVM running
  * `dotty.tools.dotc.Main` was given until 2026-11-14: eleven cold child
  * JVMs took 18.8 s of the suite (2026-11-14), the compiler's start-up and
  * warm-up repeated eleven times.
  */
class CustomWartsTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CustomWartsTest, "NoArray", takes 6.276 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  private val classpathEntries: Vector[String] =
    System.getProperty("java.class.path").split(java.io.File.pathSeparator).toVector

  private val wartremoverJar: String =
    classpathEntries.filter(_.contains("wartremover_3")).head

  private def snake(name: String): String =
    name.flatMap(character => if character.isUpper then s"_${character.toLower}" else character.toString).stripPrefix("_")

  /** The diagnostic's level, the file name, line and column of its point
    * (the compiler's own `line:column`, the line counted from 1), the text
    * of the source it marks, and its message.
    */
  private def rendered(level: String, diagnostic: Diagnostic): String =
    val position = diagnostic.pos
    val marked = position.source.content().slice(position.start, position.end).mkString
    s"$level ${position.source.file.name}:${position.line + 1}:${position.column} marking \"$marked\": ${diagnostic.message}"

  /** The compiler's diagnostics for the wart's two sources, sorted by file
    * and offset, then its summary. A reporter that prints nothing
    * (`Reporter.SilentReporter`) still keeps every diagnostic it was given
    * (`allErrors`, `allWarnings`, `allInfos`).
    */
  private def compiled(wart: String): String =
    val sourceDirectory = Paths.get(System.getProperty("gezi.wartsRoot")).resolve("src/test/resources/planted").resolve(wart)
    val classes = Files.createTempDirectory("custom-wart")
    val sources = Vector("planted.scala", "clean.scala").map(name => sourceDirectory.resolve(name).toString)
    val classpath = classpathEntries.mkString(java.io.File.pathSeparator)
    val arguments = Vector(
      "-classpath",
      classpath,
      "-color:never",
      "-d",
      classes.toString,
      s"-Xplugin:$wartremoverJar",
      s"-P:wartremover:traverser:gezi.warts.$wart"
    ) ++ classpathEntries.map(entry => s"-P:wartremover:cp:file:$entry") ++ sources
    val reporter = Main.process(arguments.toArray, Reporter.SilentReporter())
    val diagnostics =
      reporter.allErrors.map(error => ("Error", error)) ++
        reporter.allWarnings.map(warning => ("Warning", warning)) ++
        reporter.allInfos.map(info => ("Info", info))
    val lines = diagnostics
      .sortBy((_, diagnostic) => (diagnostic.pos.source.file.name, diagnostic.pos.start, diagnostic.pos.point))
      .map(rendered)
    (lines :+ reporter.summary).mkString("", "\n", "\n")

  Vector(
    "NoArray",
    "NoDynamicVariable",
    "NoIterator",
    "NoJavaUtilConcurrent",
    "NoJavaUtilMutableCollection",
    "NoNewBuilder",
    "NoStringBuilder",
    "NoThreadLocal",
    "NoUnsafe",
    "NoVarHandle",
    "NoVolatile"
  ).foreach(wart => test(wart) { assertFileSnapshot(compiled(wart), s"warts/${snake(wart)}.txt") })
