package gezi.conventions

import java.nio.file.Files
import scala.util.matching.Regex

/** Source locations are for people and tools, never for a choice: only
  * the projects that read, carry or show a location may depend on
  * `locations` or `provenance`, by a `dependsOn` of the build or by naming
  * their packages in a source. Its purpose is to catch a strategy, a cost
  * model, the saturation, the extraction or an evaluator that comes to read
  * a location, which would make a location change a result. The framework's
  * projects are kept out of both by `FrameworkBoundaryTest` as well.
  */
class LocationsBoundaryTest extends gezi.generatedinputs.FailFastSuite:

  /** The projects that may use locations: the reader that makes them, the
    * module that computes a graph's, the migrations that rewrite texts at
    * them, the conventions that check this, and the trace's debug
    * information, which writes and shows where a trace's terms and lemmas
    * are written: the trace's text and its source maps, and the player;
    * and the benchmarks, which measure what reading and computing locations
    * cost and choose nothing by them.
    */
  private val allowed: Set[String] =
    Set("locations", "frontend", "provenance", "migration", "conventions", "rewrite-trace", "trace-player", "jmh-pipeline")

  /** The sources of other projects that may name the packages, by path under
    * the build's root, each with its reason: each carries a location to a
    * trace's debug information and chooses nothing by it.
    */
  private val allowedSources: Map[String, String] = Map(
    "standardlibrary/src/main/scala/gezi/standardlibrary/LemmaSources.scala" ->
      "the spans of a knowledge file's lemma declarations, read beside the library, which reads none of them",
    "standardlibrary/src/test/scala/gezi/standardlibrary/LemmaSourcesSnapshotTest.scala" -> "the snapshot of those spans",
    "contest-entry-generic/src/main/scala/gezi/contest/entry/generic/GenericEntry.scala" ->
      "the lemmas' texts handed to the trace it writes as evidence",
    "strategies/src/test/scala/gezi/strategies/TraceSourceMapsLawTest.scala" ->
      "a law of the trace's source maps, run over a saturation it builds",
    "trace-showcase-generator/src/test/scala/gezi/traceshowcase/ShowcasePages.scala" ->
      "the lemmas' texts handed to the traces of the player's showcase it writes (#1807)",
    "narrow-blocks/src/main/scala/gezi/narrowblocks/DebugAttributes.scala" ->
      "the debugging attributes of a class of narrow blocks, which no block's code reads (#1504, D6.2 and D7)",
    "narrow-blocks/src/main/scala/gezi/narrowblocks/NarrowBlockCompilation.scala" ->
      "the program's map walked beside its blocks for those attributes, the blocks found the same without it",
    "narrow-blocks/src/main/scala/gezi/narrowblocks/lists/NarrowBlockCompilation.scala" ->
      "the same walk in the opt-in copy of the narrow blocks with lists and booleans (#1538)",
    "narrow-blocks/src/test/scala/gezi/narrowblocks/NarrowBlockDebugAttributesSnapshotTest.scala" ->
      "the snapshot of those attributes"
  )

  private val locationProjects: Set[String] = Set("locations", "provenance")

  private val declarationPattern: Regex = """(?m)^lazy val `?([\w-]+)`?\s*=""".r

  private val dependsOnPattern: Regex = """(?s)dependsOn\((.*?)\)""".r

  private val stringPattern: Regex = """"[^"]*"""".r

  private val dependencyPattern: Regex = """`([\w-]+)`|(?<![\w-])([A-Za-z]\w*)(?![\w-])""".r

  private val packageReferencePattern: Regex = """\bgezi\.(locations|provenance)\b""".r

  test("only the projects that carry locations depend on locations or provenance, in the build") {
    val build = ScalaSources.commentsBlanked(Files.readString(ScalaSources.root.resolve("build.sbt")))
    val declarations = declarationPattern.findAllMatchIn(build).toVector
    val blocks = declarations.zip(declarations.drop(1).map(_.start) :+ build.length).map((declaration, end) =>
      declaration.group(1) -> build.substring(declaration.end, end)
    )
    assert(locationProjects.subsetOf(blocks.map(_._1).toSet), "the build declares locations and provenance")
    val found = blocks.filterNot((name, _) => allowed.contains(name)).flatMap((name, block) =>
      dependsOnPattern
        .findAllMatchIn(block)
        .flatMap(arguments => dependencyPattern.findAllMatchIn(stringPattern.replaceAllIn(arguments.group(1), "")))
        .map(dependency => Option(dependency.group(1)).getOrElse(dependency.group(2)))
        .filter(locationProjects.contains)
        .map(dependency => s"$name depends on $dependency")
    )
    assertEquals(found, Vector.empty)
  }

  test("only the projects that carry locations name their packages, in the sources") {
    val root = ScalaSources.root
    val sources = ScalaSources
      .sources(root)
      .filterNot(path => allowed.exists(project => path.startsWith(root.resolve(project))))
      .filterNot(path => allowedSources.contains(root.relativize(path).toString))
    assert(sources.nonEmpty, s"no Scala source found outside the allowed projects of $root")
    val found = sources.flatMap(path =>
      packageReferencePattern
        .findAllMatchIn(ScalaSources.commentsBlanked(Files.readString(path)))
        .map(_.group(1))
        .distinct
        .map(segment => s"${root.relativize(path)}: gezi.$segment")
    )
    assertEquals(found, Vector.empty)
  }
