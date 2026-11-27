import java.nio.file.Files
import java.nio.file.Path
import sbt.*
import sbt.Keys.*
import sbt.util.Digest
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The files the tests read at run time, from the build's root
  * (`-Dgezi.buildRoot`), declared as inputs of sbt 2's test cache.
  *
  * sbt 2 caches `test` by the test classpath, its resources and the test
  * options; a file a test opens by path at run time is none of these, so a
  * change of a library file under `corpora` alone would be answered from the
  * cache with the old result. The digest of every regular file under the
  * directories below, with its path, is added to `extraTestDigests` ("Extra
  * digests that would invalidate test caching"), so that a change of one of
  * them reruns the tests that depend on the build's root, with no need of
  * `testFull`. Every project gets it, so that a project's tests are rerun
  * whenever these files change; a project that reads none of them runs its
  * tests again too, which costs time and never an answer.
  */
object RuntimeTestInputs extends AutoPlugin:

  override def trigger: PluginTrigger = allRequirements

  /** The directories and files, relative to the build's root, that tests read
    * at run time. The Lean package is listed by its sources, not as `lean`,
    * whose `.lake` holds the build's output: the tests that run `lake` read the
    * package (measured 2026-11-10: with
    * `lean/LambdaJit/StatementNormalisation.lean` changed and the package not
    * listed, `proofs/test` answered its 6 suites from the cache).
    */
  private val tracked: Seq[String] = Seq(
    "corpora",
    "tests",
    "contest-entries-fixture/entry.lambdalattice",
    "contest-entries-solo/entry.lambdalattice",
    "contest-entries-wren/entry.lambdalattice",
    "lean/LambdaJit",
    "lean/LambdaJit.lean",
    "lean/lakefile.lean",
    "lean/lake-manifest.json",
    "lean/lean-toolchain"
  )

  /** The regular files under the path, sorted, the path itself when it is a
    * file.
    */
  private def files(path: Path): Seq[Path] =
    if Files.isRegularFile(path) then Seq(path)
    else if Files.isDirectory(path) then
      Using
        .resource(Files.walk(path))(
          _.toList.asScala.toVector.filter(Files.isRegularFile(_))
        )
        .sortBy(_.toString)
    else Seq.empty

  /** The digest of the files, each with its path from the root. */
  private def digest(root: Path, listed: Seq[Path]): Digest =
    Digest.sha256Hash(
      listed.map(file =>
        Digest.sha256Hash(
          root.relativize(file).toString.getBytes("UTF-8") ++ Files
            .readAllBytes(file)
        )
      )*
    )

  /** The Scala sources of every project, which the tests of `conventions` read
    * at run time (`ScalaSources.sources`): without them, a source that breaks a
    * convention would pass `conventions` from the cache, as a line of
    * `selection-elimination` did on 2026-11-09 (the word `while` in a message,
    * which `ImmutabilityTest` reads as a loop).
    */
  private def scalaSources(root: Path): Seq[Path] =
    Using
      .resource(Files.list(root))(_.toList.asScala.toVector)
      .sortBy(_.toString)
      .flatMap(project => files(project.resolve("src")))
      .filter(path =>
        val name = root.relativize(path).toString
        name.endsWith(".scala") && (name.contains("/src/main/scala/") || name
          .contains("/src/test/scala/"))
      )

  /** The Markdown files under the root, outside build outputs (`target`),
    * hidden directories and `node_modules`, which `conventions`'
    * `MarkdownLinksTest` reads at run time (`MarkdownLinks.markdownFiles`):
    * without them, a link broken by an edit of a Markdown file alone would pass
    * from the cache.
    */
  private def markdownFiles(directory: Path): Seq[Path] =
    Using
      .resource(Files.list(directory))(_.toList.asScala.toVector)
      .sortBy(_.toString)
      .flatMap(entry =>
        val name = entry.getFileName.toString
        if Files.isDirectory(entry) then
          if name == "target" || name == "node_modules" || name.startsWith(".")
          then Seq.empty
          else markdownFiles(entry)
        else if name.endsWith(".md") then Seq(entry)
        else Seq.empty
      )

  override def projectSettings: Seq[Setting[?]] = Seq(
    // Uncached: sbt 2 caches a task by its inputs, the settings it reads, and
    // the files read here are none of them, so a cached digest would stay
    // the same when they change (measured 2026-11-09: with the task cached,
    // a reference line changed by hand still passed contest-corpora from the
    // cache, all 191 suites cached).
    Test / extraTestDigests ++= Def.uncached {
      val root = (LocalRootProject / baseDirectory).value.toPath
      val runtimeData =
        digest(root, tracked.flatMap(relative => files(root.resolve(relative))))
      if name.value == "conventions" then
        Seq(
          runtimeData,
          digest(root, scalaSources(root)),
          digest(root, markdownFiles(root))
        )
      else Seq(runtimeData)
    }
  )
