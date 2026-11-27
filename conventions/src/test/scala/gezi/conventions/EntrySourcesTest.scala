package gezi.conventions

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** No file of a contest entry or of a reusable module, under a directory
  * `contest-entries-<name>` or `contest-modules-<name>` (its sources, resources
  * and `build.sbt`), names the packages of the problem corpora or of the judge,
  * or the project `contest-corpora`: an entry uses the framework's and the
  * baseline's public API only. Its purpose is to catch an entry that imports a
  * problem generator, a reference or the judge, or names one for reflection in
  * a literal, or a `build.sbt` that adds `contest-corpora` to its dependencies.
  * A name built at run time escapes it; the judge's `EntryClasspathTest` checks
  * that an entry's JVM cannot load those classes at all. A module may register
  * the services of the interfaces it implements, such as an executor module
  * (`gezi.contest.entry.ExecutorModule`), but no `EntryProvider`, which would
  * put a second provider in the JVM of every entry, all of which depend on it,
  * and no `NativesProvider`, which a natives project registers.
  */
class EntrySourcesTest extends gezi.generatedinputs.FailFastSuite:

  private val forbidden: Vector[String] =
    Vector("gezi.contest.corpora", "gezi.contest.judge", "contest-corpora")

  private def directories(root: Path, prefix: String): Vector[Path] =
    Using.resource(Files.list(root))(paths =>
      paths.toList.asScala.toVector.filter(path =>
        Files.isDirectory(path) && path.getFileName.toString.startsWith(prefix)
      )
    )

  private def filesUnder(root: Path, prefix: String): Vector[Path] =
    directories(root, prefix).flatMap(directory =>
      Using.resource(Files.walk(directory))(paths =>
        paths.toList.asScala.toVector.filter(path =>
          Files.isRegularFile(path) && !root
            .relativize(path)
            .toString
            .split('/')
            .contains("target")
        )
      )
    )

  test(
    "no file under contest-entries-* or contest-modules-* names the problem corpora or the judge"
  ) {
    val root = ScalaSources.root
    val entryFiles = filesUnder(root, "contest-entries-")
    val files = entryFiles ++ filesUnder(root, "contest-modules-")
    assert(
      entryFiles.exists(_.toString.endsWith(".scala")),
      s"no Scala source found under $root/contest-entries-*"
    )
    val found = files.flatMap(file =>
      val text = Files.readString(file)
      forbidden
        .filter(text.contains)
        .map(name => s"${root.relativize(file)}: $name")
    )
    assertEquals(found, Vector.empty)
  }

  /** The services no module registers: an entry's provider and a natives
    * project's natives.
    */
  private val servicesNoModuleRegisters: Vector[String] =
    Vector("gezi.contest.entry.EntryProvider", "gezi.jit.NativesProvider")

  test(
    "no file under contest-modules-* registers an entry provider or natives"
  ) {
    val root = ScalaSources.root
    val registrations = filesUnder(root, "contest-modules-").filter(path =>
      path.toString.contains("META-INF/services") && servicesNoModuleRegisters
        .contains(path.getFileName.toString)
    )
    assertEquals(registrations.map(root.relativize(_).toString), Vector.empty)
  }
