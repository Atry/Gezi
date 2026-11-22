import java.nio.file.Files
import java.nio.file.Path
import sbt.*
import sbt.Keys.*
import sbt.internal.inc.AnalyzingCompiler
import sbt.internal.inc.LoggedReporter
import scala.jdk.OptionConverters.*

/** The check that every Scaladoc link (`[[...]]`) of a project's main sources
  * resolves: `docLinks` runs scaladoc over the project's TASTy files, as
  * `Compile / doc` does, and fails on every unresolved link it reports, each
  * named by its file and line and by the query. The line is the one scaladoc
  * reports, that of the definition the comment documents (Scala 3.10.0 keeps
  * no position of a link inside its comment), so the query says which link
  * of the comment it is.
  *
  * Scaladoc reports an unresolved link as a warning and offers no option that
  * makes it an error: `-Werror` and `-Wconf` reach scaladoc's options but not
  * the compiler context it reports into (Scala 3.10.0's
  * `dotty.tools.scaladoc.Scaladoc.extract` copies only the common settings
  * there and prints `Skipping unused scalacOptions: -Werror, -Wconf` under
  * `-warn-on-unused-options`), and the warning is reported with no compiler
  * run, whose end is where `-Werror` turns warnings into an error. So the
  * task calls zinc's `AnalyzingCompiler.doc` with a reporter of its own and
  * reads the problems it recorded.
  *
  * A problem is an unresolved link when its message is scaladoc's for one:
  * "Couldn't resolve a member for the given link query", "Unable to find a
  * link" or "Unable to parse query". Only a problem whose source lies under
  * the build's root counts: scaladoc also reports the links of documentation
  * a class inherits from a dependency (almond's `Interpreter`, inherited by
  * `jupyter-kernel`), whose sources are the dependency's, which this build
  * cannot fix. The documentation is written to a scratch directory under the
  * project's target, never to `Compile / doc`'s.
  *
  * `docLinks` is defined in every project, so at the root it runs in every
  * project the root aggregates. A project with no TASTy file has nothing to
  * check.
  */
object DocumentationLinks extends AutoPlugin {

  object autoImport {
    val docLinks = taskKey[Unit]("Runs scaladoc on the main sources and fails on every unresolved link.")
  }

  import autoImport.*

  override def trigger = allRequirements

  override def requires = plugins.JvmPlugin

  private val unresolvedLinkMessages: Seq[String] = Seq(
    "Couldn't resolve a member for the given link query",
    "Unable to find a link",
    "Unable to parse query"
  )

  /** The file and line of the problem, the file relative to the root, when
    * its source lies under the root.
    */
  private def locationUnder(root: Path, problem: xsbti.Problem): Option[String] = {
    val position = problem.position
    position.sourcePath.toScala.map(path => root.resolve(path).normalize).filter(source =>
      source.startsWith(root) && Files.isRegularFile(source)
    ).map(source =>
      s"${root.relativize(source)}:${position.line.toScala.fold("?")(_.toString)}"
    )
  }

  override def projectSettings: Seq[Setting[?]] = Seq(
    docLinks := Def.uncached {
      val log = streams.value.log
      val documentedTastyFiles = (Compile / doc / tastyFiles).value
      val documentationClasspath = (Compile / doc / dependencyClasspath).value
      val documentationOptions = (Compile / doc / scalacOptions).value
      val converter = fileConverter.value
      val scalaCompiler = (Compile / doc / compilers).value.scalac
      val output = (Compile / target).value.toPath.resolve("doc-links")
      val root = (LocalRootProject / baseDirectory).value.toPath.toAbsolutePath.normalize
      val project = thisProject.value.id
      if (documentedTastyFiles.nonEmpty) {
        val analyzingCompiler = scalaCompiler match {
          case analyzing: AnalyzingCompiler => analyzing
          case other =>
            throw new MessageOnlyException(s"$project: the Scala compiler is ${other.getClass}, not zinc's AnalyzingCompiler")
        }
        // Zinc's reporter records the problems it is given; it is the
        // library's object, read once after the call.
        val reporter = new LoggedReporter(Int.MaxValue, log, identity)
        // Scaladoc's `-d` must name a directory that exists; scaladoc empties it.
        Files.createDirectories(output)
        analyzingCompiler.doc(
          documentedTastyFiles.map(file => converter.toVirtualFile(file.toPath)),
          documentationClasspath.map(entry => converter.toVirtualFile(converter.toPath(entry.data))),
          converter,
          output,
          documentationOptions,
          log,
          reporter
        )
        val unresolved = reporter.problems.toVector
          .filter(problem => unresolvedLinkMessages.exists(problem.message.contains))
          .flatMap(problem =>
            locationUnder(root, problem).map(location =>
              s"$location: ${problem.message.split('\n').toVector.map(_.trim).filter(_.nonEmpty).mkString(" ")}"
            )
          )
          .distinct
        if (unresolved.nonEmpty)
          throw new MessageOnlyException(
            s"$project: ${unresolved.size} unresolved Scaladoc links:\n" + unresolved.mkString("\n")
          )
      }
    }
  )
}
