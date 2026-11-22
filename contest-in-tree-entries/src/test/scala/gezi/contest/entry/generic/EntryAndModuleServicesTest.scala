package gezi.contest.entry.generic

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The law that every service an entry's or a module's project registers in
  * its `src/main/resources/META-INF/services` is found by
  * `java.util.ServiceLoader` on this project's test classpath: an executor
  * module's and an extractor module's (`ExecutorModules.loaded`,
  * `ExtractorModules.loaded`) as much as an entry's provider. The projects
  * are those the build derives this project's dependencies from
  * (project/EntryProjects.scala, `gezi.entryAndModuleProjects`). Its purpose
  * is to catch a classpath that leaves a module out, on which
  * `InTreeEntriesTest` would refuse an entry that selects it as the selector
  * of no registered module, though the entry reads in the judge's JVM.
  */
class EntryAndModuleServicesTest extends gezi.generatedinputs.FailFastSuite:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private val projects: Vector[String] =
    sys.props("gezi.entryAndModuleProjects").split(',').toVector.filter(_.nonEmpty)

  /** The files of the directory, sorted, none when it does not exist. */
  private def filesIn(directory: Path): Vector[Path] =
    if Files.isDirectory(directory) then
      Using.resource(Files.list(directory))(_.toList.asScala.toVector.filter(Files.isRegularFile(_)).sortBy(_.toString))
    else Vector.empty

  /** The provider classes a registration file lists, its comments and blank
    * lines left out.
    */
  private def providers(registration: Path): Vector[String] =
    Files.readAllLines(registration).asScala.toVector.map(_.takeWhile(_ != '#').trim).filter(_.nonEmpty)

  /** Each registration of the project: the service, the provider and the
    * file that lists it.
    */
  private def registrations(project: String): Vector[(String, String, Path)] =
    filesIn(buildRoot.resolve(project).resolve("src/main/resources/META-INF/services")).flatMap(registration =>
      providers(registration).map(provider => (registration.getFileName.toString, provider, registration))
    )

  /** The names of the providers `java.util.ServiceLoader` finds for the
    * service on this classpath.
    */
  private def loadedProviders(service: String): Set[String] =
    java.util.ServiceLoader
      .load(Class.forName(service))
      .stream()
      .toList
      .asScala
      .toVector
      .map(_.`type`.getName)
      .toSet

  test("every service an entry's or a module's project registers is loaded on this classpath") {
    assert(projects.exists(_.startsWith("contest-entries-")), s"no entry's project in gezi.entryAndModuleProjects: $projects")
    val missing = projects.flatMap(registrations).filterNot((service, provider, _) => loadedProviders(service).contains(provider)).map(
      (service, provider, registration) => s"${buildRoot.relativize(registration)}: $provider is not loaded as a $service"
    )
    assertEquals(missing, Vector.empty)
  }
