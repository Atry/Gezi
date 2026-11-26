package gezi.contest.judge

import java.net.URL
import gezi.ir.Configured
import gezi.ir.NoFacts
import java.nio.file.Files
import java.nio.file.Path
import java.util.Collections
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.Interaction
import gezi.contest.runner.EntryRunner
import gezi.frontend.DeBruijnTerm
import gezi.hotspot.Cache
import gezi.saturation.StopSignal

/** A provider registered in this test's services file only. */
final class FirstTestProvider extends EntryProvider:
  def initial(entryDirectory: Path, cache: Cache, articles: ArticleDestination): Entry[?] = NoAnswerEntry(cache)

/** Another provider registered in this test's services file only. */
final class SecondTestProvider extends EntryProvider:
  def initial(entryDirectory: Path, cache: Cache, articles: ArticleDestination): Entry[?] = NoAnswerEntry(cache)

/** An entry that answers nothing (it displays the Output unreduced),
  * holding the judge's cache service.
  */
final case class NoAnswerEntry(cache: Cache) extends Entry[NoFacts.type]:
  def run(cell: gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[NoFacts.type] =
    Interaction.Finished(Cells.unreducedOutput(cell, Cells.initialState), Vector.empty, this)

/** The runner stops loudly when the loader registers no implementation of
  * `EntryProvider` or more than one (`EntryRunner.provider`): it throws,
  * naming how many it found. Its purpose is to catch a runner that picks
  * one of several providers, or runs with none. The loader is built in this
  * JVM, on a services directory that registers none or the two providers
  * above; no entry's JVM is started, since what is checked is the lookup.
  */
class ProviderRegistrationTest extends gezi.generatedinputs.FailFastSuite:

  /** A loader that loads the test's classes through its parent and whose
    * resources are the directory's files only: `getResources` answers the
    * file of that name under the directory, if any, and never its parent's,
    * so a provider on the test classpath is not counted.
    */
  private def servicesOnly(directory: Path): ClassLoader =
    new ClassLoader(getClass.getClassLoader):
      override def getResources(name: String): java.util.Enumeration[URL] =
        val file = directory.resolve(name)
        Collections.enumeration(if Files.exists(file) then java.util.List.of(file.toUri.toURL) else java.util.List.of[URL]())

  private def registered(providers: Vector[Class[? <: EntryProvider]]): Path =
    val services = Files.createTempDirectory("judge-services")
    Files.createDirectories(services.resolve("META-INF/services"))
    Files.writeString(
      services.resolve(s"META-INF/services/${classOf[EntryProvider].getName}"),
      providers.map(_.getName + "\n").mkString
    )
    services

  test("no registered provider stops the runner") {
    val failure = intercept[IllegalStateException](EntryRunner.provider(servicesOnly(registered(Vector.empty))))
    assert(failure.getMessage.contains("must be registered, found 0"), failure.getMessage)
  }

  test("two registered providers stop the runner") {
    val failure = intercept[IllegalStateException](
      EntryRunner.provider(servicesOnly(registered(Vector(classOf[FirstTestProvider], classOf[SecondTestProvider]))))
    )
    assert(failure.getMessage.contains("must be registered, found 2"), failure.getMessage)
  }
