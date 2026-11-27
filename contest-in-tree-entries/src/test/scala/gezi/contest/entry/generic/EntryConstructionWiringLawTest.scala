package gezi.contest.entry.generic

import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.jit.NativesProvider
import scala.util.Random

/** The law that each round's constant storage stop reaches its saturation,
  * and every round builds with the JIT's construction, through
  * `GenericEntryProvider`. For each of wren, solo and plover, the entry's
  * data with each round's stop set to generated values, negated in the
  * second setting, are set up. Derived before the run from
  * `Defaults.lemmaCompilation` and `GenericEntry[?]`: every prepared round's
  * construction is the JIT's facts' (`ConvertedTermConstruction` of the
  * entry's facts and capability), so that the rounds and the JIT intern one object for one
  * term; each round's stop is the one written. Its purpose is to catch the
  * rounds taking another construction than the JIT, or a round's stop lost
  * on the way to its saturation.
  */
class EntryConstructionWiringLawTest extends gezi.generatedinputs.FailFastSuite:

  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(240, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  Vector("contest-entries-wren", "contest-entries-solo", "contest-entries-plover").foreach(directory =>
    test(s"$directory's rounds build as its JIT does, each with its own stop") {
      val entryDirectory = buildRoot.resolve(directory)
      val (read, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
      val random = Random(20261145 + directory.length)
      val drawn = read.rounds.map(_ => random.nextBoolean())
      (1 to 2).foreach { position =>
        // The second setting negates the first's stops, so that every round's stop is read both ways.
        val stops = if position == 1 then drawn else drawn.map(!_)
        val data = read.copy(
          rounds = read.rounds.zip(stops).map((round, stopped) => round.copy(settings = round.settings.copy(constantStorageStop = stopped)))
        )
        val (_, entry) = GenericEntryProvider.initializedWithLibrary(
          data,
          gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
          gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
          NativesProvider.loaded,
          ArticleDestination.Discarded,
          afterEntry,
          Defaults.caches()
        )
        wiredAlike(entry, stops, s"$directory, setting $position: stops $stops")
      }
    }
  )

  /** Each round's construction is the entry's own, `ConvertedTermConstruction` of the JIT's encoding, the facts the
    * JIT holds (an entry may set its JIT up with natives of its own), with the round's constant storage stop.
    */
  private def wiredAlike[C <: gezi.ir.NativeSpecializer & Singleton](entry: GenericEntry[C], stops: Vector[Boolean], clue: String): Unit =
    val expected = gezi.jit.ConvertedTermConstruction[C](entry.jit.configuration.specializer)(entry.jit.configuration.storageAccess)
    val rounds = entry.rounds.map(round => round.saturator.options.construction -> round.saturator.options.constantStorageStop)
    assertEquals(rounds, stops.map(stopped => expected -> stopped), clue)
