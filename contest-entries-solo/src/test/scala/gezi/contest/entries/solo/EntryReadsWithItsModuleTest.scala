package gezi.contest.entries.solo

import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.contest.modules.solo.InterpretFirst
import gezi.contest.modules.solo.TieredExecutor
import gezi.jit.NativesProvider

/** The entry `contest-entries-solo` read as the judge's entry reads it
  * (`GenericEntryProvider.initialized`), with the executor modules registered
  * on this project's class path, which holds every module's, as the judge's
  * entry JVM does. Its purpose is to catch an entry file that no longer
  * reads with the module it selects: a selector that is no registered
  * module's, parameters the module refuses, or an executor other than the entry's
  * tiered one. The framework's InTreeEntriesTest reads the in-tree entries
  * in a project whose class path holds no module, so it cannot read an
  * entry that selects one.
  */
class EntryReadsWithItsModuleTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-21 on 4 CPUs (contest.slice, CPUs 0 to 3, nice 10), the 1-minute load about 5: 10.9 s, the entry's
  // knowledge and rounds compiled once. The bound is InTreeEntriesTest's for the same reading, whose 20.2 s it measured on
  // 2 CPUs under a load of 9 to 22 (its own comment, 2026-11-16).
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(35, "s")

  test("solo's entry reads, its rounds are prepared, and its executor is the tiered one interpreting first") {
    val entryDirectory = Paths.get(sys.props("gezi.buildRoot")).resolve("contest-entries-solo")
    val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(
      data,
      ExecutorModules.registeredFor(entryDirectory),
      ExtractorModules.registeredFor(entryDirectory),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    assert(entry.rounds.nonEmpty)
    entry.executor match
      case TieredExecutor(_, _, InterpretFirst(_, steps)) => assert(steps > 0, s"the interpretation's steps are $steps")
      case other                                         => fail(s"solo's entry reads with the executor $other")
  }
