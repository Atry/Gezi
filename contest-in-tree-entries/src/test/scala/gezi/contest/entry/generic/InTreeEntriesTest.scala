package gezi.contest.entry.generic

import java.nio.file.Paths
import gezi.contest.entry.Defaults
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.EntryData
import gezi.jit.BackendFacts
import gezi.jit.NativesProvider
import gezi.narrowblocks.NarrowBlockCompilation
import gezi.narrowblocks.NarrowBlocks
import gezi.narrowblocks.NarrowKind

/** The in-tree entries written as data, the framework's fixture
  * `contest-entries-fixture`, `contest-entries-solo` and
  * `contest-entries-wren`, read as the judge's entry reads them
  * (`GenericEntryProvider.initial`): each `entry.lambdalattice` read by
  * projection off the tree whose visible subtree is Gezi's
  * directory, its knowledge, one term, compiled with the natives' checks,
  * and each round's knowledge read as members of it. Its purpose is to
  * catch an in-tree entry file that no longer reads: an import that
  * reaches nothing, a round that chooses a knowledge file
  * the library does not, or a setting off the published lists.
  */
class InTreeEntriesTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of InTreeEntriesTest, "contest-entries-solo's entry reads and its rounds are prepared", takes 20.220 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(35, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private val inTreeEntries = Vector("contest-entries-fixture", "contest-entries-plover", "contest-entries-solo", "contest-entries-wren")

  inTreeEntries.foreach(directory =>
    test(s"$directory's entry reads and its rounds are prepared") {
      val entryDirectory = buildRoot.resolve(directory)
      val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
      val entry = GenericEntryProvider.initialized(data, gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory), gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory), NativesProvider.loaded, ArticleDestination.Discarded, afterEntry, gezi.contest.entry.Defaults.caches())
      assert(entry.rounds.nonEmpty, directory)
    }
  )

  /** The law that the narrow check reads a term the backend binds to a
    * native (`BackendFacts.bindings`) as that name (`NarrowBlocks.nameKind`),
    * not through its layers, on each in-tree entry's library, at least one
    * of the terms a native. Its purpose is to catch a narrow check whose
    * names leave the bound terms out, so that no narrow block calls a
    * native and every native call falls back to the JIT.
    */
  inTreeEntries.foreach(directory =>
    test(s"$directory's narrow check reads every term bound to a native as its name") {
      val entryDirectory = buildRoot.resolve(directory)
      val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
      val entry = GenericEntryProvider.initialized(data, gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory), gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory), NativesProvider.loaded, ArticleDestination.Discarded, afterEntry, gezi.contest.entry.Defaults.caches())
      val bound = BackendFacts.bindings(entry.index, entry.natives).map(_.instruction).distinct
      val check = NarrowBlockCompilation(entry.index, entry.natives)
      val read = bound.map(term => (term, check.kinds(Vector(term))(term), NarrowBlocks.nameKind(term, entry.index, entry.natives)))
      assert(
        read.exists {
          case (_, NarrowKind.Native(_, _, _), _) => true
          case _                                  => false
        },
        s"$directory binds no term the narrow check reads as a native"
      )
      read.foreach((term, kind, named) => assertEquals(kind, named, s"$directory: $term"))
    }
  )
