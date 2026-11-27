package gezi.contest.entry.generic

import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.jit.NativesProvider
import gezi.jit.UniqueSpellingPremiseCheck

/** The unique spelling's premise (proofs, section 23) on each in-tree entry's
  * facts, by jit's test checker (`UniqueSpellingPremiseCheck`): every
  * constructor of every representation the entry's facts store and of every
  * declared family its knowledge declares is shown a member of its criterion's
  * unfolding, and the families of a finite value parameter agree with the
  * backend's facts. The premise is the backend's obligation, which no run
  * checks, so a family an entry declares is covered here, by running the one
  * checker over every in-tree entry, a new entry included without anyone
  * writing its own test. Its purpose is to catch an entry's knowledge whose
  * declared constructor or field criteria are not its criterion's own, which
  * the readers of its storages would read wrongly.
  */
class EntriesPremiseTest extends gezi.generatedinputs.FailFastSuite:
  // An entry's setup reads its knowledge and prepares its rounds (InTreeEntriesTest: up to 20 s on two loaded cores).
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(35, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private val inTreeEntries = Vector(
    "contest-entries-fixture",
    "contest-entries-plover",
    "contest-entries-solo",
    "contest-entries-wren"
  )

  inTreeEntries.foreach(directory =>
    test(
      s"$directory's facts show the unique spelling's premise for every constructor they store or declare"
    ) {
      val entryDirectory = buildRoot.resolve(directory)
      val (data, afterEntry) =
        EntryData.read(entryDirectory, Defaults.entryDataState)
      val entry = GenericEntryProvider.initialized(
        data,
        gezi.contest.entry.ExecutorModules.registeredFor(entryDirectory),
        gezi.contest.entry.ExtractorModules.registeredFor(entryDirectory),
        NativesProvider.loaded,
        ArticleDestination.Discarded,
        afterEntry,
        Defaults.caches()
      )
      val premise = UniqueSpellingPremiseCheck(entry.encoding)
      assertEquals(
        (
          premise.nonMembers,
          premise.declaredNonMembers,
          premise.parameterizedDisagreements
        ),
        (Vector.empty[String], Vector.empty[String], Vector.empty[String]),
        directory
      )
    }
  )
