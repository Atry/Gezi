package gezi.contest.entry.generic

import java.nio.file.Paths
import gezi.contest.entry.Defaults
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.UnitSelectionOption
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorOption
import gezi.contest.entry.Interaction
import gezi.contest.entry.OutputDisplay
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.contest.entry.Phase
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.TermOf
import gezi.jit.NativesProvider
import gezi.saturation.StopSignal
import scala.util.Random

/** The law of the judge's cancel (`gezi.contest.runner.PipeLines`, the line
  * `cancel`) through the generic entry's whole route: a cell whose signal asks
  * for a stop after a short delay returns within the judge's grace of 2
  * seconds after it, on generated programs of many hot sites, whose lemma
  * round saturates for long, on a generated hot site whose compiled narrow
  * block's recursion runs far beyond any budget, and on generated nested
  * hot sites written η-expanded, run far beyond any budget (stopped after
  * 3 s). A nested site compiles to a narrow block since the unpriced
  * reading (4e59a1471): on main a1b899b86 every thread dump of this case,
  * taken every two minutes from 4 to 16 minutes into it, was inside a
  * generated block's recursion under `LemmaRoute.blocksComputed`, and the
  * case timed out after 1310 s with the block reading no signal
  * (2026-11-14). The general reading's late regime, about a minute in with
  * about 600 MB live, is beyond the tests' heap of 256 MB; its return times
  * are measured on the points, in the pull request that added the
  * trampoline's check. And
  * after such a cancel, the entry the cell
  * returns reads generated small programs to the outputs a fresh entry
  * reads. Purpose: catch a phase that does not read the signal (a lemma
  * round's saturation; a compiled narrow block's run; the general reading's work that no budget charges,
  * or its unwinding after the stop, measured on 2026-11-07 at 11 to 19 s
  * after the stop on the hot ladder's nested points), which would have the judge
  * kill the entry's JVM and cost the next family a cold start; and catch a
  * cancelled reading that leaves the JIT state it hands on marking an
  * instance as being read, which would make a later reading take a wrong
  * cycle exit.
  */
class CancelGraceLawTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CancelGraceLawTest, "a hot site whose block runs far too long returns within the grace of the cancel", takes 12.423 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The one version of the tree's contents every cell is run under: no file changes while the suite runs. */
  private val source: gezi.hotspot.ExpansionSource = gezi.hotspot.ExpansionSource.fresh()

  /** The in-tree entry `contest-entries-solo`, read as the judge's entry reads it
    * (`EntryData.read`, then `GenericEntryProvider.initialized`): its
    * knowledge types the iterated loops of binary naturals and compiles
    * them to narrow blocks. Its execution options are pinned to the
    * framework's executor and `upfront`, so that the law holds of the
    * framework's route whatever executor and compilation place the entry's data
    * chooses (`ExecutorOption`, `CompilationPlaceOption`).
    */
  private lazy val entry: GenericEntry[?] =
    val (read, afterEntry) = EntryData.read(buildRoot.resolve("contest-entries-solo"), Defaults.entryDataState)
    val data = read.copy(executor = ExecutorOption.Jit, compilationPlace = CompilationPlaceOption.Upfront(UnitSelectionOption.WholeProgram))
    GenericEntryProvider.initialized(data, gezi.contest.entry.ExecutorModules.registeredFor(buildRoot.resolve("contest-entries-solo")), gezi.contest.entry.ExtractorModules.registeredFor(buildRoot.resolve("contest-entries-solo")), NativesProvider.loaded, ArticleDestination.Discarded, afterEntry, gezi.contest.entry.Defaults.caches())

  /** The entry with the generated hot sites over the library terms of `TermTables.hotSiteTerms`, crossed into its
    * configuration.
    */
  private lazy val opened: Opened[?] = Opened.of(entry, HotSites.read(buildRoot))

  /** The library terms and the entry, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => opened)

  /** The judge's grace, in nanoseconds. */
  private val grace = 2_000_000_000L

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the specialized spelling makes a program's
  // typed constants storages at construction (a binary natural's, a list's), and the narrow blocks do not yet take
  // storages (#2238, "块入口直接收到存储"): a constant storage is of no narrow kind and does not decode as a literal, so
  // no block is compiled.
  stoppableTest("a hot site whose block runs far too long returns within the grace of the cancel".fail) { stopped =>
    opened.blockRunWithinGrace(StopSignal.completedWith(stopped))
  }

  test("a program of many sites whose lemma round saturates for long returns within the grace of the cancel") {
    opened.roundsWithinGrace()
  }

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the facts' native specializer converts more than
  // the e-graph converts when it adds a node, so the write-back's spelling of an opened body (`LocalExtraction`, built
  // through the graph's construction) names, for two classes the graph has not united, one term, found in the other
  // class ("the spelling of a body has no node in the graph"); #2238 makes every construction point read one decision,
  // so that a term has one object.
  test("a nested hot site run far beyond any budget returns within the grace of the cancel".fail) {
    opened.nestedWithinGrace()
  }

  // KNOWN FAILURE until https://github.com/Atry/private-overlay/issues/2238: the facts' native specializer converts more than
  // the e-graph converts when it adds a node, so the write-back's spelling of an opened body (`LocalExtraction`, built
  // through the graph's construction) names, for two classes the graph has not united, one term, found in the other
  // class ("the spelling of a body has no node in the graph"); #2238 makes every construction point read one decision,
  // so that a term has one object.
  stoppableTest("after a cancelled reading the entry reads generated small programs as a fresh entry does".fail) { stopped =>
    opened.readsAsFresh(StopSignal.completedWith(stopped))
  }

  /** The entry and the hot sites in the entry's configuration `C`, with the laws' bodies. */
  private final case class Opened[C <: NativeSpecializer & Singleton](entry: Entry[C], hotSites: HotSites[C]):

    /** The nanoseconds from the signal's stop to the cell's return, the
      * signal stopping `delay` nanoseconds after the cell starts. The entry is
      * built and the point written before the clock starts, so that the
      * library's compilation is not charged to the cell.
      */
    private def returnedAfterTheStop(program: TermOf[Configured[C]], delay: Long): Long = cancelled(program, delay)._1

    /** `returnedAfterTheStop`, and the entry the cell returned. */
    private def cancelled(program: TermOf[Configured[C]], delay: Long): (Long, Entry[C]) =
      val point = program.locallyNamelessTerm
      val start = System.nanoTime
      val stop = new StopSignal:
        def stopRequested: Boolean = System.nanoTime - start > delay
      entry.run(Cells.cell(point), source, stop) match
        case Interaction.Finished(_, _, returned) => (System.nanoTime - start - delay, returned)

    /** The display of the output the entry gives for the point, never
      * stopped.
      */
    private def output(from: Entry[C], point: DeBruijnTermOf[Configured[C]], stop: StopSignal): OutputDisplay[C] =
      from.run(Cells.cell(point), source, stop) match
        case Interaction.Finished(output, _, _) => output

    def blockRunWithinGrace(stop: StopSignal): Unit =
      val random = Random(20261107)
      // The shape compiles to a block: read never stopped at small counts, the
      // site runs one, so the cases below test a block's run, not a reading
      // that compiled none.
      val small = hotSites.site(random, 1, 8).locallyNamelessTerm
      entry.run(Cells.cell(small), source, stop) match
        case Interaction.Finished(_, phases, _) =>
          assert(phases.exists { case Phase(name, _) => name == "block_run"; case _ => false }, s"no block ran: $phases")
      (1 to 3).foreach { _ =>
        val after = returnedAfterTheStop(hotSites.site(random, 1, 48 + random.nextInt(16)), 500_000_000L)
        assert(after < grace, s"returned ${after / 1e9} s after the stop")
      }

    def roundsWithinGrace(): Unit =
      val random = Random(20261108)
      (1 to 2).foreach { _ =>
        val after = returnedAfterTheStop(hotSites.site(random, 150 + random.nextInt(100), 12), 300_000_000L)
        assert(after < grace, s"returned ${after / 1e9} s after the stop")
      }

    def nestedWithinGrace(): Unit =
      val random = Random(20261109)
      (1 to 3).foreach { _ =>
        val after = returnedAfterTheStop(hotSites.nested(random, 16 + random.nextInt(4)), 3_000_000_000L)
        assert(after < grace, s"returned ${after / 1e9} s after the stop")
      }

    def readsAsFresh(stop: StopSignal): Unit =
      val random = Random(20261110)
      val (_, after) = cancelled(hotSites.nested(random, 18), 2_000_000_000L)
      (1 to 6).foreach { index =>
        // The point is written once: the generators draw inside the bodies of
        // `λ`, which run again each time a term is written.
        val point = (if index % 2 == 0 then hotSites.nested(random, 2) else hotSites.site(random, 1, 3)).locallyNamelessTerm
        assertEquals(output(after, point, stop), output(entry, point, stop), s"program $index")
      }

  private object Opened:

    /** The entry opened in its configuration, the sites crossed into it. */
    def of[C <: NativeSpecializer & Singleton](entry: GenericEntry[C], sites: HotSites[NoFacts.type]): Opened[C] =
      Opened(entry, HotSites.crossed(sites, entry.specializer))
