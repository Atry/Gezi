package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExecutorOption
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.Interaction
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExpansionSource
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import scala.util.Random

/** The laws of where an entry's program is compiled
  * (`CompilationPlaceOption`, https://github.com/Atry/private-overlay/issues/1549,
  * https://github.com/Atry/private-overlay/issues/1827), on solo's entry,
  * whose lemma rounds compile the hot ladder's iterated sites to narrow
  * blocks, read with the executor of `ProgramRecordingModule`, and generated
  * hot sites of one iterated call (`HotSites.site`). The test pins solo's
  * execution options, its executor and its compilation place, so that the
  * laws hold of the framework's route whatever solo's data chooses. Under
  * `upfront` the executor receives the program the rounds give
  * (`ProgramCompiler.compiledProgram`), as before the option; under
  * `by_executor` it receives the program uncompiled; under both it is handed
  * the entry's prepared compilation, and the two entries' compilations are
  * equal. The rounds rewrite every drawn site, so that the two places are
  * told apart by what the executor receives. Its purpose is to catch an
  * entry that runs its rounds under `by_executor` or skips them under
  * `upfront`, and a module handed another compilation than the entry's, or
  * one that depends on the option.
  */
class CompilationPlaceLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  private val entryDirectory = buildRoot.resolve("contest-entries-solo")

  /** The table of the one module of these tests, its selector read off the
    * tree whose visible subtree is Gezi's directory.
    */
  private lazy val modules: ExecutorModules = ExecutorModules.registered(buildRoot, Vector(ProgramRecordingModule()))

  /** The natives both entries are built over, loaded once, so that their
    * compilations compare the natives as one value.
    */
  private lazy val natives = NativesProvider.loaded

  /** The cache service both entries are built with, so that the second
    * entry's reading of the knowledge answers from the tables the first one
    * kept: built with a cache service each, the two entries took the shared
    * fixtures past their 15 s deadline on two cores at a load of about 7
    * (main 9d04c1b6c, 2026-11-21).
    */
  private lazy val caches = Defaults.caches()

  /** solo's entry, read as the judge's entry reads it, with its execution
    * options pinned: the test module as its executor and the compilation's
    * place given, whatever solo's data writes.
    */
  private def entryAt(place: CompilationPlaceOption): GenericEntry =
    val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
    val Vector(selector) = (modules.bySelector.keys.toVector: @unchecked)
    GenericEntryProvider.initialized(
      data.copy(
        executor = ExecutorOption.Module(selector, Defunctionalization.thunkInstruction(Lambdalattice.term("λx. x"))),
        compilationPlace = place
      ),
      modules,
      ExtractorModules.registeredFor(entryDirectory),
      natives,
      ArticleDestination.Discarded,
      afterEntry,
      caches
    )

  private lazy val upfront: GenericEntry = entryAt(CompilationPlaceOption.Upfront)

  private lazy val byExecutor: GenericEntry = entryAt(CompilationPlaceOption.ByExecutor)

  private lazy val hotSites: HotSites = HotSites.read(buildRoot)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => modules, _ => natives, _ => caches, _ => upfront, _ => byExecutor, _ => hotSites)

  /** The compilation the entry's executor was handed and the programs it was given, after the entry ran the cell
    * of the point.
    */
  private def received(entry: GenericEntry, point: DeBruijnTerm, stop: StopSignal): ProgramRecordingExecutor =
    entry.run(Cells.cell(point), ExpansionSource.fresh(), stop) match
      case Interaction.Finished(_, _, after: GenericEntry) =>
        after.executor match
          case recording: ProgramRecordingExecutor => recording
          case other                               => throw AssertionError(s"the entry's executor is $other")
      case other => throw AssertionError(s"the entry's cell ended as $other")

  /** Its purpose is to catch a place given in the entry's data that does not reach the entry. */
  test("the place given reaches the entry") {
    assertEquals((upfront.compilationPlace, byExecutor.compilationPlace), (CompilationPlaceOption.Upfront, CompilationPlaceOption.ByExecutor))
  }

  // One input: each input runs solo's rounds twice and reads the site twice, and the laws hold of any site, so a run
  // checks them on one drawn site and successive runs draw others. Five inputs overran the 3 s deadline on main
  // eece45790 at a load of about 7 on two cores (2026-11-21, twice), and two did on 9d04c1b6c (3.013 s).
  stoppableProperty(
    "the executor receives the compiled program upfront, the uncompiled one by_executor, and the entry's compilation",
    _.copy(testLimit = hedgehog.core.SuccessCount(1))
  ) { stopped =>
    for
      seed <- Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue)).forAll
      bits <- Gen.int(Range.linear(2, 5)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      // The site is written once: its draws happen inside the bodies of `λ` (`HotSites`).
      val point = hotSites.site(Random(seed), 1, bits).locallyNamelessTerm
      val program = Defunctionalization.thunkInstruction(point)
      val (compiled, _) = ProgramCompiler.compiledProgram(upfront.compilation, program, explained = false, stop)
      val beforeTheRounds = received(byExecutor, point, stop)
      val afterTheRounds = received(upfront, point, stop)
      Result
        .all(
          List(
            Result.diff(afterTheRounds.received, Vector(compiled))(_ == _).log("upfront: the programs received and the rounds' program"),
            Result.diff(beforeTheRounds.received, Vector(program))(_ == _).log("by_executor: the programs received and the program"),
            Result.diff(afterTheRounds.compilation, upfront.compilation)(_ == _).log("upfront: the compilation handed and the entry's"),
            Result.diff(beforeTheRounds.compilation, byExecutor.compilation)(_ == _).log("by_executor: the compilation handed and the entry's"),
            Result.diff(byExecutor.compilation, upfront.compilation)(_ == _).log("the two entries' compilations"),
            Result.assert(compiled != program).log("the rounds left the program as it was")
          )
        )
        .log(s"a site of one iterated call of $bits binary digits, drawn from the seed $seed")
  }
