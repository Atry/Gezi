package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.UnitSelectionOption
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExecutorOption
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.Interaction
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExpansionSource
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import scala.util.Random

/** The laws of where an entry's program is compiled (`CompilationPlaceOption`,
  * https://github.com/Atry/private-overlay/issues/1549,
  * https://github.com/Atry/private-overlay/issues/1827), on solo's entry, whose
  * lemma rounds compile the hot ladder's iterated sites to narrow blocks, read
  * with the executor of `ProgramRecordingModule`, and generated hot sites of
  * one iterated call (`HotSites.site`). The test pins solo's execution options,
  * its executor and its compilation place, so that the laws hold of the
  * framework's route whatever solo's data chooses. Under `upfront` the executor
  * receives the program the rounds give (`ProgramCompiler.compiledProgram`), as
  * before the option; under `by_executor` it receives the program uncompiled;
  * under both it is handed the entry's prepared compilation, and the two
  * entries' compilations are equal but for their configurations. The rounds
  * rewrite every drawn site, so that the two places are told apart by what the
  * executor receives. Its purpose is to catch an entry that runs its rounds
  * under `by_executor` or skips them under `upfront`, and a module handed
  * another compilation than the entry's, or one that depends on the option.
  */
class CompilationPlaceLawTest extends GeneratedProperties:

  private val buildRoot =
    Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  private val entryDirectory = buildRoot.resolve("contest-entries-solo")

  /** The table of the one module of these tests, its selector read off the tree
    * whose visible subtree is Gezi's directory.
    */
  private lazy val modules: ExecutorModules =
    ExecutorModules.registered(buildRoot, Vector(ProgramRecordingModule()))

  /** The natives both entries are built over, loaded once, so that their
    * compilations compare the natives as one value.
    */
  private lazy val natives = NativesProvider.loaded

  /** The cache service both entries are built with, so that the second entry's
    * reading of the knowledge answers from the tables the first one kept: built
    * with a cache service each, the two entries took the shared fixtures past
    * their 15 s deadline on two cores at a load of about 7 (main 9d04c1b6c,
    * 2026-11-21).
    */
  private lazy val caches = Defaults.caches()

  /** solo's entry, read as the judge's entry reads it, with its execution
    * options pinned: the test module as its executor and the compilation's
    * place given, whatever solo's data writes.
    */
  private def entryAt(place: CompilationPlaceOption): GenericEntry[?] =
    val (data, afterEntry) =
      EntryData.read(entryDirectory, Defaults.entryDataState)
    val Vector(selector) = (modules.bySelector.keys.toVector: @unchecked)
    GenericEntryProvider.initialized(
      data.copy(
        executor = ExecutorOption.Module(
          selector,
          Defunctionalization.thunkInstruction(Lambdalattice.term("λx. x"))(
            using gezi.ir.NoFacts
          )
        ),
        compilationPlace = place
      ),
      modules,
      ExtractorModules.registeredFor(entryDirectory),
      natives,
      ArticleDestination.Discarded,
      afterEntry,
      caches
    )

  private lazy val upfront: GenericEntry[?] = entryAt(
    CompilationPlaceOption.Upfront(UnitSelectionOption.WholeProgram)
  )

  private lazy val byExecutor: GenericEntry[?] = entryAt(
    CompilationPlaceOption.ByExecutor
  )

  private lazy val hotSites: HotSites[gezi.ir.NoFacts.type] =
    HotSites.read(buildRoot)

  /** Each entry with the hot sites crossed into its configuration. */
  private lazy val upfrontOpened: Opened[?] = Opened.of(upfront, hotSites)

  private lazy val byExecutorOpened: Opened[?] = Opened.of(byExecutor, hotSites)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => modules,
      _ => natives,
      _ => caches,
      _ => upfront,
      _ => byExecutor,
      _ => hotSites,
      _ => upfrontOpened,
      _ => byExecutorOpened
    )

  /** Its purpose is to catch a place given in the entry's data that does not
    * reach the entry.
    */
  test("the place given reaches the entry") {
    assertEquals(
      (upfront.compilationPlace, byExecutor.compilationPlace),
      (
        CompilationPlaceOption.Upfront(UnitSelectionOption.WholeProgram),
        CompilationPlaceOption.ByExecutor
      )
    )
  }

  // One input: each input runs solo's rounds twice and reads the site twice, and the laws hold of any site, so a run
  // checks them on one drawn site and successive runs draw others. Five inputs overran the 3 s deadline on main
  // eece45790 at a load of about 7 on two cores (2026-11-21, twice), and two did on 9d04c1b6c (3.013 s).
  stoppableProperty(
    "the executor receives the compiled program upfront, the uncompiled one by_executor, and the entry's compilation",
    _.copy(testLimit = hedgehog.core.SuccessCount(1))
  ) { stopped =>
    for
      seed <- Gen
        .long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))
        .forAll
      bits <- Gen.int(Range.linear(2, 5)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      Result
        .all(
          List(
            upfrontOpened.receivedCompiled(seed, bits, stop),
            byExecutorOpened.receivedUncompiled(seed, bits, stop),
            Result
              .diff(
                configurationFree(byExecutor.compilation),
                configurationFree(upfront.compilation)
              )(_ == _)
              .log(
                "the two entries' compilations, but for their configurations"
              )
          )
        )
        .log(
          s"a site of one iterated call of $bits binary digits, drawn from the seed $seed"
        )
  }

  /** What of a compilation does not depend on its configuration: each round's
    * lemmas, built-in rules, budget, narrow blocks' route and instances per
    * node, and the natives. The two entries are built apart, each with the
    * encoding of its own facts, so their compilations, which hold the
    * encoding's index and constructions, are of two configurations, which no
    * comparison of terms equates; what the place could change is this.
    */
  private def configurationFree(compilation: ProgramCompilation[?]) =
    (
      compilation.rounds.map(round =>
        (
          round.compilation.saturator.options.lemmas,
          round.compilation.saturator.options.builtInRules,
          round.compilation.budget,
          round.compilation.route,
          round.instancesPerNode
        )
      ),
      compilation.natives
    )

  /** An entry opened in its configuration `C`, the hot sites crossed into it,
    * with the laws on what its executor received.
    */
  private final case class Opened[C <: NativeSpecializer & Singleton](
      entry: GenericEntry[C],
      sites: HotSites[C]
  ):

    private given C = entry.specializer

    /** The point of the drawn site and its program, in `C`. The site is written
      * once: its draws happen inside the bodies of `λ` (`HotSites`).
      */
    private def drawn(
        seed: Long,
        bits: Int
    ): (DeBruijnTermOf[Configured[C]], Configured[C]) =
      val point = sites.site(Random(seed), 1, bits).locallyNamelessTerm
      (point, Defunctionalization.thunkInstruction[C](point))

    /** The compilation the entry's executor was handed and the programs it was
      * given, after the entry ran the cell of the point, in the entry's
      * configuration: the executor the module built and the entry the cell
      * returned are read in `C` after checking that their specializers are the
      * entry's (`NativeSpecializer.sameAs`).
      */
    private def received(
        point: DeBruijnTermOf[Configured[C]],
        stop: StopSignal
    ): ProgramRecordingExecutor[C] =
      entry.run(Cells.cell(point), ExpansionSource.fresh(), stop) match
        case Interaction.Finished(_, _, after: GenericEntry[?]) =>
          after.executor match
            case recording: ProgramRecordingExecutor[?] => recordedIn(recording)
            case other                                  =>
              throw AssertionError(s"the entry's executor is $other")
        case other => throw AssertionError(s"the entry's cell ended as $other")

    private def recordedIn[D <: NativeSpecializer & Singleton](
        recording: ProgramRecordingExecutor[D]
    ): ProgramRecordingExecutor[C] =
      NativeSpecializer.sameAs(
        recording.compilation.encoding: D,
        entry.specializer
      ) match
        case Some(same) => same[ProgramRecordingExecutor](recording)
        case None       =>
          throw AssertionError(
            "the module's executor is of another configuration than the entry's"
          )

    /** Under `upfront` the executor receives the program the rounds give, and
      * the entry's compilation; the rounds rewrite the site.
      */
    def receivedCompiled(seed: Long, bits: Int, stop: StopSignal): Result =
      val (point, program) = drawn(seed, bits)
      val (compiled, _) = ProgramCompiler.compiledProgram(
        entry.compilation,
        program,
        explained = false,
        stop
      )
      val afterTheRounds = received(point, stop)
      Result.all(
        List(
          Result
            .assert(
              afterTheRounds.received.size == 1 && afterTheRounds.received
                .forall(Configured.same(_, compiled))
            )
            .log("upfront: the programs received and the rounds' program"),
          Result
            .diff(afterTheRounds.compilation, entry.compilation)(_ == _)
            .log("upfront: the compilation handed and the entry's"),
          Result
            .assert(!Configured.same(compiled, program))
            .log("the rounds left the program as it was")
        )
      )

    /** Under `by_executor` the executor receives the program uncompiled, and
      * the entry's compilation.
      */
    def receivedUncompiled(seed: Long, bits: Int, stop: StopSignal): Result =
      val (point, program) = drawn(seed, bits)
      val beforeTheRounds = received(point, stop)
      Result.all(
        List(
          Result
            .assert(
              beforeTheRounds.received.size == 1 && beforeTheRounds.received
                .forall(Configured.same(_, program))
            )
            .log("by_executor: the programs received and the program"),
          Result
            .diff(beforeTheRounds.compilation, entry.compilation)(_ == _)
            .log("by_executor: the compilation handed and the entry's")
        )
      )

  private object Opened:

    /** The entry opened in its configuration, the sites crossed into it. */
    def of[C <: NativeSpecializer & Singleton](
        entry: GenericEntry[C],
        sites: HotSites[gezi.ir.NoFacts.type]
    ): Opened[C] =
      Opened(entry, HotSites.crossed(sites, entry.specializer))
