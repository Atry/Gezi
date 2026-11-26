package gezi.contest.entry.generic

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ArtifactKey
import gezi.hotspot.CompilationUnit
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramArtifacts
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

private given programCompilerLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the program unit's compiler (`ProgramCompiler`), on the
  * framework's fixture entry's three lemma rounds and generated programs, each
  * a recursive count by fixpoint over the successors of a drawn numeral,
  * nested a drawn number of times: the artifact the compiler writes is the
  * program the rounds give the residual directly
  * (`ProgramCompiler.compiledProgram`); a second compilation of the unit, under
  * a configuration whose rounds were prepared again from the same compilations,
  * spends no instance, so the key compares the rounds by value; and a
  * configuration of the first round alone finds nothing that the three rounds'
  * configuration wrote under the unit, and writes, at its own cost, the artifact
  * its own rounds give. Its purpose is
  * to catch an artifact that differs from what the rounds give, a second
  * compilation that runs the rounds again, and two configurations that share an
  * artifact.
  */
class ProgramCompilerLawTest extends GeneratedProperties:
  // Measured 2026-11-21 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load 7.1: the property takes
  // 2.498 s, its five inputs each running the fixture's three rounds three times and its first round once; the bound
  // is 1.5 times that rounded up to 5 s, since on 2 CPUs under load the reading may pass the 3 s default.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(5, "s")

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** The framework's fixture entry, read as the judge's entry reads it. */
  private lazy val entry: GenericEntry[?] =
    val entryDirectory = buildRoot.resolve("contest-entries-fixture")
    val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
    GenericEntryProvider.initialized(
      data,
      ExecutorModules.registeredFor(entryDirectory),
      ExtractorModules.registeredFor(entryDirectory),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )

  /** The entry's three configurations, in the entry's configuration. */
  private lazy val configurations: Configurations[?] = Configurations.of(entry)

  /** The library terms the programs are written with, closed instructions read by projection off the program
    * families' fixture file (`TermTables.programFamilyLibraryTerms`).
    */
  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary.entryMembers(buildRoot, TermTables.programFamilyLibraryTerms, Expansions.none)._1

  private def term(name: String): Term =
    Term.closed(terms.getOrElse(name, throw IllegalArgumentException(s"${TermTables.programFamilyLibraryTerms.file} has no member $name")))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => entry, _ => configurations, _ => terms)

  /** The recursive count of the successors of `natural`, by fixpoint, as the fixture's benchmark writes it
    * (`gezi.jmh.pipeline.CompiledRunInputs.recursiveCount`).
    */
  private def count(natural: Term): Term =
    term("fixpoint")(λ(self => λ(t => t(term("zero"))(λ(u => term("successor")(self(u)))))))(natural)

  /** The count nested `depth` times over successor^size zero, as an instruction. */
  private def program(size: Int, depth: Int): Configured[NoFacts.type] =
    val numeral = (1 to size).foldLeft(term("zero"))((value, _) => term("successor")(value))
    Defunctionalization.thunkInstruction((1 to depth).foldLeft(numeral)((value, _) => count(value)).deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)

  // Five inputs, not the default twenty: each input runs the fixture's rounds four times (the first round alone once),
  // and the laws hold of any program, so more inputs mostly repeat the rounds' cost.
  stoppableProperty("the compiler writes the rounds' program once per unit and configuration", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    stopped =>
      for
        size <- Gen.int(Range.linear(0, 6)).forAll
        depth <- Gen.int(Range.linear(1, 2)).forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        configurations
          .compiledOnce(program(size, depth), stop)
          .log(s"successor^$size zero counted $depth times")
  }

  /** The entry's configuration, its rounds as the entry prepared them (`configuration`); the same with every round
    * prepared again from its compilation and index, scaled by its instances per node as the entry scaled it
    * (`preparedAgain`); and the configuration of the entry's first round alone (`firstRoundAlone`), all in the entry's
    * configuration `C`.
    */
  private final case class Configurations[C <: NativeSpecializer & Singleton](
      configuration: ProgramCompilation[C],
      preparedAgain: ProgramCompilation[C],
      firstRoundAlone: ProgramCompilation[C]
  ):

    private given C = configuration.index.specializer

    /** The instances the rounds added, the cost `ProgramCompiler.compiled` reports for a compilation it ran. */
    private def instances(compilation: ProgramCompilation[C], residual: Configured[C], stop: StopSignal): (Configured[C], Long) =
      val (artifact, result) = ProgramCompiler.compiledProgram(compilation, residual, explained = false, stop)
      (artifact, result.fold(0L)(_.rounds.map(_.instances.toLong).sum))

    /** The laws on one program, written with no facts and crossed into `C` by its pure key. */
    def compiledOnce(written: Configured[NoFacts.type], stop: StopSignal): Result =
      val residual = Configured.fromPure(summon[C]: C)(Pure.required(written))
      val unit = CompilationUnit.Program(residual)
      val cache = Defaults.caches()
      val dependencies = ExecutionDependencies(cache, ExpansionSource.fresh())
      val artifacts = ProgramArtifacts(summon[C])
      val (direct, directInstances) = instances(configuration, residual, stop)
      val (firstRoundDirect, firstRoundInstances) = instances(firstRoundAlone, residual, stop)
      val (_, _, first) = ProgramCompiler(configuration).compiled(residual, unit, dependencies, stop)
      val written = cache.locked(artifacts)(_.tryGet(ArtifactKey(unit, configuration)))
      val (_, _, second) = ProgramCompiler(preparedAgain).compiled(residual, unit, dependencies, stop)
      val otherBefore = cache.locked(artifacts)(_.tryGet(ArtifactKey(unit, firstRoundAlone)))
      val (_, _, other) = ProgramCompiler(firstRoundAlone).compiled(residual, unit, dependencies, stop)
      val otherWritten = cache.locked(artifacts)(_.tryGet(ArtifactKey(unit, firstRoundAlone)))
      Result.all(
        List(
          Result.assert(written.exists(Configured.same(_, direct))).log("the artifact written and the rounds' program"),
          Result.diff(first.instances, directInstances)(_ == _).log("the first compilation's instances and the rounds'"),
          Result.diff(preparedAgain, configuration)(_ == _).log("the configuration with its rounds prepared again"),
          Result.diff(preparedAgain.hashCode, configuration.hashCode)(_ == _).log("their hashes"),
          Result.diff(second.instances, 0L)(_ == _).log("the second compilation's instances"),
          Result.assert(otherBefore.isEmpty).log("the first round's configuration found an artifact before it compiled"),
          Result.assert(otherWritten.exists(Configured.same(_, firstRoundDirect))).log("the first round's artifact and its rounds' program"),
          Result.diff(other.instances, firstRoundInstances)(_ == _).log("the first round's compilation's instances and its rounds'")
        )
      )

  private object Configurations:

    /** The entry's configurations, opened in its configuration. */
    def of[C <: NativeSpecializer & Singleton](entry: GenericEntry[C]): Configurations[C] =
      Configurations(
        ProgramCompilation(entry.index, entry.rounds, entry.natives, entry.encoding),
        ProgramCompilation(
          entry.index,
          entry.rounds.map(round => round.compilation.prepared(round.index).copy(instancesPerNode = round.instancesPerNode)),
          entry.natives,
          entry.encoding
        ),
        ProgramCompilation(entry.index, entry.rounds.take(1), entry.natives, entry.encoding)
      )
