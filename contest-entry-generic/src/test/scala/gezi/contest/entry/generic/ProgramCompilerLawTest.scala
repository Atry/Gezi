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
import gezi.ir.Instruction
import gezi.jit.NativesProvider
import gezi.narrowblocks.ProgramArtifacts
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Expansions

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
  private lazy val entry: GenericEntry =
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

  /** The entry's configuration, its rounds as the entry prepared them. */
  private lazy val configuration: ProgramCompilation = ProgramCompilation(entry.index, entry.rounds, entry.natives)

  /** The same configuration with every round prepared again from its compilation and index. */
  private lazy val preparedAgain: ProgramCompilation =
    ProgramCompilation(entry.index, entry.rounds.map(round => round.compilation.prepared(round.index)), entry.natives)

  /** The configuration of the entry's first round alone. */
  private lazy val firstRoundAlone: ProgramCompilation = ProgramCompilation(entry.index, entry.rounds.take(1), entry.natives)

  /** The library terms the programs are written with, closed instructions read by projection off the program
    * families' fixture file (`TermTables.programFamilyLibraryTerms`).
    */
  private lazy val terms: Map[String, Instruction] =
    StandardLibrary.entryMembers(buildRoot, TermTables.programFamilyLibraryTerms, Expansions.none)._1

  private def term(name: String): Term =
    Term.closed(terms.getOrElse(name, throw IllegalArgumentException(s"${TermTables.programFamilyLibraryTerms.file} has no member $name")))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => entry, _ => configuration, _ => preparedAgain, _ => firstRoundAlone, _ => terms)

  /** The recursive count of the successors of `natural`, by fixpoint, as the fixture's benchmark writes it
    * (`gezi.jmh.pipeline.CompiledRunInputs.recursiveCount`).
    */
  private def count(natural: Term): Term =
    term("fixpoint")(λ(self => λ(t => t(term("zero"))(λ(u => term("successor")(self(u)))))))(natural)

  /** The count nested `depth` times over successor^size zero, as an instruction. */
  private def program(size: Int, depth: Int): Instruction =
    val numeral = (1 to size).foldLeft(term("zero"))((value, _) => term("successor")(value))
    Defunctionalization.thunkInstruction((1 to depth).foldLeft(numeral)((value, _) => count(value)).deBruijnTerm(Map.empty))

  /** The instances the rounds added, the cost `ProgramCompiler.compiled` reports for a compilation it ran. */
  private def instances(compilation: ProgramCompilation, residual: Instruction, stop: StopSignal): (Instruction, Long) =
    val (artifact, result) = ProgramCompiler.compiledProgram(compilation, residual, explained = false, stop)
    (artifact, result.fold(0L)(_.rounds.map(_.instances.toLong).sum))

  // Five inputs, not the default twenty: each input runs the fixture's rounds four times (the first round alone once),
  // and the laws hold of any program, so more inputs mostly repeat the rounds' cost.
  stoppableProperty("the compiler writes the rounds' program once per unit and configuration", _.copy(testLimit = hedgehog.core.SuccessCount(5))) {
    stopped =>
      for
        size <- Gen.int(Range.linear(0, 6)).forAll
        depth <- Gen.int(Range.linear(1, 2)).forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        val residual = program(size, depth)
        val unit = CompilationUnit.Program(residual)
        val cache = Defaults.caches()
        val dependencies = ExecutionDependencies(cache, ExpansionSource.fresh())
        val (direct, directInstances) = instances(configuration, residual, stop)
        val (firstRoundDirect, firstRoundInstances) = instances(firstRoundAlone, residual, stop)
        val (_, _, first) = ProgramCompiler(configuration).compiled(residual, unit, dependencies, stop)
        val written = cache.locked(ProgramArtifacts)(_.tryGet(ArtifactKey(unit, configuration)))
        val (_, _, second) = ProgramCompiler(preparedAgain).compiled(residual, unit, dependencies, stop)
        val otherBefore = cache.locked(ProgramArtifacts)(_.tryGet(ArtifactKey(unit, firstRoundAlone)))
        val (_, _, other) = ProgramCompiler(firstRoundAlone).compiled(residual, unit, dependencies, stop)
        val otherWritten = cache.locked(ProgramArtifacts)(_.tryGet(ArtifactKey(unit, firstRoundAlone)))
        Result
          .all(
            List(
              Result.diff(written, Some(direct))(_ == _).log("the artifact written and the rounds' program"),
              Result.diff(first.instances, directInstances)(_ == _).log("the first compilation's instances and the rounds'"),
              Result.diff(preparedAgain, configuration)(_ == _).log("the configuration with its rounds prepared again"),
              Result.diff(preparedAgain.hashCode, configuration.hashCode)(_ == _).log("their hashes"),
              Result.diff(second.instances, 0L)(_ == _).log("the second compilation's instances"),
              Result.assert(otherBefore.isEmpty).log("the first round's configuration found an artifact before it compiled"),
              Result.diff(otherWritten, Some(firstRoundDirect))(_ == _).log("the first round's artifact and its rounds' program"),
              Result.diff(other.instances, firstRoundInstances)(_ == _).log("the first round's compilation's instances and its rounds'")
            )
          )
          .log(s"successor^$size zero counted $depth times")
  }
