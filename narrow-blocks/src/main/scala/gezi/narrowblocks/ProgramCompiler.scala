package gezi.narrowblocks

import gezi.hotspot.ArtifactKey
import gezi.hotspot.CacheNamespace
import gezi.hotspot.CompilationSpent
import gezi.hotspot.CompilationUnit
import gezi.hotspot.Compiler
import gezi.hotspot.CompilerConfiguration
import gezi.hotspot.ExecutionDependencies
import gezi.ir.Instruction
import gezi.jit.NativeBackend
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex

/** The configuration of `ProgramCompiler`, every input of its compilation but
  * the program (`CONTRIBUTING.md`, "Tables"): the library's index, the entry's
  * prepared lemma rounds, in order, the last one's route running them, and
  * the natives their narrow blocks call.
  *
  * Its equality, the equality of the artifacts' keys:
  *   - the index by value, its hash computed once when it is made
  *     (`StandardLibraryIndex.hashCode`);
  *   - each round by what prepares it, its compilation and the index it is
  *     prepared for (`LemmaCompilation.prepared`): the prepared saturator, its
  *     compiled round and that round's e-graph, is a function of those two,
  *     and comparing it would walk an e-graph at every lookup;
  *   - the natives as `NativeBackend` compares them.
  *
  * Two parts are compared by identity, since no equality of code exists:
  * the implementations of the natives, Scala functions, and the names
  * function of a round's write-backs (`LocalExtraction.names`, in a round
  * with opening). The same goes for a module's extraction or route that has
  * no equality of its own. Identity is finer than the value, so it can only
  * miss an artifact another configuration compiled the same way, never hand
  * one configuration's artifact to another: two configurations built apart
  * from the same data, by two loads of the natives
  * (`NativesProvider.loaded`), share nothing.
  *
  * @param index
  *   the library's index the rounds read
  * @param rounds
  *   the prepared lemma rounds, run on one shared e-graph
  *   (`NarrowBlockRoute.compiledRounds` of the last one's route)
  * @param natives
  *   the natives the narrow blocks call
  */
final case class ProgramCompilation(index: StandardLibraryIndex, rounds: Vector[PreparedLemmaCompilation], natives: NativeBackend)
    extends CompilerConfiguration:

  /** What the equality compares (see the class's documentation). */
  private def compared: (StandardLibraryIndex, Vector[(LemmaCompilation, StandardLibraryIndex)], NativeBackend) =
    (index, rounds.map(round => (round.compilation, round.index)), natives)

  /** The hash of what the equality compares, computed once: a configuration is
    * part of every key of `ProgramArtifacts`, hashed at each lookup, and its
    * hash walks the natives' table.
    */
  override lazy val hashCode: Int = compared.##

  override def equals(other: Any): Boolean = other match
    case that: ProgramCompilation => (this eq that) || (hashCode == that.hashCode && compared == that.compared)
    case _                        => false

/** The namespace of `ProgramCompiler`'s artifacts in the cache service: under
  * the program unit and the configuration (`ArtifactKey`), the program the
  * entry reads after its lemma rounds. The memo of a pure function of the
  * key (`CONTRIBUTING.md`, "Tables", kind 2): the rounds run under no stop
  * (`ProgramCompiler.compiled`), so the artifact is not an answer read within
  * a budget, and clearing it changes only cost.
  */
object ProgramArtifacts extends CacheNamespace[ArtifactKey[Instruction], Instruction]("narrow_blocks.program_artifacts")

/** The baseline compiler of a program unit: its artifact is the program an entry reads after its lemma rounds,
  * the rounds run on one shared e-graph and the last round's extraction with
  * its narrow blocks computed (`ProgramCompiler.compiledProgram`), written to
  * `ProgramArtifacts` under `ArtifactKey(unit, configuration)`, so that a unit
  * compiled twice under one configuration is computed once. The generic
  * entry compiles its points by the same function
  * (`gezi.contest.entry.generic.GenericEntry`), so that there is one path.
  *
  * @param configuration
  *   every input of the compilation but the program
  */
final case class ProgramCompiler(configuration: ProgramCompilation) extends Compiler[Instruction]:

  /** The program unit compiled into the cache service, the residual being
    * the unit's root: the key holds the root, not the residual, so a residual
    * of another root would be compiled under a key that leaves out what it
    * depends on (`CONTRIBUTING.md`, "Tables"); a caller compiling a residual
    * names it as the unit, `CompilationUnit.Program(residual)`. The cost is
    * the instances the rounds added, or none when the artifact was already
    * written. The compilation runs outside the namespace's lock: `tryGet` first, the rounds on a miss, then
    * `getOrElseUpdate`. Throws `IllegalArgumentException` for a code or a
    * closure unit, and for a residual that is not the unit's root.
    *
    * The rounds read the stop; a compilation the stop has asked to stop by
    * the time the rounds return is not written, its artifact depending on
    * when it stopped, and its instances are reported all the same.
    */
  def compiled(
      residual: Instruction,
      unit: CompilationUnit,
      dependencies: ExecutionDependencies,
      stop: StopSignal
  ): (Compiler[Instruction], ExecutionDependencies, CompilationSpent) =
    unit match
      case CompilationUnit.Program(root) =>
        require(root == residual, s"a program unit's root is the residual compiled: $root is not $residual")
        val key = ArtifactKey[Instruction](unit, configuration)
        dependencies.cache.locked(ProgramArtifacts)(_.tryGet(key)) match
          case Some(_) => (this, dependencies, CompilationSpent(0))
          case None =>
            val (artifact, result) = ProgramCompiler.compiledProgram(configuration, residual, explained = false, stop)
            if !stop.stopRequested then dependencies.cache.locked(ProgramArtifacts)(_.getOrElseUpdate(key, artifact))
            (this, dependencies, CompilationSpent(result.fold(0L)(_.rounds.map(_.instances.toLong).sum)))
      case CompilationUnit.Code(_) | CompilationUnit.Closure(_) =>
        throw IllegalArgumentException(s"the program compiler compiles program units, not $unit")

/** The compilation of a program by an entry's lemma rounds. */
object ProgramCompiler:

  /** The program an entry reads after the configuration's rounds, with what
    * the rounds gave: the rounds on one shared e-graph, run by the last
    * round's route (`NarrowBlockRoute.compiledRounds`), its graph recording
    * the terms made when `explained` (a run whose proof is wanted), and then
    * the program with its blocks computed, else the extraction, else the
    * program; the program itself, and nothing, when the configuration has no
    * round.
    */
  def compiledProgram(
      configuration: ProgramCompilation,
      program: Instruction,
      explained: Boolean,
      stop: StopSignal
  ): (Instruction, Option[LemmaRoundsResult]) =
    configuration.rounds.lastOption match
      case None => (program, None)
      case Some(last) =>
        val result =
          last.compilation.route.compiledRounds(configuration.index, configuration.rounds, configuration.natives, program, explained, stop)
        // FIXME (https://github.com/Atry/private-overlay/issues/1788): the order of what is read after the rounds
        // (the program with its blocks computed, else the extraction, else the program) is fixed here, the only
        // implementation. It is to become an option of one interface chosen by configuration (entry data and
        // `Defaults`) once a second one exists.
        (result.program.orElse(result.extracted).getOrElse(program), Some(result))
