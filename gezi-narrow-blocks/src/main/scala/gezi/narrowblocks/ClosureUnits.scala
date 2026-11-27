package gezi.narrowblocks

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.hotspot.ArtifactKey
import gezi.hotspot.CacheNamespace
import gezi.hotspot.CompilationUnit
import gezi.hotspot.CompilerConfiguration
import gezi.hotspot.ExpansionSource
import gezi.ir.Code
import gezi.ir.Hole
import gezi.saturation.BodyOpening
import gezi.saturation.End
import gezi.saturation.Opening
import gezi.saturation.StopSignal
import gezi.strategies.FixpointEgraph
import gezi.ir.{Configured, NativeSpecializer}

/** Every input of a closure unit's compilation but the unit's function: the
  * entry's prepared compilation, the version of the contents the URI nodes
  * expand to (compared by identity, as `ExpansionSource` is) and the unit's
  * arity, the number of eigenvariables its compilation opens it at.
  */
final case class ClosureUnitCompilation[C <: NativeSpecializer & Singleton](
    compilation: ProgramCompilation[C],
    source: ExpansionSource,
    arity: Int
) extends CompilerConfiguration

/** The namespace of the closure units' artifacts in the cache service: under
  * the unit `Closure(F)` and `ClosureUnitCompilation`, the artifact
  * `ClosureUnits.compiledUnit` gives. The memo of a pure function of the key
  * (`CONTRIBUTING.md`, "Tables", kind 2): the rounds run under the caller's
  * stop, and a compilation the stop asked to stop is not written.
  */
// FIXME: an artifact is cached with no proof, and the key has no `explained`, so the article of a point that https://github.com/Atry/private-overlay/issues/2217
// replaces a unit by its artifact cannot be written; the unit's proof is to be kept with the artifact.
final case class ClosureArtifacts[C <: NativeSpecializer & Singleton](specializer: C)
    extends CacheNamespace[ArtifactKey[C, Configured[C]], Configured[C]]("narrow_blocks.closure_artifacts")

/** What a closure unit's compilation gave: the artifact, the instances its
  * rounds added, how its last round ended, whether the artifact is the
  * function itself (the extraction kept it, or the rounds were stopped), and
  * the graph the compilation left, none when it ran no round or the artifact
  * was read from the cache service.
  */
final case class CompiledUnit[C <: NativeSpecializer & Singleton](
    artifact: Configured[C],
    instances: Long,
    end: Option[End],
    kept: Boolean,
    graph: Option[EGraph[C]]
)

/** The compilation of a closure unit and the replacement of units in a
  * program by their artifacts.
  *
  * A unit is a closed function F with an arity k (`BoundFunctionUnit`: the
  * function a program's top-level let binds, and the most arguments its body
  * applies it to). Its compilation runs the entry's rounds on F applied to
  * k eigenvariables, so that the knowledge's lemmas at calls find the call
  * `F v1 … vk` to write their filters at, and gives the term of F's class
  * the entry's own extractor chooses once the typed body has been written
  * back into that class. A program's literals are not in F, so every point
  * of a family whose let binds one F reads one artifact.
  *
  * The graph holds F and its η-expansions, one level per argument: T1 =
  * `λx. F x`, a thunk of one hole whose code applies its one filling to the
  * hole; its body opened at the eigenvariable v1 (`BodyOpening.openedAt`) is
  * `F v1`; T2 = `λx. (F v1) x` over that body's class, opened at v2; and so
  * on to the body `F v1 … vk`. Each body is read by the β rule
  * (`EGraph.applicationRead`): its function is a slot the level's filling
  * fills, which the β rule does not read of itself (it reads an application
  * whose function a code writes as a thunk), so that `F v1` takes a β step
  * with each closure F's class holds, and a level's body with each its
  * filling's class gains. The rounds saturate the graph. Then, from the
  * innermost level out, the body's class is extracted, written back as a
  * thunk united with the level's T by the abstraction rule
  * (`BodyOpening.writtenBack`, which writes back only when the
  * eigenvariables are alone in their classes), and T is united with its
  * filling by the η rule (`Justification.Eta`), so that each written-back
  * thunk reaches the class of the level above and, at the outermost, F's
  * class. Each level is a one-hole η step, the shape of the defunctionalized
  * η rule (`gezi.rewritetrace.Statements.eta`); the k levels together are
  * `λx1 … xk. F x1 … xk = F`. Every union is an equation: a lemma instance, a
  * built-in rule, congruence, the abstraction rule or the η rule. So the
  * artifact equals F up to ≃_O.
  *
  * The artifact is F's class as the last round's extractor spells it, so
  * the written-back thunk competes with F in one class under one extractor;
  * when the extractor keeps F the unit changes nothing (`CompiledUnit.kept`).
  * The narrow blocks of the last round are not computed on a unit: a unit's
  * body holds its eigenvariables, so no closed natural is there to compute.
  */
object ClosureUnits:

  /** The η-expanding code: slot 0, the filling, applied to slot 1, the hole. */
  private val etaCode: Code = Code(gezi.ir.Apply(Code(gezi.ir.Slot(0)), Code(gezi.ir.Slot(1))))

  /** The one hole of the η-expanding thunk. */
  private val etaHoles: Vector[Hole] = Vector(Hole.Bound(1))

  /** The unit's compilation under the configuration: the artifact and what
    * the rounds spent, as the class documentation says, the graph recording
    * the terms made when `explained`. A configuration with no round, or
    * rounds the stop stopped, gives the function itself.
    */
  def compiledUnit[C <: NativeSpecializer & Singleton](
      configuration: ProgramCompilation[C],
      function: Configured[C],
      arity: Int,
      explained: Boolean,
      stop: StopSignal
  )(using C): CompiledUnit[C] =
    require(arity > 0, s"a closure unit is opened at one eigenvariable or more: $arity")
    configuration.rounds.lastOption match
      case None => CompiledUnit(function, 0, None, kept = true, None)
      case Some(last) =>
        val shared = configuration.rounds.map(_.compiledRound)
        val (withFunction, functionNode) = FixpointEgraph.sharedGraph(shared, explained).instructionAdded(function)
        // Each level: the thunk's node, its filling's node, the opening, and
        // the term of the body as written (`F v1 … vi`), what an extraction
        // the stop ended gives for the body's class.
        val (opened, levels) = (1 to arity).foldLeft((withFunction, Vector.empty[(Int, Int, Opening[C], Configured[C])])) {
          case ((graph, made), _) =>
            val (filling, fillingTerm) = made.lastOption.fold((functionNode, function))((_, _, opening, term) => (opening.body, term))
            val thunk = gezi.ir.Thunk(etaCode, etaHoles, Vector(filling))
            val (withThunk, thunkNode) = graph.layerAdded(thunk)
            val (withBody, opening) = BodyOpening.openedAt(withThunk, thunkNode, thunk)
            val Vector((leaf, _)) = opening.eigenvariables: @unchecked
            (withBody.applicationRead(opening.body), made :+ (thunkNode, filling, opening, (summon[C]: C).application(fillingTerm, leaf)))
        }
        val (saturated, instances, lastEnd) = configuration.rounds.foldLeft((opened, 0L, Option.empty[End])) {
          case ((graph, spent, Some(previous @ End.Stopped(_))), _) => (graph, spent, Some(previous))
          case ((graph, spent, _), round) =>
            val run = round.saturatedOn(graph, shared, function, stop)
            (run.graph, spent + (run.graph.instances - graph.instances), Some(run.end))
        }
        lastEnd match
          case Some(End.Stopped(_)) => CompiledUnit(function, instances, lastEnd, kept = true, Some(saturated))
          case _ =>
            val eigenvariables = levels.flatMap((_, _, opening, _) => opening.eigenvariables).toMap
            val writtenBack = levels.reverse.foldLeft(saturated) { case (graph, (thunkNode, filling, opening, bodyTerm)) =>
              val body = classSpelled(last, graph, opening.body, bodyTerm, stop)
              BodyOpening
                .writtenBack(graph, opening, body, eigenvariables)
                .unionWorked(thunkNode, filling, Justification.Eta(thunkNode), None)
            }
            val artifact = classSpelled(last, writtenBack, functionNode, function, stop)
            assert(
              !holdsEigenvariable(artifact, configuration.index.noinline),
              s"a closure unit's artifact is closed: an eigenvariable of its compilation is in it"
            )
            CompiledUnit(artifact, instances, lastEnd, kept = Configured.same(artifact, function), Some(writtenBack))

  /** Whether the term holds an opaque instruction that is no noinline name
    * of the library, as an eigenvariable is, each distinct subterm visited
    * once; a native storage the e-graph keeps as a leaf holds none, its view
    * not read.
    */
  private def holdsEigenvariable[C <: NativeSpecializer & Singleton](term: Configured[C], noinline: Set[Configured[C]])(using C): Boolean =
    @scala.annotation.tailrec
    def visited(pending: List[Configured[C]], seen: Set[Configured[C]]): Boolean = pending match
      case Nil                                  => false
      case head :: rest if seen.contains(head) => visited(rest, seen)
      case head :: rest =>
        head.layer match
          case gezi.ir.Opaque(_) if !noinline.contains(head) => true
          case _ if head.heldAsLeaf || noinline.contains(head) => visited(rest, seen + head)
          case layer                                         => visited(layer.children.toList ::: rest, seen + head)
    visited(List(term), Set.empty)

  /** The term of the node's class as the round's extractor spells it,
    * `written`, a term of the class, what an extraction the stop ended gives.
    */
  private def classSpelled[C <: NativeSpecializer & Singleton](round: PreparedLemmaCompilation[C], graph: EGraph[C], node: Int, written: Configured[C], stop: StopSignal)(using C): Configured[C] =
    round.compilation.extractor.extracted(round.index, graph, Vector(node), Vector(written), stop) match
      case Vector(output) => output
      case outputs        => throw IllegalStateException(s"one output for one class, not ${outputs.size}")

  /** The unit of the program cut by `BoundFunctionUnit`, compiled into the
    * cache service under `ArtifactKey(Closure(F), ClosureUnitCompilation)`,
    * or read from it: the artifact and the instances spent, none on a hit. A
    * compilation the stop asked to stop is not written. None for a program
    * with no unit.
    */
  def cached[C <: NativeSpecializer & Singleton](
      configuration: ProgramCompilation[C],
      program: Configured[C],
      dependencies: gezi.hotspot.ExecutionDependencies,
      explained: Boolean,
      stop: StopSignal
  )(using C): Option[(BoundFunctionUnit[C], CompiledUnit[C])] =
    val artifacts = ClosureArtifacts[C](summon[C])
    BoundFunctionUnit.of(program).map { unit =>
      val key = ArtifactKey[C, Configured[C]](
        CompilationUnit.Closure(unit.function),
        ClosureUnitCompilation(configuration, dependencies.source, unit.arity)
      )
      dependencies.cache.locked(artifacts)(_.tryGet(key)) match
        case Some(artifact) => (unit, CompiledUnit(artifact, 0, None, kept = Configured.same(artifact, unit.function), None))
        case None =>
          val compiled = compiledUnit(configuration, unit.function, unit.arity, explained, stop)
          if !stop.stopRequested then dependencies.cache.locked(artifacts)(_.getOrElseUpdate(key, compiled.artifact))
          (unit, compiled)
    }

  /** The program with each unit replaced by its artifact, by one round with
    * no lemma: the program added to a graph of the configuration's rounds,
    * each unit's node united with its artifact's (`Justification.Compiled`),
    * and the program's class spelled by the last round's extractor, with
    * the graph; the program itself when no union was made (every artifact
    * the unit itself), and with no graph when the configuration has no
    * round.
    *
    * The extraction gives the program with the units spelled by their
    * artifacts when the last round's cost model has no repeller production:
    * its choice in a class is then the least of the class's members'
    * spellings in an order of the spellings alone, a unit's class here holds
    * the unit's spelling and the artifact's, and the unit's compilation chose
    * the artifact in a class that held both. Under a model with repellers a
    * spelling's admissibility depends on what the graph's classes hold, and
    * the extraction may keep a unit: sound, the unit's compilation lost.
    */
  def replaced[C <: NativeSpecializer & Singleton](
      configuration: ProgramCompilation[C],
      program: Configured[C],
      units: Vector[(Configured[C], Configured[C])],
      explained: Boolean,
      stop: StopSignal
  )(using C): (Configured[C], Option[EGraph[C]]) =
    configuration.rounds.lastOption match
      case None => (program, None)
      case Some(last) =>
        val shared = configuration.rounds.map(_.compiledRound)
        val (withProgram, programNode) = FixpointEgraph.sharedGraph(shared, explained).instructionAdded(program)
        val united = units.foldLeft(withProgram) { case (graph, (function, artifact)) =>
          val functionNode = graph.instructionNode(function).getOrElse(throw IllegalArgumentException(s"no node of the unit $function in the program"))
          val (withArtifact, artifactNode) = graph.instructionAdded(artifact)
          withArtifact.unionWorked(functionNode, artifactNode, Justification.Compiled(functionNode), None)
        }
        if united.unionCount == withProgram.unionCount then (program, Some(united))
        else (classSpelled(last, united, programNode, program, stop), Some(united))

  /** The program an entry reads after compiling its closure unit: the unit
    * cut by `BoundFunctionUnit`, compiled or read from the cache service
    * (`cached`), and replaced in the program by its artifact (`replaced`),
    * with what the compilation gave, as `ProgramCompiler.compiledProgram`
    * reports it: the replacement's graph, the program it spells as the
    * extraction, and the saturation of the unit's compilation's rounds (none
    * on a cache hit, where no round ran), with the unit's compilation. A
    * program with no unit is compiled whole (`ProgramCompiler.compiledProgram`).
    */
  def compiledProgram[C <: NativeSpecializer & Singleton](
      configuration: ProgramCompilation[C],
      program: Configured[C],
      dependencies: gezi.hotspot.ExecutionDependencies,
      explained: Boolean,
      stop: StopSignal
  )(using C): (Configured[C], Option[LemmaRoundsResult[C]]) =
    cached(configuration, program, dependencies, explained, stop) match
      case None => ProgramCompiler.compiledProgram(configuration, program, explained, stop)
      case Some((unit, compiled)) =>
        val (output, graph) = replaced(configuration, program, Vector((unit.function, compiled.artifact)), explained, stop)
        (
          output,
          graph.map(replacement =>
            LemmaRoundsResult(
              None,
              Some(output),
              Vector.empty,
              compiled.end.toVector.map(end => RoundSaturation(compiled.instances.toInt, end)),
              replacement,
              Vector.empty,
              Vector(compiled)
            )
          )
        )
