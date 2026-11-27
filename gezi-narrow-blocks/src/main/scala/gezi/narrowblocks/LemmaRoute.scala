package gezi.narrowblocks

import gezi.egraph.EGraph
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.jit.NativeBackend
import gezi.rewritetrace.PositionSegment
import gezi.rewritetrace.Positions
import gezi.rewritetrace.TraceCommand
import gezi.saturation.End
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.strategies.FixpointEgraph
import gezi.strategies.NormalityModule
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.{Configured, NativeSpecializer}

/** What the lemma route gave for a program: the program with every narrow
  * block computed, or nothing; the round's extraction, equal to the
  * program under ⊢, or nothing when the round was stopped; the steps it went
  * through, in order, each with the nanoseconds it took; the instances of
  * the saturation's graph; and how the saturation ended.
  */
final case class LemmaRouteResult[C <: NativeSpecializer & Singleton](
    program: Option[Configured[C]],
    extracted: Option[Configured[C]],
    steps: Vector[(String, Long)],
    instances: Int,
    end: End
)

/** One lemma round's saturation on the shared graph: the instances it added
  * and how it ended.
  */
final case class RoundSaturation(instances: Int, end: End)

/** What the shared lemma rounds gave for a program: the program with every
  * narrow block computed, or nothing; the last round's extraction, or
  * nothing when a round was stopped; the steps, in order, with their
  * nanoseconds; each round's saturation, in order, as far as the rounds
  * went; the graph the last round that ran left, which the extraction
  * read and from which a proof of the program equal to its extraction is
  * read (`GraphProof`); and the trace's commands that take the extraction
  * to the program with its blocks computed (`LemmaRoute.nativeCommands`),
  * none when no block was computed or the run was not `explained`; and the
  * closure units compiled for the program (`ClosureUnits.compiledProgram`),
  * none when the program was compiled whole.
  */
final case class LemmaRoundsResult[C <: NativeSpecializer & Singleton](
    program: Option[Configured[C]],
    extracted: Option[Configured[C]],
    steps: Vector[(String, Long)],
    rounds: Vector[RoundSaturation],
    graph: EGraph[C],
    natives: Vector[TraceCommand[C]],
    units: Vector[CompiledUnit[C]] = Vector.empty[CompiledUnit[C]]
)

/** The lemma route: the round of a lemma compilation, its extraction's narrow blocks
  * compiled to bytecode and run, and their numerals put back into the
  * program.
  *
  * It began as a copy of `WrenEntry.lemmaCompiledTimed` via
  * `SoloEntry.lemmaCompiled`, with `numeral` and `substituted`; it takes
  * the entry's natives as data instead of naming them. It resolves
  * SoloEntry's FIXME of 2026-11-07, which asked for this glue in the
  * framework beside `LemmaCompilation`.
  */
object LemmaRoute extends NarrowBlockRoute:

  /** The configuration of the program a round's run holds: its graph's construction, the native specializer and the
    * capability of the round's configuration.
    */
  def readingConfiguration[C <: NativeSpecializer & Singleton](run: Run[C]): gezi.weakhead.ReadingConfiguration[C] =
    gezi.weakhead.ReadingConfiguration(run.graph.store.construction.specializer, run.graph.store.construction.storageAccess)

  /** The default narrow blocks' modules, `LemmaCompilation.extractorModules`. */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] = LemmaCompilation.extractorModules(natives, configuration)

  /** The program with every narrow block of its lemma compilation computed:
    * the round of `compilation`, its extraction's maximal closed narrow
    * naturals compiled to bytecode (`NarrowBlockCompilation` with
    * `natives`) and run, each replaced by the canonical binary natural it
    * computes; nothing when the round is stopped, finds no block, or a block
    * does not compile. With the steps it went through, in order:
    * `lemma_saturation`, `lemma_extraction`, `block_compilation` and
    * `block_run`, as far as it got. The graph records the terms made when
    * `explained` (a run whose proof is wanted).
    */
  def compiled[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      compilation: PreparedLemmaCompilation[C],
      natives: NativeBackend,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRouteResult[C] =
    val (run, saturation) = timed("lemma_saturation")(compilation.saturated(program, explained, stop))
    val (computed, extracted, steps) = blocksComputed(index, compilation, natives, program, run, Vector(saturation), explained, stop)
    LemmaRouteResult(computed.map(_._1), extracted, steps, run.graph.instances, run.end)

  /** The lemma rounds on one shared graph: the graph built for every round (`FixpointEgraph.sharedGraph`),
    * each round in order saturating it to its fixed point under its own
    * modules and budget (`PreparedLemmaCompilation.saturatedOn`), and only
    * after the last round the graph extracted by the last round's
    * extraction and its narrow blocks compiled and run, as `compiled` does.
    * A stopped round ends the rounds; the graph records the terms made when
    * `explained` (a run whose proof is wanted). Each round is a `lemma_saturation`
    * step, with the instances it added and how it ended.
    *
    * It replaces handing an extraction from round to round, which loses
    * what a later round needs: measured (2026-11-07),
    * wren_typed_block, an extraction, then wren_typed_specialization finds
    * no block on any hot program, the extraction dropping the typed member
    * of a choice.
    */
  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C] =
    val (run, steps, saturations) = saturatedRounds(rounds, program, explained, stop)
    val (computed, extracted, allSteps) = blocksComputed(index, rounds.last, natives, program, run, steps, explained, stop)
    LemmaRoundsResult(
      computed.map(_._1),
      extracted,
      allSteps,
      saturations,
      run.graph,
      computed.fold(Vector.empty[TraceCommand[C]])(_._2)
    )

  /** The saturation part of `compiledRounds`: the graph built for every
    * round, recording the terms made when `explained`, each round in order
    * saturating it, a stopped round ending the rounds. The last run, its
    * `lemma_saturation` steps and each round's saturation.
    */
  def saturatedRounds[C <: NativeSpecializer & Singleton](
      rounds: Vector[PreparedLemmaCompilation[C]],
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): (Run[C], Vector[(String, Long)], Vector[RoundSaturation]) =
    require(rounds.nonEmpty, "the shared rounds are one round or more")
    val shared = rounds.map(_.compiledRound)
    val initial = FixpointEgraph.sharedGraph(shared, explained)
    val (lastRun, steps, saturations) =
      rounds.foldLeft((Option.empty[Run[C]], Vector.empty[(String, Long)], Vector.empty[RoundSaturation])) {
        case ((Some(previous), steps, saturations), _) if stopped(previous.end) => (Some(previous), steps, saturations)
        case ((previous, steps, saturations), round) =>
          val graph = previous.fold(initial)(_.graph)
          val (run, step) = timed("lemma_saturation")(round.saturatedOn(graph, shared, program, stop))
          (Some(run), steps :+ step, saturations :+ RoundSaturation(run.graph.instances - graph.instances, run.end))
      }
    (lastRun.getOrElse(throw IllegalStateException("one round or more ran")), steps, saturations)

  private[narrowblocks] def stopped(end: End): Boolean = end match
    case End.Stopped(_) => true
    case _              => false

  /** The extraction of the run's graph by `compilation`, or the program
    * itself when the graph has no union at all: neither a lemma instance nor
    * a built-in rule (β among them) joined two classes, so every class holds
    * the one node it was made with, and the extraction reads the program
    * back. That is what `NoUnionExtractionLawTest` checks on generated
    * programs. Measured 2026-11-21 on 122 generated points of the program
    * families saturated by an entry's lemma rounds: 104 had no union, each
    * one's extraction was the program, and reading it back cost those 104
    * points 18.1 s in all. The narrow blocks are then searched in the
    * program, as they would be in the extraction, so a block a graph with no
    * union still holds (48 of the 104 points have some) is still computed.
    */
  private def extractionOf[C <: NativeSpecializer & Singleton](compilation: PreparedLemmaCompilation[C], program: Configured[C], run: Run[C], stop: StopSignal)(using C): Configured[C] =
    if run.graph.unionCount == 0 then program else compilation.extracted(program, run, stop)

  /** After a saturation: nothing more when it was stopped; otherwise the
    * extraction by `compilation`, its narrow blocks compiled to bytecode
    * (`NarrowBlockCompilation` with `natives`) and run under `stop`, each
    * replaced by the canonical binary natural it computes. The program with
    * its blocks computed and the native commands that take the extraction to
    * it (only when `explained`, so that a scored reading pays nothing for
    * them), or nothing, as when a block does not compile, if `stop` stopped a
    * block's run; the extraction, or nothing; and the steps, those given then
    * `lemma_extraction`, `block_compilation` and `block_run`, as far as it got.
    *
    * FIXME: after the last round each block is evaluated eagerly https://github.com/Atry/private-overlay/issues/2032
    * to its end at compile time and substituted back as a numeral; when to evaluate a block and the representation of
    * its value are fixed here. Each is to become an option of one interface chosen by configuration (entry data and
    * `Defaults`).
    */
  private def blocksComputed[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      compilation: PreparedLemmaCompilation[C],
      natives: NativeBackend,
      program: Configured[C],
      run: Run[C],
      steps: Vector[(String, Long)],
      explained: Boolean,
      stop: StopSignal
  )(using C): (Option[(Configured[C], Vector[TraceCommand[C]])], Option[Configured[C]], Vector[(String, Long)]) =
    if stopped(run.end) then (None, None, steps)
    else
      val blockCompilation = NarrowBlockCompilation(index, natives, LemmaRoute.readingConfiguration(run))
      val ((output, blocks), extraction) = timed("lemma_extraction") {
        val extracted = extractionOf(compilation, program, run, stop)
        (extracted, blockCompilation.blocks(extracted))
      }
      if blocks.isEmpty then (None, Some(output), steps :+ extraction)
      else
        // FIXME: the blocks are compiled without their debugging attributes: the route has no source map https://github.com/Atry/private-overlay/issues/1969
        // of the program it extracts. The generic entry reads its program as a de Bruijn term, and no map of the
        // extracted program reaches here. Once the extraction carries the program's map,
        // pass `DebugAttributes.Written(maps of blockCompilation.locatedBlocks(output, map), texts)`.
        val (compiled, compilationStep) = timed("block_compilation")(blockCompilation.compiled(blocks, DebugAttributes.Omitted, stop))
        compiled match
          case Left(_) => (None, Some(output), steps ++ Vector(extraction, compilationStep))
          case Right(programs) =>
            val (values, running) = timed("block_run")(blockValues(blocks, programs, stop))
            values match
              case None => (None, Some(output), steps ++ Vector(extraction, compilationStep, running))
              case Some(computed) =>
                (
                  Some(
                    (
                      substituted(output, computed, index.noinline),
                      if explained then nativeCommands(output, computed, index.noinline) else Vector.empty
                    )
                  ),
                  Some(output),
                  steps ++ Vector(extraction, compilationStep, running)
                )

  /** Each block's numeral, its program run under `stop`, in order; nothing
    * from the first run `stop` stopped, the blocks after it not run. A run
    * gives nothing only when `stop` asked for a stop (`NarrowBlockProgram.run`),
    * so nothing under a signal that asks for none is a defect of the
    * generated class and throws.
    */
  private def blockValues[C <: NativeSpecializer & Singleton](
      blocks: Vector[Configured[C]],
      programs: Vector[NarrowBlockProgram],
      stop: StopSignal
  )(using C): Option[Map[Configured[C], Configured[C]]] =
    blocks.zip(programs).foldLeft(Option(Map.empty[Configured[C], Configured[C]])) {
      case (None, _) => None
      case (Some(found), (block, compiled)) =>
        compiled.run(stop) match
          case Some(value) => Some(found.updated(block, numeral(BigInt(value))))
          case None =>
            if !stop.stopRequested then
              throw IllegalStateException(s"a narrow block's run gave no value with no stop asked: $block")
            None
    }

  /** The value of `body` and the step of the name with the nanoseconds it
    * took, read with `System.nanoTime` before and after `body`, as the
    * contest entry's `Phase.timed` reads a phase.
    *
    * Timed by hand, not by JMH: the contest judge's reading of a point is
    * not a benchmark (it reads each point once, by its wall time, with no
    * warm-up), and an entry reports these steps as phases of that reading.
    */
  private[narrowblocks] def timed[A](name: String)(body: => A): (A, (String, Long)) =
    val start = System.nanoTime
    val value = body
    (value, (name, System.nanoTime - start))

  /** The canonical binary natural of the number: zero λz.λe.λo. z, 2h
    * λz.λe.λo. e h for h positive, 2h + 1 λz.λe.λo. o h.
    */
  private[narrowblocks] def numeral[C <: NativeSpecializer & Singleton](number: BigInt)(using C): Configured[C] =
    require(number >= 0, s"a natural is not negative: $number")
    def term(value: BigInt): Term =
      if value == 0 then λ(zero => λ(_ => λ(_ => zero)))
      else if value.testBit(0) then λ(_ => λ(_ => λ(odd => odd(term(value >> 1)))))
      else λ(_ => λ(even => λ(_ => even(term(value >> 1)))))
    // A numeral holds no parallel at the level of instructions, so it is its own spelling under every configuration.
    Configured.fromPure(summon[C]: C)(Defunctionalization.pure(term(number).deBruijnTerm(Map.empty)))

  /** The trace's commands (`native`) that put each subterm of `values` in the term
    * at each of its positions, outermost first in preorder, so that the
    * term's replay through them is `substituted(term, values, names)`: one
    * `Native` command for each occurrence, none under a name of `names` or
    * an opaque instruction, nor under an occurrence. The occurrences are
    * disjoint, so a command's position is the same before and after the
    * commands before it.
    */
  private[narrowblocks] def nativeCommands[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      values: Map[Configured[C], Configured[C]],
      names: Set[Configured[C]]
  )(using C): Vector[TraceCommand[C]] =
    def commands(instruction: Configured[C], position: Vector[PositionSegment]): Vector[TraceCommand[C]] =
      values.get(instruction) match
        case Some(value) => Vector(TraceCommand.Native(position, value))
        case None if instruction.heldAsLeaf || names.contains(instruction) => Vector.empty
        case None =>
          val layer = instruction.layer
          layer.children.zip(childRoles(layer)).flatMap((child, role) => commands(child, position :+ role))
    commands(term, Vector.empty)

  /** The role of each child of the layer, in the order of its children: a thunk's fillings by number, an
    * application's function and argument, a choice's or a parallel's sides; none for a leaf, a storage's view not
    * read.
    */
  private def childRoles(layer: gezi.ir.IrLayer[Any]): Vector[PositionSegment] = layer match
    case gezi.ir.Thunk(_, _, fillings)                   => fillings.indices.map(PositionSegment.Filling(_)).toVector
    case gezi.ir.Apply(_, _)                             => Vector(PositionSegment.Function, PositionSegment.Argument)
    case gezi.ir.Choice(_, _) | gezi.ir.Parallel(_, _)   => Vector(PositionSegment.Left, PositionSegment.Right)
    case gezi.ir.UriNode(_) | gezi.ir.Opaque(_) | (_: gezi.ir.NativeStorage) => Vector.empty

  /** The term with each subterm of `values` replaced by its value, rebuilt
    * from the leaves up, each subterm once; a name of `names`, or an opaque
    * instruction, kept as it is.
    */
  private[narrowblocks] def substituted[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      values: Map[Configured[C], Configured[C]],
      names: Set[Configured[C]]
  )(using specializer: C): Configured[C] =
    @scala.annotation.tailrec
    def rebuilt(pending: List[(Configured[C], Boolean)], made: Map[Configured[C], Configured[C]]): Map[Configured[C], Configured[C]] =
      pending match
        case Nil                                                    => made
        case (instruction, _) :: rest if made.contains(instruction) => rebuilt(rest, made)
        case (instruction, _) :: rest if values.contains(instruction) =>
          rebuilt(rest, made.updated(instruction, values(instruction)))
        case (instruction, _) :: rest if instruction.heldAsLeaf || names.contains(instruction) =>
          rebuilt(rest, made.updated(instruction, instruction))
        case (instruction, false) :: rest =>
          rebuilt(instruction.layer.children.toList.map((_, false)) ::: (instruction, true) :: rest, made)
        case (instruction, true) :: rest =>
          val built = instruction.layer match
            case gezi.ir.Apply(function, argument) => specializer.application(made(function), made(argument))
            case gezi.ir.Parallel(left, right)     => specializer.parallel(made(left), made(right))
            case gezi.ir.Choice(left, right)       => specializer.choice(made(left), made(right))
            case gezi.ir.Thunk(code, holes, fillings) =>
              gezi.ir.NonEmptyHoles.of(holes) match
                case Some(present) => specializer.thunk(code, present, fillings.map(made))
                case None => specializer.instance(code, fillings.map(made))
            case _ => instruction
          rebuilt(rest, made.updated(instruction, built))
    rebuilt(List((term, false)), Map.empty)(term)
