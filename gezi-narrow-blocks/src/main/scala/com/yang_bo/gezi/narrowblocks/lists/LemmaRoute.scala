package com.yang_bo.gezi.narrowblocks

/** The opt-in copy of the narrow blocks with lists and booleans
  * ([[com.yang_bo.gezi.narrowblocks.lists]]), selected by
  * `ExtractorImplementation.NarrowListBlock`.
  */
package lists

import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Literals
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.narrowblocks.LemmaRoute.nativeCommands
import com.yang_bo.gezi.narrowblocks.LemmaRoute.numeral
import com.yang_bo.gezi.narrowblocks.LemmaRoute.stopped
import com.yang_bo.gezi.narrowblocks.LemmaRoute.substituted
import com.yang_bo.gezi.narrowblocks.LemmaRoute.timed
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.jit.NaturalLattice
import com.yang_bo.gezi.rewritetrace.TraceCommand
import com.yang_bo.gezi.saturation.Run
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.Compression
import com.yang_bo.gezi.strategies.NormalityModule

/** The copy's lemma route: the parent's (`com.yang_bo.gezi.narrowblocks.LemmaRoute`), the
  * rounds saturated by the parent's `saturatedRounds`, with this package's
  * narrow blocks (`NarrowBlockOrder`, `NarrowBlockCompilation`) and a block
  * that gives no value read as no program rather than as a defect
  * (`blockValues`). `declaredRecords` is whether its blocks also decode lists
  * of records of declared data families (`NarrowBlockCompilation`).
  */
class ListBlockRoute(declaredRecords: Boolean) extends NarrowBlockRoute:

  /** The copy's narrow blocks over the natives first, then the size. */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: com.yang_bo.gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] =
    Vector(NarrowBlockOrder(natives, configuration), Compression.at[C])

  /** The parent's `compiledRounds`, its blocks those of this package. */
  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: com.yang_bo.gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C] =
    val (run, steps, saturations) = com.yang_bo.gezi.narrowblocks.LemmaRoute
      .saturatedRounds(rounds, program, explained, stop)
    val (computed, extracted, allSteps) = blocksComputed(
      index,
      rounds.last,
      natives,
      program,
      run,
      steps,
      explained,
      stop
    )
    LemmaRoundsResult(
      computed.map(_._1),
      extracted,
      allSteps,
      saturations,
      run.graph,
      computed.fold(Vector.empty[TraceCommand[C]])(_._2)
    )

  /** After a saturation: nothing more when it was stopped; otherwise the
    * extraction by `compilation`, its narrow blocks compiled to bytecode
    * (`NarrowBlockCompilation` with `natives`) and run under `stop`, each
    * replaced by the canonical binary natural it computes. The program with its
    * blocks computed and the native commands that take the extraction to it
    * (only when `explained`, so that a scored reading pays nothing for them),
    * or nothing, as when a block does not compile, if `stop` stopped a block's
    * run or a block gave no value (`blockValues`); the extraction, or nothing;
    * and the steps, those given then `lemma_extraction`, `block_compilation`
    * and `block_run`, as far as it got.
    *
    * FIXME: after the last round each block is evaluated eagerly
    * https://github.com/Atry/private-overlay/issues/2032 to its end at compile
    * time and substituted back as a numeral; when to evaluate a block and the
    * representation of its value are fixed here. Each is to become an option of
    * one interface chosen by configuration (entry data and `Defaults`).
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
  )(using
      C
  ): (
      Option[(Configured[C], Vector[TraceCommand[C]])],
      Option[Configured[C]],
      Vector[(String, Long)]
  ) =
    if stopped(run.end) then (None, None, steps)
    else
      val blockCompilation =
        NarrowBlockCompilation(
          index,
          natives,
          com.yang_bo.gezi.narrowblocks.LemmaRoute.readingConfiguration(run),
          declaredRecords
        )
      val ((output, blocks), extraction) = timed("lemma_extraction") {
        val extracted = compilation.extracted(program, run, stop)
        (extracted, blockCompilation.blocks(extracted))
      }
      if blocks.isEmpty then (None, Some(output), steps :+ extraction)
      else
        // FIXME: the blocks are compiled without their debugging attributes: the route has no source map https://github.com/Atry/private-overlay/issues/1969
        // of the program it extracts. The generic entry reads its program as a de Bruijn term, and no map of the
        // extracted program reaches here. Once the extraction carries the program's map,
        // pass `DebugAttributes.Written(maps of blockCompilation.locatedBlocks(output, map), texts)`.
        val (compiled, compilationStep) = timed("block_compilation")(
          blockCompilation.compiled(blocks, DebugAttributes.Omitted, stop)
        )
        compiled match
          case Left(_) =>
            (None, Some(output), steps ++ Vector(extraction, compilationStep))
          case Right(programs) =>
            val (values, running) = timed("block_run")(
              blockValues(blockCompilation, blocks, programs, stop)
            )
            values match
              case None =>
                (
                  None,
                  Some(output),
                  steps ++ Vector(extraction, compilationStep, running)
                )
              // A native command states an equation, and a block replaced by `top` is an approximation from
              // above: a trace reads the extraction instead.
              case Some(computed) if explained && computed.notNumerals =>
                (
                  None,
                  Some(output),
                  steps ++ Vector(extraction, compilationStep, running)
                )
              case Some(computed) =>
                (
                  Some(
                    (
                      substituted(output, computed.values, index.noinline),
                      if explained then
                        nativeCommands(output, computed.values, index.noinline)
                      else Vector.empty
                    )
                  ),
                  Some(output),
                  steps ++ Vector(extraction, compilationStep, running)
                )

  /** The term a block whose root native found its term ≃_O `top` is replaced by
    * (`com.yang_bo.gezi.jit.StaticBlockResult.NaturalOrNoAnswer`): `top` itself, from the
    * front end, so that it depends on no reading state's list of known
    * extremes.
    */
  private val noAnswerTerm: Pure = Defunctionalization.pure(Literals.top)

  /** The IR term of a native's term over naturals: its numerals the canonical
    * binary naturals, a choice nested to the right in the members' order, a
    * parallel of the two sides. Stack-safe over a long choice: the members are
    * folded from the last; a nesting of choices and parallels as deep as the
    * native builds is recursed into.
    */
  private def latticeTerm[C <: NativeSpecializer & Singleton](
      lattice: NaturalLattice
  )(using specializer: C): Configured[C] = lattice match
    case NaturalLattice.Numeral(value)  => numeral(BigInt(value))
    case NaturalLattice.Choice(members) =>
      val (last, others) = members.lastOption
        .map(last => (last, members.init))
        .getOrElse(
          throw IllegalStateException(
            "a native's term over naturals holds an empty choice"
          )
        )
      others.foldRight(latticeTerm(last))((member, right) =>
        specializer.choice(latticeTerm(member), right)
      )
    case NaturalLattice.Parallel(left, right) =>
      specializer.parallel(latticeTerm(left), latticeTerm(right))

  /** What the blocks' runs gave: each block's term, a numeral, `noAnswerTerm`,
    * the term over naturals of a native (`latticeTerm`) or a value of a
    * declared family, and whether any is not a numeral, for which a native
    * command of a trace states no equation.
    */
  private final case class BlockValues[C <: NativeSpecializer & Singleton](
      values: Map[Configured[C], Configured[C]],
      notNumerals: Boolean
  )

  /** Each block's term, its program run under `stop`, in order; nothing from
    * the first run that gave nothing, the blocks after it not run. A run gives
    * nothing when `stop` asked for a stop or when the block gives no value, a
    * value read in a representation it does not have (a list as a natural, a
    * natural as a list or another value as a boolean)
    * (`NarrowBlockProgram.outcome`): the route then gives no program, as when a
    * block does not compile, and its caller reads the extraction, its blocks
    * not computed (`ProgramCompiler.compiledProgram`), which adds no answer. A
    * block whose root native found its term ≃_O `top` is `noAnswerTerm`, and
    * one whose root native gave the term over naturals its term is ≃_O to is
    * that term (`latticeTerm`): each stands for the block's term in every
    * context, so neither loses an answer.
    *
    * FIXME (found in a review, 2026-11-21;
    * https://github.com/Atry/private-overlay/issues/1538): one block that gives
    * no value makes the route give no program, so the blocks that did compute
    * are lost with it, and the reader reads every one of them again. The loss
    * adds no answer but costs the whole program's blocks for one block's
    * misfit. Candidate fix: substitute the blocks that gave a value and leave
    * the others as the extraction wrote them, which the reader then reads;
    * their values are independent, each a closed natural.
    */
  private def blockValues[C <: NativeSpecializer & Singleton](
      blockCompilation: NarrowBlockCompilation[C],
      blocks: Vector[Configured[C]],
      programs: Vector[NarrowBlockProgram],
      stop: StopSignal
  )(using C): Option[BlockValues[C]] =
    blocks.zip(programs).foldLeft(Option(BlockValues[C](Map.empty, false))) {
      case (None, _)                        => None
      case (Some(found), (block, compiled)) =>
        compiled.outcome(stop) match
          case NarrowBlockOutcome.Computed(value) =>
            Some(
              found.copy(values =
                found.values.updated(block, numeral(BigInt(value)))
              )
            )
          case NarrowBlockOutcome.NoAnswer =>
            Some(
              BlockValues(
                found.values.updated(
                  block,
                  Configured.fromPure(summon[C]: C)(noAnswerTerm)
                ),
                true
              )
            )
          case NarrowBlockOutcome.Lattice(lattice) =>
            Some(
              BlockValues(
                found.values.updated(block, latticeTerm(lattice)),
                true
              )
            )
          case NarrowBlockOutcome.Constructed(value) =>
            blockCompilation
              .constructedTerm(block, value)
              .map(term => BlockValues(found.values.updated(block, term), true))
          case NarrowBlockOutcome.NoValue => None
    }

/** The route of the extractor `narrow_list_block`: lists of naturals, no
  * declared family.
  */
object LemmaRoute extends ListBlockRoute(false)

/** The opt-in route whose blocks also read lists of records of declared data
  * families, selected by an entry through an extractor module. It differs from
  * `LemmaRoute` only at a native's `NativePlace.NaturalRecordList`.
  */
object DeclaredFamilyRoute extends ListBlockRoute(true)
