package gezi.narrowblocks

/** The opt-in copy of the narrow blocks with lists and booleans ([[gezi.narrowblocks.lists]]), selected by `ExtractorImplementation.NarrowListBlock`. */
package lists

import gezi.ir.Instruction
import gezi.narrowblocks.LemmaRoute.nativeCommands
import gezi.narrowblocks.LemmaRoute.numeral
import gezi.narrowblocks.LemmaRoute.stopped
import gezi.narrowblocks.LemmaRoute.substituted
import gezi.narrowblocks.LemmaRoute.timed
import gezi.jit.NativeBackend
import gezi.rewritetrace.TraceCommand
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.Compression
import gezi.strategies.NormalityModule

/** The copy's lemma route: the parent's (`gezi.narrowblocks.LemmaRoute`),
  * the rounds saturated by the parent's `saturatedRounds`, with this
  * package's narrow blocks (`NarrowBlockOrder`, `NarrowBlockCompilation`)
  * and a block that gives no value read as no program rather than as a
  * defect (`blockValues`).
  */
object LemmaRoute extends NarrowBlockRoute:

  /** The copy's narrow blocks over the natives first, then the size. */
  def extractorModules(natives: NativeBackend): Vector[NormalityModule] = Vector(NarrowBlockOrder(natives), Compression)

  /** The parent's `compiledRounds`, its blocks those of this package. */
  def compiledRounds(
      index: StandardLibraryIndex,
      rounds: Vector[PreparedLemmaCompilation],
      natives: NativeBackend,
      program: Instruction,
      explained: Boolean,
      stop: StopSignal
  ): LemmaRoundsResult =
    val (run, steps, saturations) = gezi.narrowblocks.LemmaRoute.saturatedRounds(rounds, program, explained, stop)
    val (computed, extracted, allSteps) = blocksComputed(index, rounds.last, natives, program, run, steps, explained, stop)
    LemmaRoundsResult(
      computed.map(_._1),
      extracted,
      allSteps,
      saturations,
      run.graph,
      computed.fold(Vector.empty[TraceCommand])(_._2)
    )

  /** After a saturation: nothing more when it was stopped; otherwise the
    * extraction by `compilation`, its narrow blocks compiled to bytecode
    * (`NarrowBlockCompilation` with `natives`) and run under `stop`, each
    * replaced by the canonical binary natural it computes. The program with
    * its blocks computed and the native commands that take the extraction to
    * it (only when `explained`, so that a scored reading pays nothing for
    * them), or nothing, as when a block does not compile, if `stop` stopped a
    * block's run or a block gave no value (`blockValues`); the extraction, or
    * nothing; and the steps, those given then
    * `lemma_extraction`, `block_compilation` and `block_run`, as far as it got.
    *
    * FIXME: after the last round each block is evaluated eagerly https://github.com/Atry/private-overlay/issues/2032
    * to its end at compile time and substituted back as a numeral; when to evaluate a block and the representation of
    * its value are fixed here. Each is to become an option of one interface chosen by configuration (entry data and
    * `Defaults`).
    */
  private def blocksComputed(
      index: StandardLibraryIndex,
      compilation: PreparedLemmaCompilation,
      natives: NativeBackend,
      program: Instruction,
      run: Run,
      steps: Vector[(String, Long)],
      explained: Boolean,
      stop: StopSignal
  ): (Option[(Instruction, Vector[TraceCommand])], Option[Instruction], Vector[(String, Long)]) =
    if stopped(run.end) then (None, None, steps)
    else
      val blockCompilation = NarrowBlockCompilation(index, natives)
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
    * from the first run that gave nothing, the blocks after it not run. A
    * run gives nothing when `stop` asked for a stop or when the block gives
    * no value, a value read in a representation it does not have (a list as
    * a natural, a natural as a list or another value as a boolean)
    * (`NarrowBlockProgram.run`): the
    * route then gives no program, as when a block does not compile, and its
    * caller reads the extraction, its blocks not computed
    * (`ProgramCompiler.compiledProgram`), which adds no answer.
    *
    * FIXME (found in a review, 2026-11-21; https://github.com/Atry/private-overlay/issues/1538):
    * one block that gives no value makes the route give no
    * program, so the blocks that did compute are lost with it, and the
    * reader reads every one of them again. The loss adds no answer but costs
    * the whole program's blocks for one block's misfit. Candidate fix:
    * substitute the blocks that gave a value and leave the others as the
    * extraction wrote them, which the reader then reads; their values are
    * independent, each a closed natural.
    */
  private def blockValues(
      blocks: Vector[Instruction],
      programs: Vector[NarrowBlockProgram],
      stop: StopSignal
  ): Option[Map[Instruction, Instruction]] =
    blocks.zip(programs).foldLeft(Option(Map.empty[Instruction, Instruction])) {
      case (None, _) => None
      case (Some(found), (block, compiled)) =>
        compiled.run(stop).map(value => found.updated(block, numeral(BigInt(value))))
    }
