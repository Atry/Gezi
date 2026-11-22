package gezi.backendcomparison

import gezi.ematching.indexing.Indexing
import gezi.orientation.Orientations
import gezi.ematching.Backend
import gezi.ematching.CompiledProgram
import gezi.ematching.Program
import gezi.orientation.Orientation
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Store

/** What a run of the saturation reads: the store, the orientations, the
  * pattern instructions, the inputs and the budget.
  */
final case class RunInput(
    store: Store,
    orientations: Vector[Orientation],
    patternInstructions: Vector[Instruction],
    inputs: Vector[Instruction],
    budget: Int
):
  /** The codes the run may meet (`Indexing.codesMet`). */
  def codes: Set[Code] = Indexing.codesMet(orientations, patternInstructions ++ inputs)

/** A run's input compiled: its program, the program as the backend compiled
  * it, and the head arity bounds of its orientations.
  */
final case class Compiled(
    input: RunInput,
    program: Program,
    compiled: CompiledProgram,
    headArityBounds: Map[Instruction, Int]
)

object Compiled:
  /** The input compiled by the index and by the default backend
    * (`Backends.defaultName`, closure compilation), for callers that choose
    * none.
    */
  def of(input: RunInput): Compiled = of(input, Backends.named(Backends.defaultName))

  /** The input compiled by the index and by the backend. */
  def of(input: RunInput, backend: Backend): Compiled =
    val program = Indexing.program(input.orientations, input.codes)
    Compiled(
      input,
      program,
      backend.compiled(program),
      Orientations.headArityBounds(input.orientations)
    )
