package gezi.backendcomparison

import gezi.ematching.indexing.Indexing
import gezi.orientation.Orientations
import gezi.ematching.Backend
import gezi.ematching.CompiledProgram
import gezi.ematching.Program
import gezi.orientation.Orientation
import gezi.ir.Code
import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.Store

/** What a run of the saturation reads: the store, the orientations, the pattern
  * instructions, the inputs and the budget.
  */
final case class RunInput[C <: NativeSpecializer & Singleton](
    store: Store[C],
    orientations: Vector[Orientation[C]],
    patternInstructions: Vector[Configured[C]],
    inputs: Vector[Configured[C]],
    budget: Int
):
  /** The codes the run may meet (`Indexing.codesMet`). */
  def codes(using C): Set[Code] =
    Indexing.codesMet(orientations, patternInstructions ++ inputs)

/** A run's input compiled: its program, the program as the backend compiled it,
  * and the head arity bounds of its orientations.
  */
final case class Compiled[C <: NativeSpecializer & Singleton](
    input: RunInput[C],
    program: Program[C],
    compiled: CompiledProgram[C],
    headArityBounds: Map[Configured[C], Int]
)

object Compiled:
  /** The input compiled by the index and by the default backend
    * (`Backends.defaultName`, closure compilation), for callers that choose
    * none.
    */
  def of[C <: NativeSpecializer & Singleton](input: RunInput[C])(using
      C
  ): Compiled[C] = of(input, Backends.named(Backends.defaultName))

  /** The input compiled by the index and by the backend. */
  def of[C <: NativeSpecializer & Singleton](
      input: RunInput[C],
      backend: Backend
  )(using C): Compiled[C] =
    val program = Indexing.program(input.orientations, input.codes)
    Compiled(
      input,
      program,
      backend.compiled(program),
      Orientations.headArityBounds(input.orientations)
    )
