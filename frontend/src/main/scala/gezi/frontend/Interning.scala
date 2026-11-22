package gezi.frontend

import gezi.ir.Instruction
import gezi.ir.Layer

/** The counted interning of a layer. An instruction is the canonical object
  * of its layer and a code of its code layer (`gezi.ir.Instruction`), so
  * interning needs no table threaded through.
  */
object Interning:

  /** The instruction of the layer, with the count of one operation, the interning.
    */
  def layerInternedCounted(layer: Layer[Instruction]): Counted[Instruction] =
    Counted(Instruction(layer), 1L)
