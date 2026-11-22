package gezi.weakhead

import gezi.ir.ConstructorIdentity
import gezi.ir.Instruction

/** The conversions between the instructions of the IR and the evaluator's
  * values. Every term is interned in one pool, and the IR's layers are among
  * a value's, so an instruction is a value as it is, and a value with no
  * neutral value anywhere in it is the instruction it spells, the same
  * object.
  */
object Values:

  /** The value of a closed instruction: the instruction itself. The names
    * are no longer read: a name and the tree it was written as are one
    * interned term.
    */
  def ofInstruction(instruction: Instruction, names: Set[Instruction]): Value = instruction

  /** The instruction a value stands for: the value itself, checked to hold
    * no neutral value (`ConstructorIdentity.isInstruction`, one field read).
    * Throws `IllegalArgumentException` for a value that holds one, which is
    * no part of an instruction.
    */
  def instruction(value: Value): Instruction =
    if !ConstructorIdentity.isInstruction(value) then
      throw IllegalArgumentException("a neutral value is no part of an instruction")
    // Sound: one pool interns both, and a value made of the IR's
    // constructors only is an instruction.
    value.asInstanceOf[Instruction]
