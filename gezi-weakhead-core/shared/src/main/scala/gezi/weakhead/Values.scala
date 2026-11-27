package gezi.weakhead

import gezi.ir.ConstructorIdentity
import gezi.ir.{Configured, NativeSpecializer, Value}

/** The conversions between the instructions of the IR and the evaluator's
  * values. Every term is interned in one pool, and the IR's layers are among a
  * value's, so an instruction is a value as it is, and a value with no neutral
  * value anywhere in it is the instruction it spells, the same object.
  */
object Values:

  /** The value of a closed instruction: the instruction itself. The names are
    * no longer read: a name and the tree it was written as are one interned
    * term.
    */
  def ofInstruction[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      names: Set[Configured[C]]
  )(using C): Value[C] =
    Value.of(instruction)

  /** The instruction a value stands for: the value itself, checked to hold no
    * neutral value (`ConstructorIdentity.isInstruction`, one field read).
    * Throws `IllegalArgumentException` for a value that holds one, which is no
    * part of an instruction.
    */
  def instruction[C <: NativeSpecializer & Singleton](
      value: Value[C]
  )(using C): Configured[C] =
    gezi.ir.Closed
      .configured(value)
      .getOrElse(
        throw IllegalArgumentException(
          "a value holding a neutral value or a suspension is no term of the IR"
        )
      )
