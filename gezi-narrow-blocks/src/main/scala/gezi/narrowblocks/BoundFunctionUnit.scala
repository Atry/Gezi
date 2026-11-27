package gezi.narrowblocks

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.{Configured, NativeSpecializer}

/** The unit of a program whose compilation is kept across the points of a
  * family: the function a top-level let binds, and the most arguments the let's
  * body applies it to.
  *
  * The cut is one mechanical rule on the program's structure, and reads no
  * name, no library term and no shape of a value. The program is a let,
  * `(λf. B) F`: an application whose function is a thunk with one bound hole
  * and whose argument is F. Every instruction is closed, so F is a closed term.
  * The unit is F. Its arity is the most arguments any occurrence of f in B is
  * applied to, f being the slot of the hole: an occurrence at the head of an
  * application spine counts its arguments, and an occurrence passed whole as a
  * filling of an inner thunk is followed into that thunk's code, where it is
  * the slot that filling fills. A bare occurrence anywhere else (an argument,
  * `g f`, or an operand of a choice or a parallel) hands the function on and
  * counts nothing. A program of any other shape, or whose f is never applied,
  * has no unit.
  *
  * Why the arity: the unit is compiled applied to that many fresh parameters,
  * so that every site of the body that applies f to its arguments reads the
  * compiled function at its full arity.
  */
final case class BoundFunctionUnit[C <: NativeSpecializer & Singleton](
    function: Configured[C],
    arity: Int
):
  require(arity > 0, s"a unit is applied to at least one argument: $arity")

object BoundFunctionUnit:

  /** The program's unit, none for a program that is no let of a function its
    * body applies.
    */
  def of[C <: NativeSpecializer & Singleton](
      program: Configured[C]
  ): Option[BoundFunctionUnit[C]] = program.layer match
    case gezi.ir.Apply(function, argument) =>
      function.layer match
        case gezi.ir.Thunk(code, Vector(Hole.Bound(slot)), _) =>
          Some(applications(code, slot))
            .filter(_ > 0)
            .map(BoundFunctionUnit(argument, _))
        case _ => None
    case _ => None

  /** The most arguments the code applies its slot to, as `of` counts them: zero
    * when the code applies it to none.
    */
  def applications(code: Code, slot: Int): Int =
    @scala.annotation.tailrec
    def spine(current: Code, arguments: List[Code]): (Code, List[Code]) =
      current.layer match
        case gezi.ir.Apply(function, argument) =>
          spine(function, argument :: arguments)
        case _ => (current, arguments)
    @scala.annotation.tailrec
    def most(pending: List[(Code, Int)], found: Int): Int = pending match
      case Nil                     => found
      case (current, read) :: rest =>
        current.layer match
          case gezi.ir.Apply(_, _) =>
            val (head, arguments) = spine(current, Nil)
            val atHead = head.layer match
              case gezi.ir.Slot(`read`) => arguments.size
              case _                    => 0
            val headPending = head.layer match
              case gezi.ir.Slot(_) => Nil
              case _               => List((head, read))
            most(
              headPending ::: arguments.map((_, read)) ::: rest,
              found max atHead
            )
          case gezi.ir.Thunk(inner, holes, fillings) =>
            val passedOn =
              filledSlots(holes, fillings.size).zip(fillings).collect {
                case (innerSlot, filling)
                    if filling.layer == gezi.ir.Slot(read) =>
                  (inner, innerSlot)
              }
            most(
              passedOn.toList ::: fillings.map((_, read)).toList ::: rest,
              found
            )
          case gezi.ir.Parallel(left, right) =>
            most((left, read) :: (right, read) :: rest, found)
          case gezi.ir.Choice(left, right) =>
            most((left, read) :: (right, read) :: rest, found)
          case _ => most(rest, found)
    most(List((code, slot)), 0)

  /** The slots of a thunk's code its fillings fill, in filling order: every
    * slot from 0 that no hole binds, in slot order (`Saturation.slotValues`).
    */
  private def filledSlots(holes: Vector[Hole], fillingCount: Int): Vector[Int] =
    val bound = holes.collect { case Hole.Bound(slot) => slot }.toSet
    (0 until bound.size + fillingCount).filterNot(bound).toVector
