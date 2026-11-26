package gezi.rewritetrace

import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.Thunk
import scala.annotation.tailrec
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A term being rewritten step by step (`gezi.proofs.RewriteTrace`'s
  * plan, `Trace.replayedCommands`): a node off the
  * steps' paths settled, an interned instruction, and a node on them rebuilt
  * over the nodes below it and not interned, so that a step costs the depth
  * of its position and the logarithm of the widths on its path, not those
  * widths: a settled node turns into a rebuilt one, at the cost of its width,
  * only the first time a step's path crosses it.
  */
enum Spine:
  case Settled(instruction: Instruction)
  case Rebuilt(layer: Layer[Spine])

object Spine:

  /** The index among a layer's children (`Layer.children`) of the subterm at
    * the segment: function and left first, argument and right second, a
    * thunk's fillings in order.
    */
  private def childIndex(segment: PositionSegment): Int = segment match
    case PositionSegment.Function | PositionSegment.Left       => 0
    case PositionSegment.Argument | PositionSegment.Right      => 1
    case PositionSegment.Filling(index)                        => index

  /** The node one segment below. Throws `IllegalArgumentException` when the
    * node has no subterm there.
    */
  private def child(spine: Spine, segment: PositionSegment): Spine =
    val index = childIndex(segment)
    spine match
      case Settled(instruction) =>
        Settled(
          instruction.layered.children
            .lift(index)
            .getOrElse(throw IllegalArgumentException(s"$instruction has no subterm at $segment"))
        )
      case Rebuilt(layer) =>
        layer.children.lift(index).getOrElse(throw IllegalArgumentException(s"a rebuilt node has no subterm at $segment"))

  /** The node at the position. */
  def subterm(spine: Spine, position: Vector[PositionSegment]): Spine = position.foldLeft(spine)(child)

  /** The term with the subterm at the position replaced, the nodes on the
    * path rebuilt, none interned.
    */
  def replaced(spine: Spine, position: Vector[PositionSegment], replacement: Instruction): Spine =
    val ancestors = position.scanLeft(spine)(child)
    position.indices.foldRight(Settled(replacement): Spine)((place, inner) =>
      val layer = ancestors(place) match
        case Settled(instruction) => instruction.layered.map(Settled(_): Spine)
        case Rebuilt(rebuilt)      => rebuilt
      Rebuilt(layer.over(layer.children.updated(childIndex(position(place)), inner)))
    )

  /** The interned term of the node, its rebuilt nodes interned bottom up. A
    * trampoline: a rebuilt region is as deep as the positions of the steps.
    */
  def materialized(spine: Spine): Instruction = materializedStep(spine).result

  private def materializedStep(spine: Spine): TailRec[Instruction] = spine match
    case Settled(instruction) => done(instruction)
    case Rebuilt(layer) =>
      TailRecFolds.folded(layer.children.toVector, Vector.empty[Instruction])((found, node) => materializedStep(node).map(found :+ _))
        .map(children => Instruction(layer.over(children)))

  /** The positions in the term's replay spelling of the subterm at the
    * position (`ReplaySpelling.positions`), read along the path: a thunk on
    * it that is its own spelling passes its filling's segment on, and one
    * that is not passes on the positions of the filling's placeholder in its
    * spelling (`ReplaySpelling.fillingPositions`), several when the spelling
    * copies the filling. The filling positions of each code, holes and number
    * of fillings are computed once, in the spellings `known`, which are
    * returned with the positions: computing them costs the code's size, which a program's
    * top-level thunk has as many slots as its fillings, so that computed at
    * every step under it they made the flattening quadratic. A step costs its
    * position's depth, apart from the first time a kind of thunk is met.
    */
  def spelledPositions(
      spine: Spine,
      position: Vector[PositionSegment],
      known: Spellings
  ): (Vector[Vector[PositionSegment]], Spellings) =
    @tailrec
    def walked(
        pending: List[(Spine, Vector[PositionSegment], Vector[PositionSegment])],
        found: Vector[Vector[PositionSegment]],
        known: Spellings
    ): (Vector[Vector[PositionSegment]], Spellings) =
      pending match
        case Nil => (found, known)
        case (at, rest, prefix) :: others =>
          rest.headOption match
            case None => walked(others, found :+ prefix, known)
            case Some(segment) =>
              val kind = at match
                case Settled(instruction) =>
                  instruction.layered match
                    case Thunk(code, holes, fillings) => Some((code, holes, fillings.size))
                    case _                            => None
                case Rebuilt(Thunk(code, holes, fillings)) => Some((code, holes, fillings.size))
                case Rebuilt(_)                            => None
              val (placed, knownAfter) = kind match
                case None                              => (None, known)
                case Some((code, holes, fillingCount)) => known.fillingPositions(code, holes, fillingCount)
              val below = child(at, segment)
              val next = placed match
                case None => List((below, rest.tail, prefix :+ segment))
                case Some(byPlace) =>
                  segment match
                    case PositionSegment.Filling(place) =>
                      byPlace(place).toList.map(spelled => (below, rest.tail, prefix ++ spelled))
                    case other => throw IllegalArgumentException(s"a thunk has no subterm $other")
              walked(next ++ others, found, knownAfter)
    walked(List((spine, position, Vector.empty)), Vector.empty, known)
