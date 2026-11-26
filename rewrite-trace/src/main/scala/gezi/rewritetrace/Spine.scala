package gezi.rewritetrace

import gezi.ir.Layer
import gezi.ir.NotTerm
import gezi.ir.StorageAccess
import gezi.ir.Thunk
import scala.annotation.tailrec
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Configured, NativeSpecializer}

/** A term being rewritten step by step (`gezi.proofs.RewriteTrace`'s
  * plan, `Trace.replayedCommands`): a node off the
  * steps' paths settled, a term of the trace's configuration, and a node on
  * them rebuilt over the nodes below it and not built, so that a step costs
  * the depth of its position and the logarithm of the widths on its path, not
  * those widths: a settled node turns into a rebuilt one, at the cost of its
  * width, only the first time a step's path crosses it. A settled storage is
  * read through its view (`Positions.layerOf`).
  */
enum Spine[C <: NativeSpecializer & Singleton]:
  case Settled(term: Configured[C])
  case Rebuilt(layer: Layer[Spine[C]])

object Spine:

  /** A node of a spine is no IR term: a layer over nodes is a layer of the spine's. */
  given [C <: NativeSpecializer & Singleton]: NotTerm[Spine[C]] = NotTerm.granted

  /** The node one segment below. Throws `IllegalArgumentException` when the
    * node has no subterm there.
    */
  private def child[C <: NativeSpecializer & Singleton](spine: Spine[C], segment: PositionSegment)(using C, StorageAccess): Spine[C] =
    spine match
      case Settled(term) => Settled(Positions.childAt(term, segment))
      case Rebuilt(layer) =>
        layer.children
          .lift(Positions.childIndex(segment))
          .getOrElse(throw IllegalArgumentException(s"a rebuilt node has no subterm at $segment"))

  /** The node at the position. */
  def subterm[C <: NativeSpecializer & Singleton](spine: Spine[C], position: Vector[PositionSegment])(using C, StorageAccess): Spine[C] =
    position.foldLeft(spine)(child)

  /** The term with the subterm at the position replaced, the nodes on the
    * path rebuilt, none built.
    */
  def replaced[C <: NativeSpecializer & Singleton](spine: Spine[C], position: Vector[PositionSegment], replacement: Configured[C])(using C, StorageAccess): Spine[C] =
    val ancestors = position.scanLeft(spine)(child)
    position.indices.foldRight(Settled(replacement): Spine[C])((place, inner) =>
      val layer: Layer[Spine[C]] = ancestors(place) match
        case Settled(term)    => Positions.layerOf(term).map(Settled(_): Spine[C])
        case Rebuilt(rebuilt) => rebuilt
      Rebuilt(layer.over(layer.children.updated(Positions.childIndex(position(place)), inner)))
    )

  /** The term of the node, its rebuilt nodes built bottom up through the
    * configuration (`Positions.built`). A trampoline: a rebuilt region is as
    * deep as the positions of the steps.
    */
  def materialized[C <: NativeSpecializer & Singleton](spine: Spine[C])(using C): Configured[C] = materializedStep(spine).result

  private def materializedStep[C <: NativeSpecializer & Singleton](spine: Spine[C])(using C): TailRec[Configured[C]] = spine match
    case Settled(term) => done(term)
    case Rebuilt(layer) =>
      TailRecFolds
        .folded(layer.children.toVector, Vector.empty[Configured[C]])((found, node) => materializedStep(node).map(found :+ _))
        .map(children => Positions.built(layer, children))

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
  def spelledPositions[C <: NativeSpecializer & Singleton](
      spine: Spine[C],
      position: Vector[PositionSegment],
      known: Spellings[C]
  )(using C, StorageAccess): (Vector[Vector[PositionSegment]], Spellings[C]) =
    @tailrec
    def walked(
        pending: List[(Spine[C], Vector[PositionSegment], Vector[PositionSegment])],
        found: Vector[Vector[PositionSegment]],
        known: Spellings[C]
    ): (Vector[Vector[PositionSegment]], Spellings[C]) =
      pending match
        case Nil => (found, known)
        case (at, rest, prefix) :: others =>
          rest.headOption match
            case None => walked(others, found :+ prefix, known)
            case Some(segment) =>
              val kind = at match
                case Settled(term) =>
                  term.layer match
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
