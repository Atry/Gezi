package gezi.rewritetrace

import gezi.ir.Layer
import gezi.ir.NativeStorage
import gezi.ir.NonEmptyHoles
import gezi.ir.Opaque
import gezi.ir.StorageAccess
import gezi.ir.StorageView
import gezi.ir.UriNode
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}
import gezi.ir.{Configured, NativeSpecializer}

/** One step of a position: the role of a subterm in the layer above it. */
enum PositionSegment:
  case Function, Argument, Left, Right
  case Filling(index: Int)

/** Which side of the equation a step replaces: `Forward` replaces an instance
  * of the left side by the instance of the right side, `Backward` the right by
  * the left.
  */
enum RewriteDirection:
  case Forward, Backward

  def reversed: RewriteDirection = this match
    case Forward  => Backward
    case Backward => Forward

/** Where a variable of a step's equation occurs: its positions in the subterm
  * the step replaces and in the subterm it puts there, each from the root of
  * that subterm, the step's provenance mapping. The subterm at each position
  * before is the subterm at each position after: a position before and none
  * after is a subtree the step drops, several after a subtree it copies.
  */
final case class Provenance(
    variable: String,
    before: Vector[Vector[PositionSegment]],
    after: Vector[Vector[PositionSegment]]
):

  def turned: Provenance = Provenance(variable, after, before)

/** Positions in a term: the roles of a layer's subterms, and the subterm at a
  * position read or replaced. A trace reads a term one layer at a time: a
  * native storage, a leaf of its term's layer, is read as its one-layer view
  * `v ∥ T` (`NativeSpecializer.viewOf`), its two sides the parallel's, and a
  * layer rebuilt over new children is built through the trace's configuration,
  * so that the result may be a storage again, whose view the next segment
  * reads.
  */
object Positions:

  /** The one layer a trace reads of a term: an application, a parallel, a
    * choice, a thunk, or a storage's view.
    */
  type TraceLayer[+Child] = Apply[Child] | Parallel[Child] | Choice[Child] |
    Thunk[Child] | StorageView[Child]

  /** The term's one layer: a storage's its view. Throws `IllegalStateException`
    * for an opaque term, a URI node included, whose layer is no part of the IR.
    */
  def layerOf[C <: NativeSpecializer & Singleton](
      term: Configured[C]
  )(using specializer: C, access: StorageAccess): TraceLayer[Configured[C]] =
    term.layer match
      case storage: NativeStorage    => (specializer: C).viewOf(storage)
      case application @ Apply(_, _) => application
      case parallel @ Parallel(_, _) => parallel
      case choice @ Choice(_, _)     => choice
      case thunk @ Thunk(_, _, _)    => thunk
      case UriNode(_) | Opaque(_)    =>
        throw IllegalStateException(s"the $term has no layer")

  /** The term of the layer's shape over the children, as many as it has, built
    * through the configuration: a parallel, a storage's view included,
    * converted into its storage when it is the unique spelling of one, and a
    * thunk with no hole its code's body. Throws `IllegalArgumentException` for
    * children of another number.
    */
  def built[C <: NativeSpecializer & Singleton](
      layer: Layer[Any],
      children: Vector[Configured[C]]
  )(using specializer: C): Configured[C] =
    (layer, children) match
      case (Apply(_, _), Vector(function, argument)) =>
        specializer.application(function, argument)
      case (Parallel(_, _), Vector(left, right)) =>
        specializer.parallel(left, right)
      case (StorageView(_, _), Vector(value, criterion)) =>
        specializer.parallel(value, criterion)
      case (Choice(_, _), Vector(left, right)) =>
        specializer.choice(left, right)
      case (Thunk(code, holes, fillings), _)
          if fillings.size == children.size =>
        NonEmptyHoles.of(holes) match
          case Some(present) => specializer.thunk(code, present, children)
          case None          => specializer.instance(code, children)
      case _ =>
        throw IllegalArgumentException(
          s"the layer $layer has no layer over ${children.size} children"
        )

  /** The role of each subterm of the layer, in the order of `Layer.children`;
    * none for a noinline leaf. A storage's view is the parallel it stands for.
    */
  def roles(layer: Layer[Any]): Vector[PositionSegment] = layer match
    case Thunk(_, _, fillings) =>
      fillings.indices.map(PositionSegment.Filling(_)).toVector
    case Apply(_, _) =>
      Vector(PositionSegment.Function, PositionSegment.Argument)
    case Choice(_, _) | Parallel(_, _) | StorageView(_, _) =>
      Vector(PositionSegment.Left, PositionSegment.Right)
    case NoinlineLeaf(_) => Vector.empty

  /** The positions of the term where the subterm occurs, outermost first in
    * preorder; none under an occurrence and none under an opaque term.
    */
  def occurrences[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      subterm: Configured[C]
  )(using C, StorageAccess): Vector[Vector[PositionSegment]] =
    if Configured.same(term, subterm) then Vector(Vector.empty)
    else if term.opaque then Vector.empty
    else
      val layer = layerOf(term)
      layer.children
        .zip(roles(layer))
        .flatMap((child, role) => occurrences(child, subterm).map(role +: _))

  /** The subterm at the position. Throws `IllegalArgumentException` when the
    * term has no subterm there.
    */
  def subterm[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      position: Vector[PositionSegment]
  )(using C, StorageAccess): Configured[C] =
    position.foldLeft(term)(childAt)

  /** The term with the subterm at the position replaced. Throws
    * `IllegalArgumentException` when the term has no subterm there.
    */
  def replaced[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      position: Vector[PositionSegment],
      replacement: Configured[C]
  )(using C, StorageAccess): Configured[C] =
    val ancestors = position.scanLeft(term)(childAt)
    position.indices.foldRight(replacement)((place, inner) =>
      withChild(ancestors(place), position(place), inner)
    )

  /** The index among a layer's children (`Layer.children`) of the subterm at
    * the segment: function and left first, argument and right second, a thunk's
    * fillings in order.
    */
  def childIndex(segment: PositionSegment): Int = segment match
    case PositionSegment.Function | PositionSegment.Left  => 0
    case PositionSegment.Argument | PositionSegment.Right => 1
    case PositionSegment.Filling(index)                   => index

  /** The subterm at the segment. Throws `IllegalArgumentException` when the
    * term has no subterm there.
    */
  def childAt[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      segment: PositionSegment
  )(using C, StorageAccess): Configured[C] =
    if term.opaque then
      throw IllegalArgumentException(
        s"the opaque $term has no subterm $segment"
      )
    val layer = layerOf(term)
    Option
      .when(roles(layer).contains(segment))(layer.children(childIndex(segment)))
      .getOrElse(
        throw IllegalArgumentException(
          s"the layer $layer has no subterm $segment"
        )
      )

  private def withChild[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      segment: PositionSegment,
      child: Configured[C]
  )(using C, StorageAccess): Configured[C] =
    if term.opaque then
      throw IllegalArgumentException(
        s"the opaque $term has no subterm $segment"
      )
    val layer = layerOf(term)
    if !roles(layer).contains(segment) then
      throw IllegalArgumentException(
        s"the layer $layer has no subterm $segment"
      )
    built(layer, layer.children.updated(childIndex(segment), child))
