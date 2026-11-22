package gezi.rewritetrace

import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}

/** One step of a position: the role of a subterm in the layer above it. */
enum PositionSegment:
  case Function, Argument, Left, Right
  case Filling(index: Int)

/** Which side of the equation a step replaces: `Forward` replaces an
  * instance of the left side by the instance of the right side, `Backward`
  * the right by the left.
  */
enum RewriteDirection:
  case Forward, Backward

  def reversed: RewriteDirection = this match
    case Forward  => Backward
    case Backward => Forward

/** Where a variable of a step's equation occurs: its positions in the
  * subterm the step replaces and in the subterm it puts there, each from the
  * root of that subterm, the step's provenance mapping. The subterm at each position
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
  * position read or replaced.
  */
object Positions:

  /** The role of each subterm of the layer, in the order of
    * `Layer.children`; none for a noinline leaf.
    */
  def roles(layer: Layer[Any]): Vector[PositionSegment] = layer match
    case Thunk(_, _, fillings)              => fillings.indices.map(PositionSegment.Filling(_)).toVector
    case Apply(_, _)                        => Vector(PositionSegment.Function, PositionSegment.Argument)
    case Choice(_, _) | Parallel(_, _) => Vector(PositionSegment.Left, PositionSegment.Right)
    case NoinlineLeaf(_)                            => Vector.empty

  /** The positions of the term where the subterm occurs, outermost first in
    * preorder; none under an occurrence.
    */
  def occurrences(term: Instruction, subterm: Instruction): Vector[Vector[PositionSegment]] =
    if term == subterm then Vector(Vector.empty)
    else
      val layer = term.layered
      layer.children.zip(roles(layer)).flatMap((child, role) => occurrences(child, subterm).map(role +: _))

  /** The subterm at the position. Throws `IllegalArgumentException` when the
    * term has no subterm there.
    */
  def subterm(term: Instruction, position: Vector[PositionSegment]): Instruction =
    position.foldLeft(term)(childAt)

  /** The term with the subterm at the position replaced. Throws
    * `IllegalArgumentException` when the term has no subterm there.
    */
  def replaced(term: Instruction, position: Vector[PositionSegment], replacement: Instruction): Instruction =
    val ancestors = position.scanLeft(term)(childAt)
    position.indices.foldRight(replacement)((place, inner) => withChild(ancestors(place), position(place), inner))

  private def childAt(term: Instruction, segment: PositionSegment): Instruction = (term.layer, segment) match
    case (Apply(function, _), PositionSegment.Function) => function
    case (Apply(_, argument), PositionSegment.Argument) => argument
    case (Choice(left, _), PositionSegment.Left)        => left
    case (Choice(_, right), PositionSegment.Right)      => right
    case (Parallel(left, _), PositionSegment.Left)      => left
    case (Parallel(_, right), PositionSegment.Right)    => right
    case (Thunk(_, _, fillings), PositionSegment.Filling(place)) =>
      fillings.lift(place).getOrElse(throw IllegalArgumentException(s"$term has no filling $place"))
    case (layer, _) => throw IllegalArgumentException(s"the layer $layer has no subterm $segment")

  private def withChild(term: Instruction, segment: PositionSegment, child: Instruction): Instruction =
    (term.layer, segment) match
      case (Apply(_, argument), PositionSegment.Function) => Instruction.Apply(child, argument)
      case (Apply(function, _), PositionSegment.Argument) => Instruction.Apply(function, child)
      case (Choice(_, right), PositionSegment.Left)       => Instruction.Choice(child, right)
      case (Choice(left, _), PositionSegment.Right)       => Instruction.Choice(left, child)
      case (Parallel(_, right), PositionSegment.Left)     => Instruction.Parallel(child, right)
      case (Parallel(left, _), PositionSegment.Right)     => Instruction.Parallel(left, child)
      case (Thunk(code, holes, fillings), PositionSegment.Filling(place)) if fillings.indices.contains(place) =>
        Instruction.Thunk(code, holes, fillings.updated(place, child))
      case (layer, _) => throw IllegalArgumentException(s"the layer $layer has no subterm $segment")
