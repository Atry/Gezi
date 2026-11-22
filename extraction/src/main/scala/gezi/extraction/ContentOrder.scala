package gezi.extraction

import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.SpecializationRange
import scala.annotation.tailrec
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}

/** The order of content between entries of equal cost, the extraction's
  * tie-break: a structural order of the term, the same for every
  * constructor and name.
  *
  * Two entries compare first by the size of the term they spell
  * (`Entry.size`), the smaller first, then by structure: a name, then a
  * node, a specialization choice and a judgment (`Shape`); two names by
  * their instructions; two nodes by the layer's constructor
  * (apply, parallel, choice, thunk, leaf, in that order), the thunk's code
  * and holes, the leaf's instruction; two specialization choices by what stands
  * around the typed application (nothing, a range, a contract) and by the
  * order of their members, two judgments by the order of theirs; and then
  * their child entries left to right. A dispatch pattern spells a choice
  * that a node's entry may spell too, and the two compare by their shapes,
  * not as one term. Two instructions, and two codes, compare by
  * their hash codes, which the IR computes from content alone and makes the
  * same in every process (`gezi.ir.Instruction`), and only on equal
  * hash codes by their structure the same way. An opaque instruction compares by
  * its name. Nothing reads a node's number, a class's root, a name's
  * meaning, a type or a filter's criterion: the order is the spelled
  * term's, so the entry a class keeps among equal costs does not depend on
  * the order in which the graph numbered its nodes.
  *
  * The order is total on spelled terms, and well founded among the entries
  * of a graph: the size comes first, and a finite graph spells finitely many
  * terms of each size.
  *
  * Stack safe: the comparison walks a list of pending pairs, the first
  * difference deciding.
  */
object ContentOrder:

  /** Negative when `left` comes first, zero when the two spell one term,
    * positive otherwise.
    */
  def compare[Cost](left: Entry[Cost], right: Entry[Cost]): Int =
    compared(List(Pending.Entries(left, right)))

  private enum Pending:
    case Entries(left: Entry[?], right: Entry[?])
    case Instructions(left: Instruction, right: Instruction)
    case Codes(left: Code, right: Code)
    case Integers(left: Int, right: Int)
    case Texts(left: String, right: String)

  @tailrec
  private def compared(pending: List[Pending]): Int = pending match
    case Nil => 0
    case next :: rest =>
      step(next) match
        case Left(0)        => compared(rest)
        case Left(decision) => decision
        case Right(more)    => compared(more ++ rest)

  /** The decision of one pair, or the pairs it is decided by, in order. */
  private def step(pair: Pending): Either[Int, List[Pending]] = pair match
    case Pending.Integers(left, right) => Left(Integer.compare(left, right))
    case Pending.Texts(left, right)    => Left(left.compareTo(right))
    case Pending.Entries(left, right) =>
      if left eq right then Left(0)
      else
        val bySize = left.size.compare(right.size)
        if bySize != 0 then Left(bySize)
        else
          Right(
            shapePairs(left.shape, right.shape) ++
              left.childEntries.zip(right.childEntries).map(Pending.Entries(_, _))
          )
    case Pending.Instructions(left, right) =>
      if left eq right then Left(0)
      else if left.hashCode != right.hashCode then Left(Integer.compare(left.hashCode, right.hashCode))
      else if left.opaque || right.opaque then
        Right(List(Pending.Integers(opaqueRank(left), opaqueRank(right)), Pending.Texts(left.toString, right.toString)))
      else layerPairs(left.layered, right.layered)
    case Pending.Codes(left, right) =>
      if left eq right then Left(0)
      else if left.hashCode != right.hashCode then Left(Integer.compare(left.hashCode, right.hashCode))
      else codePairs(left.layer, right.layer)

  private def opaqueRank(instruction: Instruction): Int = if instruction.opaque then 0 else 1

  private def shapePairs(left: Shape, right: Shape): List[Pending] = (left, right) match
    case (Shape.Name(leftInstruction), Shape.Name(rightInstruction)) => List(Pending.Instructions(leftInstruction, rightInstruction))
    case (Shape.Node(_, leftLayer), Shape.Node(_, rightLayer)) =>
      Pending.Integers(layerRank(leftLayer), layerRank(rightLayer)) :: atomPairs(leftLayer, rightLayer)
    case (Shape.Specialized(_, leftSpecialization), Shape.Specialized(_, rightSpecialization)) =>
      List(
        Pending.Integers(rangeRank(leftSpecialization.range), rangeRank(rightSpecialization.range)),
        Pending.Integers(orderRank(leftSpecialization.untypedFirst), orderRank(rightSpecialization.untypedFirst))
      )
    case (Shape.Judged(_, leftFallback), Shape.Judged(_, rightFallback)) =>
      List(Pending.Integers(orderRank(leftFallback.valueFirst), orderRank(rightFallback.valueFirst)))
    case _ => List(Pending.Integers(shapeRank(left), shapeRank(right)))

  /** A name, a node, a specialization choice, a judgment. */
  private def shapeRank(shape: Shape): Int = shape match
    case Shape.Name(_)           => 0
    case Shape.Node(_, _)        => 1
    case Shape.Specialized(_, _) => 2
    case Shape.Judged(_, _)      => 3

  private def rangeRank(range: SpecializationRange[Int]): Int = range match
    case SpecializationRange.Absent        => 0
    case SpecializationRange.Filtered(_)   => 1
    case SpecializationRange.Contracted(_) => 2

  private def orderRank(first: Boolean): Int = if first then 0 else 1

  /** The pairs of the atoms of two layers of one constructor: a thunk's code
    * and holes, a leaf's instruction.
    */
  private def atomPairs(left: Layer[Any], right: Layer[Any]): List[Pending] = (left, right) match
    case (Thunk(leftCode, leftHoles, _), Thunk(rightCode, rightHoles, _)) =>
      Pending.Codes(leftCode, rightCode) :: holePairs(leftHoles, rightHoles)
    case (NoinlineLeaf(leftInstruction), NoinlineLeaf(rightInstruction)) =>
      List(Pending.Instructions(leftInstruction, rightInstruction))
    case _ => Nil

  /** The pairs of two instructions' layers of equal hash code: the
    * constructor, the atoms, then the children.
    */
  private def layerPairs(left: Layer[Instruction], right: Layer[Instruction]): Either[Int, List[Pending]] =
    val rankOrder = Integer.compare(layerRank(left), layerRank(right))
    if rankOrder != 0 then Left(rankOrder)
    else Right(atomPairs(left, right) ++ left.children.zip(right.children).map(Pending.Instructions(_, _)))

  private def codePairs(left: CodeLayer[Code], right: CodeLayer[Code]): Either[Int, List[Pending]] =
    val rankOrder = Integer.compare(codeRank(left), codeRank(right))
    if rankOrder != 0 then Left(rankOrder)
    else
      (left, right) match
        case (Slot(leftIndex), Slot(rightIndex)) => Left(Integer.compare(leftIndex, rightIndex))
        case (Apply(leftFunction, leftArgument), Apply(rightFunction, rightArgument)) =>
          Right(List(Pending.Codes(leftFunction, rightFunction), Pending.Codes(leftArgument, rightArgument)))
        case (Parallel(leftLeft, leftRight), Parallel(rightLeft, rightRight)) =>
          Right(List(Pending.Codes(leftLeft, rightLeft), Pending.Codes(leftRight, rightRight)))
        case (Choice(leftLeft, leftRight), Choice(rightLeft, rightRight)) =>
          Right(List(Pending.Codes(leftLeft, rightLeft), Pending.Codes(leftRight, rightRight)))
        case (Thunk(leftInner, leftHoles, leftFillings), Thunk(rightInner, rightHoles, rightFillings)) =>
          Right(
            Pending.Codes(leftInner, rightInner) :: holePairs(leftHoles, rightHoles) ++
              (Pending.Integers(leftFillings.size, rightFillings.size) ::
                leftFillings.zip(rightFillings).map(Pending.Codes(_, _)).toList)
          )
        case other => throw IllegalStateException(s"two code layers of one rank differ in constructor: $other")

  /** Two hole lists: their lengths, then each hole, an ignored binder
    * before a bound one, bound ones by slot.
    */
  private def holePairs(left: Vector[Hole], right: Vector[Hole]): List[Pending] =
    Pending.Integers(left.size, right.size) ::
      left.zip(right).map((leftHole, rightHole) => Pending.Integers(holeRank(leftHole), holeRank(rightHole))).toList

  private def holeRank(hole: Hole): Int = hole match
    case Hole.Ignored     => -1
    case Hole.Bound(slot) => slot

  /** The rank of a layer's constructor. */
  private def layerRank(layer: Layer[Any]): Int = layer match
    case Apply(_, _)     => 0
    case Parallel(_, _)  => 1
    case Choice(_, _)    => 2
    case Thunk(_, _, _)  => 3
    case NoinlineLeaf(_)         => 4

  /** The rank of a code's constructor. */
  private def codeRank(layer: CodeLayer[Code]): Int = layer match
    case Slot(_)         => 0
    case Apply(_, _)     => 1
    case Parallel(_, _)  => 2
    case Choice(_, _)    => 3
    case Thunk(_, _, _)  => 4
