package gezi.saturation

import gezi.ir.Instruction
import gezi.ir.Pattern

/** The n-ary reverse beta of a lemma whose left side is a metavariable
  * applied to names, `C^(C @ G1 @ ... @ Gn)`, on the spellings of a round's
  * inputs: every subterm T whose spelling holds every Gi is in one class with
  * `(λx1 ... λxn. T[G1 := x1, ..., Gn := xn]) @ G1 @ ... @ Gn`, a beta redex
  * whose contraction is T, so that the first-order matching finds the left
  * side at T. The root case of the n-ary reverse beta every lemma carries,
  * beside
  * `HigherOrderMatching`, which solves an occurrence under a side's object
  * lambda on a thunk node's code; the names are closed, so the union relies
  * on no fact about a bound variable.
  *
  * It began as `ReverseBetaSaturator` of the module contest-modules-wren,
  * moved into the framework; the names a side lists are read off the framework's
  * patterns instead of the baseline encoding's.
  */
object ReverseBeta:

  /** The names a left side applies its head metavariable to, when the side
    * is that metavariable applied to one name or more and nothing else.
    */
  def abstractedNames(left: Pattern): Option[Vector[Instruction]] =
    def spine(pattern: Pattern, arguments: List[Instruction]): Option[Vector[Instruction]] = pattern match
      case Pattern.Apply(function, Pattern.InstructionReference(name)) => spine(function, name :: arguments)
      case Pattern.Metavariable(_) if arguments.nonEmpty               => Some(arguments.toVector)
      case _                                                           => None
    spine(left, Nil)

  /** The subterms of the inputs, each once, whose spelling holds every name,
    * in the order of a walk from the inputs, a subterm before the subterms
    * under it.
    */
  def holdingAll(inputs: Vector[Instruction], names: Vector[Instruction]): Vector[Instruction] =
    val unread = names.toSet
    val holding = names.map(name => openTerms(inputs, Set(name), unread)).reduce(_ intersect _)
    preorder(inputs, unread).filter(holding.contains)

  /** The redex `(λx1 ... λxn. T[G1 := x1, ...]) @ G1 @ ... @ Gn` of a term
    * whose spelling holds every name. The abstraction is spelled as the
    * front end spells the lambda (`HigherOrderMatching.abstractedInstruction`),
    * so that it is the instruction of the program's own lambda of the same body:
    * one term, one instruction.
    */
  def redex(term: Instruction, names: Vector[Instruction]): Instruction =
    val open = openTerms(Vector(term), names.toSet, names.toSet)
    require(names.forall(open.contains), s"the term holds every name: $term")
    names.foldLeft(HigherOrderMatching.abstractedInstruction(term, names))(Instruction.Apply(_, _))

  /** The subterms read below an instruction: none under a name or an opaque
    * instruction.
    */
  private def children(instruction: Instruction, names: Set[Instruction]): Vector[Instruction] =
    if names.contains(instruction) || instruction.opaque then Vector.empty
    else instruction.layer.children

  /** The subterms of the terms, each once, a subterm before those under it. */
  private def preorder(terms: Vector[Instruction], names: Set[Instruction]): Vector[Instruction] =
    @scala.annotation.tailrec
    def visited(pending: List[Instruction], seen: Set[Instruction], order: Vector[Instruction]): Vector[Instruction] =
      pending match
        case Nil                                      => order
        case instruction :: rest if seen(instruction) => visited(rest, seen, order)
        case instruction :: rest =>
          visited(children(instruction, names).toList ::: rest, seen + instruction, order :+ instruction)
    visited(terms.toList, Set.empty, Vector.empty)

  /** The subterms of the terms, each once, whose spelling holds one of the
    * names, the names among them; the layer of an unread instruction (every
    * name of the list, so that a name inside another name's body is not
    * counted) is not read.
    */
  private def openTerms(
      terms: Vector[Instruction],
      names: Set[Instruction],
      unread: Set[Instruction]
  ): Set[Instruction] =
    @scala.annotation.tailrec
    def visited(pending: List[(Instruction, Boolean)], seen: Set[Instruction], open: Set[Instruction]): Set[Instruction] =
      pending match
        case Nil                                               => open
        case (instruction, false) :: rest if seen(instruction) => visited(rest, seen, open)
        case (instruction, false) :: rest =>
          visited(
            children(instruction, unread).toList.map((_, false)) ::: (instruction, true) :: rest,
            seen + instruction,
            open
          )
        case (instruction, true) :: rest =>
          val isOpen = names.contains(instruction) || children(instruction, unread).exists(open.contains)
          visited(rest, seen, if isOpen then open + instruction else open)
    visited(terms.toList.map((_, false)), Set.empty, Set.empty)
