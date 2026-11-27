package com.yang_bo.gezi.saturation

import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The n-ary reverse beta of a lemma whose left side is a metavariable applied
  * to names, `C^(C @ G1 @ ... @ Gn)`, on the spellings of a round's inputs:
  * every subterm T whose spelling holds every Gi is in one class with
  * `(λx1 ... λxn. T[G1 := x1, ..., Gn := xn]) @ G1 @ ... @ Gn`, a beta redex
  * whose contraction is T, so that the first-order matching finds the left side
  * at T. The root case of the n-ary reverse beta every lemma carries, beside
  * `HigherOrderMatching`, which solves an occurrence under a side's object
  * lambda on a thunk node's code; the names are closed, so the union relies on
  * no fact about a bound variable.
  *
  * It began as `ReverseBetaSaturator` of the module contest-modules-wren, moved
  * into the framework; the names a side lists are read off the framework's
  * patterns instead of the baseline encoding's.
  */
object ReverseBeta:

  /** The names a left side applies its head metavariable to, when the side is
    * that metavariable applied to one name or more and nothing else.
    */
  def abstractedNames[C <: NativeSpecializer & Singleton](
      left: Pattern[C]
  ): Option[Vector[Configured[C]]] =
    def spine(
        pattern: Pattern[C],
        arguments: List[Configured[C]]
    ): Option[Vector[Configured[C]]] = pattern match
      case Pattern.Apply(function, Pattern.InstructionReference(name)) =>
        spine(function, name :: arguments)
      case Pattern.Metavariable(_) if arguments.nonEmpty =>
        Some(arguments.toVector)
      case _ => None
    spine(left, Nil)

  /** The subterms of the inputs, each once, whose spelling holds every name, in
    * the order of a walk from the inputs, a subterm before the subterms under
    * it.
    */
  def holdingAll[C <: NativeSpecializer & Singleton](
      inputs: Vector[Configured[C]],
      names: Vector[Configured[C]]
  ): Vector[Configured[C]] =
    val unread = names.toSet
    val holding = names
      .map(name => openTerms(inputs, Set(name), unread))
      .reduce(_ intersect _)
    preorder(inputs, unread).filter(holding.contains)

  /** The redex `(λx1 ... λxn. T[G1 := x1, ...]) @ G1 @ ... @ Gn` of a term
    * whose spelling holds every name. The abstraction is spelled as the front
    * end spells the lambda (`HigherOrderMatching.abstractedInstruction`), so
    * that it is the instruction of the program's own lambda of the same body:
    * one term, one instruction; every layer built by the round's construction.
    */
  def redex[C <: NativeSpecializer & Singleton](
      term: Configured[C],
      names: Vector[Configured[C]],
      construction: com.yang_bo.gezi.ir.TermConstruction[C]
  ): Configured[C] =
    val open = openTerms(Vector(term), names.toSet, names.toSet)
    require(names.forall(open.contains), s"the term holds every name: $term")
    names.foldLeft(
      HigherOrderMatching.abstractedInstruction(term, names, construction)
    )(construction.specializer.application(_, _))

  /** The subterms read below an instruction: none under a name, an opaque
    * instruction or a native storage the e-graph keeps as a leaf, whose view is
    * not read.
    */
  private def children[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      names: Set[Configured[C]]
  ): Vector[Configured[C]] =
    if names.contains(instruction) || instruction.representation.heldAsLeaf then
      Vector.empty
    else instruction.layer.children

  /** The subterms of the terms, each once, a subterm before those under it. */
  private def preorder[C <: NativeSpecializer & Singleton](
      terms: Vector[Configured[C]],
      names: Set[Configured[C]]
  ): Vector[Configured[C]] =
    @scala.annotation.tailrec
    def visited(
        pending: List[Configured[C]],
        seen: Set[Configured[C]],
        order: Vector[Configured[C]]
    ): Vector[Configured[C]] =
      pending match
        case Nil                                      => order
        case instruction :: rest if seen(instruction) =>
          visited(rest, seen, order)
        case instruction :: rest =>
          visited(
            children(instruction, names).toList ::: rest,
            seen + instruction,
            order :+ instruction
          )
    visited(terms.toList, Set.empty, Vector.empty)

  /** The subterms of the terms, each once, whose spelling holds one of the
    * names, the names among them; the layer of an unread instruction (every
    * name of the list, so that a name inside another name's body is not
    * counted) is not read.
    */
  private def openTerms[C <: NativeSpecializer & Singleton](
      terms: Vector[Configured[C]],
      names: Set[Configured[C]],
      unread: Set[Configured[C]]
  ): Set[Configured[C]] =
    @scala.annotation.tailrec
    def visited(
        pending: List[(Configured[C], Boolean)],
        seen: Set[Configured[C]],
        open: Set[Configured[C]]
    ): Set[Configured[C]] =
      pending match
        case Nil                                               => open
        case (instruction, false) :: rest if seen(instruction) =>
          visited(rest, seen, open)
        case (instruction, false) :: rest =>
          visited(
            children(instruction, unread).toList
              .map((_, false)) ::: (instruction, true) :: rest,
            seen + instruction,
            open
          )
        case (instruction, true) :: rest =>
          val isOpen =
            names.contains(instruction) || children(instruction, unread).exists(
              open.contains
            )
          visited(rest, seen, if isOpen then open + instruction else open)
    visited(terms.toList.map((_, false)), Set.empty, Set.empty)
