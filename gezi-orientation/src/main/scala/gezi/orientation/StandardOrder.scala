package gezi.orientation

import scala.annotation.tailrec
import scala.jdk.StreamConverters.*

/** A term of Prolog written out for its standard order of terms: what the
  * Prolog baseline sorted orientations by. Only the kinds of term the
  * baseline's contents hold: integers, atoms, the empty list and compound
  * terms (a list cell is the compound `'[|]'(Head, Tail)`).
  */
enum PrologTerm:
  case Integer(value: Int)
  case Atom(name: String)
  case EmptyList
  case Compound(name: String, arguments: Vector[PrologTerm])

/** The standard order of terms of SWI-Prolog 10.0.2 on `PrologTerm`, as
  * `msort/2` and `sort/2` compare: numbers by value, then the empty list,
  * then atoms by the codes of their names, then compound terms by arity, then
  * by name, then by their arguments left to right. That the empty list
  * comes before every atom was read from SWI-Prolog 10.0.2 on 2026-10-31:
  * `msort([b, [], a, '[]', 'Z', 1, f(x)], L)` gives
  * `[1, [], 'Z', '[]', a, b, f(x)]`.
  */
object StandardOrder:

  /** The standard order as an `Ordering`. */
  val ordering: Ordering[PrologTerm] = (left, right) => compared(List((left, right)))

  /** A list of the elements, in the standard order of a Prolog list. */
  def list(elements: Vector[PrologTerm]): PrologTerm =
    elements.foldRight(PrologTerm.EmptyList: PrologTerm)((element, tail) =>
      PrologTerm.Compound("[|]", Vector(element, tail))
    )

  private def rank(term: PrologTerm): Int = term match
    case PrologTerm.Integer(_)     => 0
    case PrologTerm.EmptyList      => 1
    case PrologTerm.Atom(_)        => 2
    case PrologTerm.Compound(_, _) => 3

  /** The comparison of the first pair that differs, the pairs compared left
    * to right and a compound's arguments before the pairs after it.
    */
  @tailrec
  private def compared(pending: List[(PrologTerm, PrologTerm)]): Int = pending match
    case Nil => 0
    case (left, right) :: rest =>
      val byRank = rank(left).compare(rank(right))
      if byRank != 0 then byRank
      else
        (left, right) match
          case (PrologTerm.Integer(leftValue), PrologTerm.Integer(rightValue)) =>
            val byValue = leftValue.compare(rightValue)
            if byValue != 0 then byValue else compared(rest)
          case (PrologTerm.Atom(leftName), PrologTerm.Atom(rightName)) =>
            val byName = codesCompared(leftName, rightName)
            if byName != 0 then byName else compared(rest)
          case (
                PrologTerm.Compound(leftName, leftArguments),
                PrologTerm.Compound(rightName, rightArguments)
              ) =>
            val byArity = leftArguments.size.compare(rightArguments.size)
            if byArity != 0 then byArity
            else
              val byName = codesCompared(leftName, rightName)
              if byName != 0 then byName
              else compared(leftArguments.zip(rightArguments).toList ++ rest)
          case _ => compared(rest)

  /** Names compared by their code points. */
  private def codesCompared(left: String, right: String): Int =
    val leftCodes = left.codePoints.toScala(Vector)
    val rightCodes = right.codePoints.toScala(Vector)
    leftCodes
      .zip(rightCodes)
      .map(_ compare _)
      .find(_ != 0)
      .getOrElse(leftCodes.size.compare(rightCodes.size))
