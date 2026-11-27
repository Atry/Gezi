package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The pieces of HOAS the generators of the reduction group share: the Scott
  * encodings of Booleans, unary and binary naturals and lists, and lets (the
  * translation of a closed de Bruijn term back to the HOAS is
  * `common.DeBruijnTerms`). Every piece is built afresh at each use, as the
  * Prolog builders make a fresh copy of their clause's variables at each call.
  */
object Encodings:

  /** The Scott true, `\t. \_. t`. */
  def trueTerm: ProblemTerm = λ(chosen => λ(_ => chosen))

  /** The Scott false, `\_. \f. f`. */
  def falseTerm: ProblemTerm = λ(_ => λ(otherwise => otherwise))

  /** The Scott Boolean of a bit: true for 1, false for 0. */
  def bitBoolean(bit: Int): ProblemTerm = bit match
    case 1     => trueTerm
    case 0     => falseTerm
    case other => throw IllegalArgumentException(s"not a bit: $other")

  /** The Scott unary numeral, `\z. \_. z` for zero and `\_. \s. s p` for a
    * successor (`contest_merge_dynamic:unary/2`). The numeral is built lazily,
    * one abstraction at a time, so a large one takes no stack.
    */
  def unary(number: Int): ProblemTerm =
    require(number >= 0, s"a unary numeral is not negative: $number")
    if number == 0 then λ(zero => λ(_ => zero))
    else λ(_ => λ(successor => successor(unary(number - 1))))

  /** The binary zero, `\z. \_. \_. z`. */
  def binaryZero: ProblemTerm = λ(zero => λ(_ => λ(_ => zero)))

  /** The binary even of a half, `\_. \e. \_. e h`. */
  def binaryEven(half: ProblemTerm): ProblemTerm =
    λ(_ => λ(even => λ(_ => even(half))))

  /** The binary odd of a half, `\_. \_. \o. o h`. */
  def binaryOdd(half: ProblemTerm): ProblemTerm =
    λ(_ => λ(_ => λ(odd => odd(half))))

  /** The canonical binary numeral, least significant bit outermost
    * (`contest_merge_dynamic:binary/2`).
    */
  def binary(number: BigInt): ProblemTerm =
    require(number >= 0, s"a binary numeral is not negative: $number")
    if number == 0 then binaryZero
    else if number % 2 == 0 then binaryEven(binary(number / 2))
    else binaryOdd(binary(number / 2))

  /** The function applied to each argument in turn. */
  def applied(function: ProblemTerm, arguments: Seq[ProblemTerm]): ProblemTerm =
    arguments.foldLeft(function)((applied, argument) => applied(argument))

  /** `(\x1. ... ((\xn. Body) Vn) ...) V1`: the body under a let of each value,
    * each value inside the lets before it, as the Prolog lets build them; the
    * body is given the let variables in order.
    */
  def lets(
      values: Vector[ProblemTerm],
      body: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    letsFrom(values, Vector.empty, body)

  private def letsFrom(
      values: Vector[ProblemTerm],
      bound: Vector[ProblemTerm],
      body: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    if bound.size == values.size then body(bound)
    else
      λ(variable => letsFrom(values, bound :+ variable, body))(
        values(bound.size)
      )

  /** The abstraction of `count` variables over the body, which is given them in
    * order: `\x1. ... \xn. Body`.
    */
  def abstractions(
      count: Int,
      body: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    abstractionsFrom(count, Vector.empty, body)

  private def abstractionsFrom(
      count: Int,
      bound: Vector[ProblemTerm],
      body: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    if bound.size == count then body(bound)
    else λ(variable => abstractionsFrom(count, bound :+ variable, body))

  /** The choice of the members, each a member of its own (a Prolog list in a
    * surface term).
    */
  def members(terms: Vector[ProblemTerm]): ProblemTerm = choice(terms*)

  /** Whether the term is a variable of an enclosing abstraction: Prolog's
    * `var/1` on a surface term, which the builders of the mixin encoding test
    * to let bind any object that is not one.
    */
  def isVariable(term: ProblemTerm): Boolean = term match
    case Term.BoundVariable(_) => true
    case _                     => false

  /** The de Bruijn term of a closed HOAS term holding no library name. */
  def deBruijn(term: ProblemTerm): ProblemDeBruijnTerm =
    term.deBruijnTerm(Map.empty)
