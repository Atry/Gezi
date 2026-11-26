package gezi.frontend

import hedgehog.Gen
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText

/** The laws of the precedence of M. Dezani-Ciancaglini, U. de'Liguoro and A.
  * Piperno (1996), section 2.1, "abstraction and application take precedence
  * over + and ∥", with + and ∥ of one precedence, left associative (the
  * Scaladoc of `Lambdalattice`, PRECEDENCE), on generated closed terms a, b
  * and so on written in parentheses: `λx. (a) op (b)` reads as
  * `(λx. (a)) op (b)` for op either operator, and a chain
  * `(a) op₁ (b) op₂ (c) …` of either operators, mixed, reads as
  * `(((a) op₁ (b)) op₂ (c)) …`. Its purpose is to catch an abstraction's body
  * that extends over an operator, a reader that gives one operator
  * precedence over the other, and a chain grouped to the right.
  */
class LambdalatticePrecedenceLawTest extends GeneratedProperties:

  private def parenthesized(term: gezi.frontend.Term): String = s"(${LambdalatticeText.text(term)})"

  private val operators: Gen[String] = Gen.element1("+", "∥")

  property("an abstraction's body stops before + and ∥") {
    for
      operator <- operators.forAll
      left <- HoasGenerators.closedTerm.forAllWithLog(parenthesized)
      right <- HoasGenerators.closedTerm.forAllWithLog(parenthesized)
    yield
      val bare = s"λx. ${parenthesized(left)} $operator ${parenthesized(right)}"
      val grouped = s"(λx. ${parenthesized(left)}) $operator ${parenthesized(right)}"
      Result.diff(Lambdalattice.term(bare), Lambdalattice.term(grouped))(_ == _)
  }

  property("a chain of + and ∥ reads grouped to the left, each operator over the chain before it") {
    for
      operands <- HoasGenerators.closedTerm.list(hedgehog.Range.linear(2, 5)).forAllWithLog(_.map(parenthesized).mkString(" | "))
      chainOperators <- operators.list(hedgehog.Range.singleton(operands.size - 1)).forAllWithLog(_.mkString(" "))
    yield
      val written = operands.map(parenthesized)
      val chain = written.head + chainOperators.zip(written.tail).map((operator, operand) => s" $operator $operand").mkString
      val grouped = chainOperators.zip(written.tail).foldLeft(written.head) { case (before, (operator, operand)) =>
        s"($before) $operator $operand"
      }
      Result.diff(Lambdalattice.term(chain), Lambdalattice.term(grouped))(_ == _)
  }
