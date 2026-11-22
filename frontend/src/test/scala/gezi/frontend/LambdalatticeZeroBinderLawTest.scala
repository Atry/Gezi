package gezi.frontend

import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText

/** The law of the λ of no binder, Haskell's `$`, which changes the
  * precedence only: wherever a bare λ may
  * stand, `λ. M` reads as `(M)`, M a generated term: the whole text, the last
  * argument of an application, the operands of + and of ∥, and an
  * abstraction's body; and its body extends over an application's arguments
  * and stops before +, `f λ. g x` being `f (g x)` and `λ. a b + c` being
  * `(a b) + c`. Its purpose is to catch a `λ.` read as an abstraction,
  * one whose body stops early or runs past the operator after it, or one not
  * accepted where a bare λ is.
  */
class LambdalatticeZeroBinderLawTest extends GeneratedProperties:

  private def parenthesized(term: gezi.frontend.Term): String = s"(${LambdalatticeText.text(term)})"

  private def bare(term: gezi.frontend.Term): String = s"λ. (${LambdalatticeText.text(term)})"

  property("a λ of no binder reads as its body in parentheses wherever a bare λ may stand") {
    for
      function <- HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text)
      left <- HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text)
      right <- HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text)
    yield
      def same(written: String, meant: String): Result =
        Result.diff(Lambdalattice.term(written), Lambdalattice.term(meant))(_ == _).log(s"$written against $meant")
      Result.all(
        List(
          same(bare(left), parenthesized(left)),
          same(s"${parenthesized(function)} ${bare(left)}", s"${parenthesized(function)} ${parenthesized(left)}"),
          same(
            s"${parenthesized(function)} λ. ${parenthesized(left)} ${parenthesized(right)}",
            s"${parenthesized(function)} (${parenthesized(left)} ${parenthesized(right)})"
          ),
          same(
            s"λ. ${parenthesized(left)} ${parenthesized(right)} + ${parenthesized(function)}",
            s"(${parenthesized(left)} ${parenthesized(right)}) + ${parenthesized(function)}"
          ),
          same(s"${bare(left)} + ${bare(right)}", s"${parenthesized(left)} + ${parenthesized(right)}"),
          same(s"${bare(left)} ∥ ${bare(right)}", s"${parenthesized(left)} ∥ ${parenthesized(right)}"),
          same(s"λx. ${bare(left)}", s"λx. ${parenthesized(left)}"),
          same(s"\\. ${parenthesized(left)}", parenthesized(left))
        )
      )
  }
