package gezi.frontend

import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText

/** The law that a bare abstraction as the last argument of an application reads
  * as the same abstraction in parentheses, its body, an application, extending
  * over the statements after it, for a chain of such statements as continuation
  * passing style writes them: `(f₁) λx₁. (f₂) λx₂. … (fₙ) λxₙ. (g)` reads as
  * `(f₁) (λx₁. (f₂) (λx₂. … (fₙ) (λxₙ. (g))))`. Its purpose is to catch a
  * trailing abstraction whose body stops before the application that follows
  * it, one read as a function applied to the rest of the text instead of as an
  * argument, or a chain whose binders are counted wrong.
  */
class LambdalatticeTrailingAbstractionLawTest extends GeneratedProperties:

  private def generatedText(term: gezi.frontend.Term): String =
    LambdalatticeText.text(term)

  property(
    "a chain of trailing abstractions reads as the chain with each abstraction in parentheses"
  ) {
    for
      functions <- HoasGenerators.closedTerm
        .list(Range.linear(1, 4))
        .forAllWithLog(_.map(generatedText).mkString(" | "))
      last <- HoasGenerators.closedTerm.forAllWithLog(generatedText)
    yield
      val binders = functions.indices.map(index => s"x$index").toList
      val statements = functions
        .zip(binders)
        .map((function, binder) => (s"(${generatedText(function)})", binder))
      val lastStatement = s"(${generatedText(last)})"
      val bare = statements
        .map((function, binder) => s"$function λ$binder. ")
        .mkString + lastStatement
      val parenthesized = statements.foldRight(lastStatement) {
        case ((function, binder), rest) =>
          s"$function (λ$binder. $rest)"
      }
      Result.diff(Lambdalattice.term(bare), Lambdalattice.term(parenthesized))(
        _ == _
      )
  }
