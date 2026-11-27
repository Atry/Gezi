package gezi.frontend

import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText

/** Law: the pieces of a generated text with generated layout
  * (`Lambdalattice.lexemes`), written one after another, are the text, and
  * their tokens are the tokens of the text with no layout but single spaces.
  * Its purpose is to catch a piece that drops, repeats or splits characters,
  * which would corrupt the names, literals or comments of a text a tool
  * respells from its pieces.
  */
class LambdalatticeLexemesLawTest extends GeneratedProperties:

  private def tokens(text: String): Vector[(TokenKind, String)] =
    Lambdalattice.lexemes(text).collect { case Lexeme.Token(kind, written) =>
      (kind, written)
    }

  property(
    "the pieces of a text are the text, and its tokens are those of the text without layout"
  ) {
    val generated =
      for
        plain <- HoasGenerators.closedTerm.map(LambdalatticeText.text)
        laidOut <- LambdalatticeText.withLayout(plain)
      yield (plain, laidOut)
    generated
      .forAllWithLog(_._2)
      .map((plain, laidOut) =>
        val pieces = Lambdalattice.lexemes(laidOut)
        val problems =
          (if pieces.map(_.written).mkString == laidOut then Vector.empty
           else Vector("the pieces are not the text")) ++
            (if tokens(laidOut) == tokens(plain) then Vector.empty
             else Vector("the tokens differ from the plain text's"))
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }
