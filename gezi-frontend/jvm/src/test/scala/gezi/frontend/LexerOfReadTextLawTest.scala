package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** Law: a text the grammar reads is a text the lexer reads. `Lambdalattice`
  * reads the lexer only when the grammar rejects a text, to report a lexical
  * error as one (`Lambdalattice.rejected`); its purpose is to catch a text
  * the grammar accepts and the lexer rejects, whose lexical error that
  * reading would no longer report. The texts are sequences of fragments that
  * put names, every kind of literal, binders, parentheses and operators in
  * every place the lexer distinguishes (`Lexer.Place`): a head, an argument,
  * among the binders of a λ, and in parentheses among them.
  */
class LexerOfReadTextLawTest extends GeneratedProperties:

  private val fragments: Vector[String] = Vector(
    "x", "f", "λ", "\\", ".", "(", ")", "+", "∥", "||", " ", "_",
    "30", "30(", "\"k\"", "h'00ff'", "[1, 2]", "3.0", "0.5", "{\"k\": 1}", "true", "-7", "b64'AA'"
  )

  private val texts: Gen[String] =
    Gen.elementUnsafe(fragments.toList).list(Range.linear(1, 14)).map(_.mkString(" "))

  private def read(text: String): Boolean =
    try
      Lambdalattice.parse(text, FreeNames.Allowed)
      true
    catch case _: LambdalatticeMalformed => false

  // The grammar reads 4% to 5% of the texts drawn (seen 2026-11-20; seed 153758314098134 drew 4%, which failed a
  // coverage of 5%): about 80 of the 2,000, which the law needs; the coverage asks for 2%, below what the draws give.
  property("a text the grammar reads is a text the lexer reads", _.copy(testLimit = 2000)) {
    for text <- texts.forAll.cover(2, "the grammar reads it", read(_))
    yield
      if !read(text) then Result.success
      else
        val lexed =
          try
            Lambdalattice.tokens(text)
            None
          catch case malformed: LambdalatticeMalformed => Some(malformed)
        Result.assert(lexed.isEmpty).log(s"the grammar reads $text, the lexer rejects it: $lexed")
  }
