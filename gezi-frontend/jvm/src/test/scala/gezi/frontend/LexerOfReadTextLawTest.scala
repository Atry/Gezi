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

  /** Texts the grammar reads by construction: a name; a name applied to
    * literals of every kind and to parenthesized texts; a λ (either spelling)
    * over names, `_` and literals as binders; two parenthesized texts joined
    * by a choice or a parallel (either spelling).
    */
  private def grammatical(depth: Int): Gen[String] =
    val name = Gen.element1("x", "f")
    val literal = Gen.element1("30", "\"k\"", "h'00ff'", "[1, 2]", "3.0", "0.5", "{\"k\": 1}", "true", "-7", "b64'AA'")
    if depth == 0 then name
    else
      val inner = grammatical(depth - 1)
      Gen.choice1(
        name,
        for
          head <- name
          arguments <- Gen.choice1(literal, inner.map(text => s"($text)")).list(Range.linear(1, 3))
        yield (head :: arguments).mkString(" "),
        for
          lambda <- Gen.element1("λ", "\\")
          binders <- Gen.choice1(name, Gen.constant("_"), Gen.element1("\"k\"", "30")).list(Range.linear(1, 2))
          body <- inner
        yield s"$lambda${binders.mkString(" ")}. $body",
        for
          left <- inner
          operator <- Gen.element1("+", "∥", "||")
          right <- inner
        yield s"($left) $operator ($right)"
      )

  /** The lexer's verdict on a text: none when it reads it, its error otherwise. */
  private def lexed(text: String): Option[LambdalatticeMalformed] =
    try
      Lambdalattice.tokens(text)
      None
    catch case malformed: LambdalatticeMalformed => Some(malformed)

  /** Every iteration checks a text of fragments, which the grammar may or may
    * not read, and a text the grammar reads by construction, whose verdicts
    * are known: the grammar and the lexer read it.
    */
  property("a text the grammar reads is a text the lexer reads") {
    for
      text <- texts.forAll
      readable <- grammatical(3).forAll
    yield
      val drawn = if !read(text) then Result.success else Result.assert(lexed(text).isEmpty).log(s"the grammar reads $text, the lexer rejects it: ${lexed(text)}")
      drawn
        .and(Result.assert(read(readable)).log(s"the grammar rejects $readable, a text of its own grammar"))
        .and(Result.assert(lexed(readable).isEmpty).log(s"the lexer rejects $readable: ${lexed(readable)}"))
  }
