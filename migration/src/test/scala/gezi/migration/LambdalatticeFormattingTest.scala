package gezi.migration

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.Lambdalattice
import gezi.frontend.Lexeme
import gezi.frontend.TokenKind
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import snapshot4s.generated.snapshotConfig

/** The formatter of lambdalattice texts (`LambdalatticeFormatting.formatted`)
  * on generated closed texts, a quarter of them such texts applied to
  * literals and under a λ of literal binders, with generated layout
  * (spaces, line breaks, blank lines and comments).
  *
  *   - Law: the formatted text reads to the term of the text, and formatting
  *     it again changes nothing. Its purpose is to catch a respelling that
  *     changes the term (the formatter throws on one) and a layout that its
  *     own output does not keep.
  *   - Law: in the formatted text, a line breaks only before `λ`, `.`, +,
  *     ∥, `(` and `)`, or at a comment, and the `(` and the `)` of
  *     parentheses that span lines stand in one column. Its purpose is to
  *     catch a break the multi-line CPS layout of CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line" does not
  *     allow, and a misplaced column.
  *   - Snapshot: texts and their formatting, from a fixed seed. Its purpose
  *     is to record the layout the formatter writes, an output as complex as
  *     the formatter.
  */
class LambdalatticeFormattingTest extends GeneratedProperties with SeededSnapshots:

  /** A closed text the printer writes, which never holds a literal. */
  private val printed: Gen[String] = HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** A literal with no space in it, so that `LambdalatticeText.withLayout`
    * puts layout around it and never inside: the printer writes no literal,
    * so the literals the formatter lays out come from here.
    */
  private val literal: Gen[String] =
    Gen.element1("\"k\"", "30", "-7", "0.5", "[1,\"a\"]", "{1:2}", "h'00ff'", "(30([1]))", "0x1f")

  /** A literal binder with no space in it, bare or alone in parentheses. */
  private val binder: Gen[String] =
    Gen.element1("\"k\"", "30", "-7", "[1,\"a\"]", "{1:2}", "h'00ff'", "0x1f", "(0.5)", "30([1])")

  /** A printed text applied to literals, under a λ of literal binders. */
  private val withLiterals: Gen[String] =
    for
      body <- printed
      arguments <- literal.list(hedgehog.Range.linear(1, 3))
      binders <- binder.list(hedgehog.Range.linear(1, 2))
    yield s"λ${binders.mkString(" ")} . ($body) ${arguments.mkString(" ")}"

  private val texts: Gen[String] =
    Gen.frequency1(3 -> printed, 1 -> withLiterals).flatMap(LambdalatticeText.withLayout)

  private def formatted(text: String): String = LambdalatticeFormatting.formatted(Vector.empty, text)

  property("the formatted text reads to the term, and formatting it again changes nothing") {
    texts.forAllWithLog(identity).map(text =>
      val once = formatted(text)
      val problems =
        (if Lambdalattice.term(once) == Lambdalattice.term(text) then Vector.empty else Vector(s"`$once` reads another term")) ++
          (if formatted(once) == once then Vector.empty else Vector(s"formatting `$once` again gives `${formatted(once)}`"))
      Result.assert(problems.isEmpty).log(problems.mkString("\n"))
    )
  }

  /** A token of a text with its line and column. */
  private final case class Placed(kind: TokenKind, line: Int, column: Int, afterBreak: Boolean, afterComment: Boolean)

  private def placed(text: String): Vector[Placed] =
    Lambdalattice
      .lexemes(text)
      .foldLeft((Vector.empty[Placed], 0, 0, false, false)) {
        case ((found, line, column, broke, commented), Lexeme.Token(kind, written)) =>
          (found :+ Placed(kind, line, column, broke, commented), line, column + written.length, false, false)
        case ((found, line, column, broke, _), Lexeme.Comment(written)) =>
          (found, line, column + written.length, broke, true)
        case ((found, line, column, broke, commented), Lexeme.Space(written)) =>
          val breaks = written.count(_ == '\n')
          val nextColumn = if breaks == 0 then column + written.length else written.length - written.lastIndexOf('\n') - 1
          (found, line + breaks, nextColumn, broke || breaks > 0, commented)
      }
      ._1

  property("lines break only where the multi-line CPS layout allows, and spanning parentheses stand in one column") {
    texts.forAllWithLog(identity).map(text =>
      val tokens = placed(formatted(text))
      val misplacedBreaks = tokens.indices.drop(1).filter(index =>
        val token = tokens(index)
        token.afterBreak && !token.afterComment && !(token.kind match
          case TokenKind.Lambda | TokenKind.Dot | TokenKind.Choice | TokenKind.Parallel | TokenKind.OpenParenthesis |
              TokenKind.CloseParenthesis => true
          case _ => false
        )
      )
      val (misaligned, _) = tokens.foldLeft((Vector.empty[Placed], List.empty[Placed])) {
        case ((found, open), token) if token.kind == TokenKind.OpenParenthesis =>
          (found, token :: open)
        case ((found, opening :: rest), token) if token.kind == TokenKind.CloseParenthesis =>
          (if opening.line != token.line && opening.column != token.column then found :+ token else found, rest)
        case (state, _) => state
      }
      val problems = misplacedBreaks.map(index => s"a line breaks before the token $index") ++
        misaligned.map(token => s"the `)` at line ${token.line} stands in another column than its `(`")
      Result.assert(problems.isEmpty).log(problems.mkString("\n"))
    )
  }

  test("formatting generated texts") {
    assertSeededSnapshot(texts, 20261113L, 12, "formatting/generated_texts.txt")(identity, identity[String])(formatted)
  }
