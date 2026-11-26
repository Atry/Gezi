package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import gezi.frontend.LambdalatticeLayout.ParameterLists
import snapshot4s.generated.snapshotConfig

/** The layout of parameter lists as line prefixes
  * (`LambdalatticeLayout.ParameterLists.Prefixed`, the multi-line CPS layout
  * of CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line") on generated closed texts whose tokens are separated by a space
  * or a line break, drawn for each.
  *
  *   - Law: the laid out text reads to the term of the text, laying it out
  *     again changes nothing, a line that begins with + or ∥ stands in the
  *     column of the `(` of the innermost parentheses open across it, and a
  *     line that begins with `λ` or `.` two columns in from that `(`, the
  *     first column outside all parentheses. Its purpose is to catch a layout that
  *     changes the term, one its own output does not keep, and a prefix out
  *     of its column.
  *   - Snapshot: the examples of CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line", each written
  *     with its line breaks and no indentation, laid out; and generated
  *     texts laid out, from a fixed seed. Its purpose is to record the
  *     columns the layout gives, the inner `(` of nested parentheses
  *     included, which these examples' snapshot settles.
  */
class LambdalatticeLayoutPrefixedTest extends GeneratedProperties with SeededSnapshots:

  /** A closed text the printer writes, its tokens each separated from the
    * last by a space or a line break.
    */
  private val texts: Gen[String] =
    for
      printed <- HoasGenerators.closedTerm.map(LambdalatticeText.text)
      tokens = Lambdalattice.lexemes(printed).collect { case Lexeme.Token(_, written) => written }
      breaks <- Gen.boolean.list(Range.singleton(tokens.size))
    yield tokens.zip(breaks).map((token, broken) => (if broken then "\n" else " ") + token).mkString.drop(1)

  private def laidOut(text: String): String = LambdalatticeLayout.laidOut(Lambdalattice.lexemes(text), ParameterLists.Prefixed)

  /** A token of a text with its line and column, and whether it begins its
    * line.
    */
  private final case class Placed(kind: TokenKind, line: Int, column: Int, first: Boolean)

  private def placed(text: String): Vector[Placed] =
    text.linesIterator.zipWithIndex.toVector.flatMap((line, number) =>
      Lambdalattice
        .lexemes(line)
        .foldLeft((Vector.empty[Placed], 0)) {
          case ((found, column), Lexeme.Token(kind, written)) =>
            (found :+ Placed(kind, number, column, found.isEmpty), column + written.length)
          case ((found, column), other) => (found, column + other.written.length)
        }
        ._1
    )

  /** The prefixes standing elsewhere than their column: + and ∥ in the
    * column of the innermost open parentheses that span lines, `λ` and `.`
    * two columns in from it, the first column outside all.
    */
  private def misplacedPrefixes(text: String): Vector[String] =
    val tokens = placed(text)
    val (misplaced, _) = tokens.foldLeft((Vector.empty[String], List.empty[Placed])) {
      case ((found, open), token) =>
        val spanningOpen = open.filter(opening => opening.line < token.line)
        val expected = token.kind match
          case TokenKind.Lambda | TokenKind.Dot      => Some(spanningOpen.headOption.fold(0)(_.column + 2))
          case TokenKind.Choice | TokenKind.Parallel => Some(spanningOpen.headOption.fold(0)(_.column))
          case _                                     => None
        val prefix = token.first && expected.nonEmpty
        val checked =
          if prefix && !expected.contains(token.column) then found :+ s"line ${token.line}: column ${token.column}, not ${expected.mkString}"
          else found
        token.kind match
          case TokenKind.OpenParenthesis  => (checked, token :: open)
          case TokenKind.CloseParenthesis => (checked, open.drop(1))
          case _                          => (checked, open)
    }
    misplaced

  property("the laid out text reads to the term, laying it out again changes nothing, and prefixes stand in their column") {
    texts.forAllWithLog(identity).map(text =>
      val once = laidOut(text)
      val problems =
        (if Lambdalattice.term(once) == Lambdalattice.term(text) then Vector.empty else Vector(s"`$once` reads another term")) ++
          (if laidOut(once) == once then Vector.empty else Vector(s"laying `$once` out again gives `${laidOut(once)}`")) ++
          misplacedPrefixes(once)
      Result.assert(problems.isEmpty).log(problems.mkString("\n")).log(once)
    )
  }

  /** The examples, each line's indentation taken away. */
  private val examples: Vector[String] = Vector(
    """λ
      |. (λt. t λ. g 42 λa b. a)
      |λ $merkle$89abcdef f x
      |. f x $merkle$89abcdef
      |λ y "k" w
      |. (y w $merkle$89abcdef + λz. z ∥ x)""".stripMargin,
    """λ
      |. (λt. t λ. g 42 λa b. a)
      |λ $merkle$89abcdef f x
      |. f x $merkle$89abcdef
      |λ y "k" w
      |. ( y w $merkle$89abcdef
      |+ λz. z
      |∥ x
      |)""".stripMargin,
    """λ
      |. read_line f
      |λ line
      |. parse line
      |λ number "k"
      |. log number
      |λ
      |. done number""".stripMargin,
    """λ
      |. fixpoint
      |λ eval environment expression
      |. expression
      |(λname. lookup environment name)
      |( λ function argument
      |. apply (eval environment function)
      |λ
      |. eval environment argument
      |)
      |λ parameter body
      |. closure environment parameter body""".stripMargin
  )

  test("the examples of the multi-line CPS layout laid out") {
    assertFileSnapshot(
      examples.map(example => s"$example\n--- laid out ---\n${laidOut(example)}").mkString("\n=====\n"),
      "layout/prefixed-examples.txt"
    )
  }

  test("generated texts laid out with prefixed parameter lists") {
    assertSeededSnapshot(texts, 20261119L, 8, "layout/prefixed-generated.txt")(identity, identity[String])(laidOut)
  }
