package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import snapshot4s.generated.snapshotConfig

/** The formatter of lambdalattice text (`SourceFormatting`) on generated closed
  * texts whose tokens are separated by a space or a line break, with a numbered
  * comment drawn before some tokens and after the last.
  *
  *   - Law: the formatted text reads to the text's term with the text's
  *     comments in order (which `formatted` checks itself), its names and
  *     literals are the text's, token for token, and formatting it again
  *     changes nothing. Its purpose is to catch a formatter that renames a
  *     binder (a name merged from another occurrence of an interned subterm, or
  *     made fresh), respells a literal, extracts a shared subterm, drops or
  *     reorders a comment, or lays out its own output otherwise.
  *   - Snapshot: generated texts with comments formatted, from a fixed seed,
  *     and texts in the shape of the library's files, one of them read under
  *     enclosing names two of which are the same. Its purpose is to record
  *     where the comments and blank lines land in the multi-line CPS layout,
  *     and to catch an enclosing name renamed for a farther one it shadows.
  */
class SourceFormattingTest extends GeneratedProperties with SeededSnapshots:
  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  /** A closed text the printer writes, its tokens each separated from the last
    * by a space or a line break, a numbered comment before some tokens and
    * after the last.
    */
  private val texts: Gen[String] =
    for
      printed <- HoasGenerators.closedTerm.map(LambdalatticeText.text)
      tokens = Lambdalattice.lexemes(printed).collect {
        case Lexeme.Token(_, written) => written
      }
      breaks <- Gen.boolean.list(Range.singleton(tokens.size))
      commented <- Gen
        .frequency1(1 -> Gen.constant(true), 4 -> Gen.constant(false))
        .list(Range.singleton(tokens.size + 1))
    yield
      val written = tokens.lazyZip(breaks).lazyZip(commented).zipWithIndex.map {
        case ((token, broken, comment), index) =>
          (if comment then s"\n# comment $index\n"
           else if broken then "\n"
           else " ") + token
      }
      written.mkString.drop(1) + (if commented.lastOption.contains(true) then
                                    s"\n# comment ${tokens.size}\n"
                                  else "")

  private def formatted(text: String): String =
    SourceFormatting.formatted(Vector.empty, text)

  /** The names and literals of a text, token for token. */
  private def spelled(text: String): Vector[String] =
    Lambdalattice.lexemes(text).collect {
      case Lexeme.Token(
            TokenKind.Name(_) | TokenKind.StringLiteral(_) |
            TokenKind.CborLiteral(_),
            written
          ) =>
        written
    }

  property(
    "the formatted text keeps the term, the comments, the names and the literals, and formatting it again changes nothing"
  ) {
    texts
      .forAllWithLog(identity)
      .map(text =>
        val once = formatted(text)
        val twice = formatted(once)
        Result
          .assert(spelled(once) == spelled(text))
          .log(s"names and literals: ${spelled(text)} became ${spelled(once)}")
          .and(
            Result
              .assert(twice == once)
              .log(s"formatted once:\n$once\nformatted again:\n$twice")
          )
      )
  }

  test("generated texts with comments formatted") {
    assertSeededSnapshot(
      texts,
      20261119L,
      12,
      "source-formatting/generated.txt"
    )(identity, identity[String])(formatted)
  }

  test("texts in the shape of the library's files formatted") {
    val examples = Vector(
      """# A file's header.
        |
        |(λtuple. tuple λmixin. mixin mixin) λomega.
        |# id:
        |#   the identity.
        |(λtuple. tuple (λx. x)) λid.
        |
        |# twice:
        |#   twice f x = f (f x).
        |(λtuple. tuple (λf. λx. f (f x))) λtwice.
        |λtuple. tuple id twice
        |""".stripMargin,
      """λf. λx. f x (g 42 (λa. λb. a)) (λy. λ"k". λw. ((y w (g 42 (λa. λb. a))) + (λz. z) ∥ x))"""
        .replace("g", "f"),
      """(λt. t λx. x) λ"md". λk. k "[absorption](docs/design/gezi-hindley-milner-unions-proofs.md#absorption)" 0x2a h'00ff'
        |# trailing
        |""".stripMargin
    ).map(Vector.empty[String] -> _) :+ (Vector(
      "natural_pairs",
      "library",
      "natural_pairs"
    ) ->
      """(λtuple. tuple λmixin. mixin mixin) λomega.
        |omega (omega natural_pairs "pair") λpair.
        |λtuple. tuple λx. x λl. λr. pair r l
        |""".stripMargin)
    assertFileSnapshot(
      examples
        .map((enclosing, text) =>
          s"${
              if enclosing.isEmpty then ""
              else enclosing.mkString("under ", " ", "\n")
            }$text\n=>\n${SourceFormatting.formatted(enclosing, text)}"
        )
        .mkString("\n----\n"),
      "source-formatting/library-shapes.txt"
    )
  }
