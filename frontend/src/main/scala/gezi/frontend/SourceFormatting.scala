package gezi.frontend

/** The formatter of lambdalattice text:
  * the text read in
  * the scope of its enclosing names into the IR with its source map
  * (`Defunctionalization.locatedThunkInstruction`), written back by the
  * printer (`ReadableText.writtenBack`), and laid out in the multi-line CPS
  * layout of CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line", as `ReadableText.Printed.laidOut` lays out a
  * printed term. It formats through the IR and the source map, and keeps
  * every character-level choice of the text, its names and comments
  * included.
  *
  * Names, literals and the sharing of subterms are the text's, as
  * `writtenBack` says. Comments and blank lines are put back where the text
  * has them: each run of them between two tokens of the text (a run of
  * white space alone is respelled) stands before the first name or literal
  * the printer writes whose source spelling begins at or after the token
  * after the run (`ReadableText.Piece.Source`), moved back over the opening
  * tokens (`λ`, `.`, `(`, `+`, `∥`) the printer writes right before it, so
  * that a comment on a step of a CPS spine stands above the line that begins
  * with that step's `.`, and a comment on an operand above its `+`; a run
  * before the text's first token stands before the text, and a run after its
  * last token after it; a run of blank lines alone stays only where the
  * token after it starts a line. A part of the text with a comment or a line
  * break of the text inside, anchored the same way, breaks on lines as a
  * part wider than a line does (`ReadableText.Printed.brokenText`), so that
  * a spine holding one alternates its expressions and parameter lists, one
  * per line, as far as it: a text written on lines stays on lines, its
  * parameter lists and arguments alternating, and
  * the breaks the layout does not allow are dropped. A line break with no
  * comment stands before the same name or literal, moved back over no more
  * opening tokens than the text writes between the break and it, where the
  * text writes no other token there, so that a break between `λ` and `.`
  * stays inside the parameter list; else after the same name or literal and
  * no more closing parentheses than the text writes between it and the
  * break, where the text writes no other token there, so that a break before
  * a `)` stays inside the parentheses; else where a comment would stand. One
  * that falls between the `λ` and the `.` of a printed `λ.` stands after it,
  * which breaks the same spine. The anchors are tokens rather than subterms, since
  * where a subterm begins depends on the parentheses the printer writes, and
  * the comment would then move each time the text is formatted again.
  */
object SourceFormatting:

  /** The URI the text is located in while it is formatted. */
  private val uri: java.net.URI = java.net.URI.create("formatted:text")

  /** The text formatted, read in the scope of the enclosing names
    * (`Lambdalattice.locatedInScope`). Throws the reader's errors when the
    * text does not read in that scope, and `IllegalStateException` when the
    * formatted text reads to another term or holds other comments, a defect
    * of the formatter.
    */
  def formatted(enclosing: Vector[String], text: String)(using access: gezi.ir.StorageAccess): String =
    val (term, spans) = Lambdalattice.locatedInScope(enclosing, text)
    val (instruction, map) = Defunctionalization.locatedThunkInstruction(term, spans, uri)(using gezi.ir.NoFacts)
    val printed = ReadableText.writtenBack(instruction, map, ReadableText.SourceText.of(uri, text), enclosing.size)(using gezi.ir.NoFacts, access)
    val written = laidOut(printed, layoutRuns(Lambdalattice.lexemes(text)))
    if Lambdalattice.locatedInScope(enclosing, written)._1 != term then
      throw IllegalStateException(s"the formatted text reads to another term:\n$written")
    if comments(written) != comments(text) then
      throw IllegalStateException(s"the formatted text holds other comments:\n$written")
    written

  /** The comments of a text, in order. */
  private def comments(text: String): Vector[String] =
    Lambdalattice.lexemes(text).collect { case Lexeme.Comment(written) => written.stripTrailing }

  /** A run of white space and comments of the text that holds a line
    * break: the code point offset of the token after it, none after the
    * last token; its comments and blank lines in order, a blank line a
    * `Space` of two line feeds; the number of tokens between the last name
    * or literal and it when all of them are closing parentheses, none when
    * another token is among them or no name or literal is before it; and
    * the number of tokens between it and the next name or literal when all
    * of them are opening tokens, none when another token is among them.
    */
  private final case class LayoutRun(before: Option[Int], layout: Vector[Lexeme], closing: Option[Int], opening: Option[Int])

  /** The runs of the lexemes that hold a line break. */
  private def layoutRuns(lexemes: Vector[Lexeme]): Vector[LayoutRun] =
    def kept(pending: Vector[Lexeme]): Vector[Lexeme] = pending.collect {
      case comment: Lexeme.Comment                                 => comment
      case Lexeme.Space(written) if written.count(_ == '\n') >= 2 => Lexeme.Space("\n\n")
    }
    val kinds = lexemes.collect { case token: Lexeme.Token => token.kind }
    def openingFrom(index: Int): Option[Int] =
      val leading = kinds.drop(index).takeWhile(kind => !spelled(kind))
      Option.when(leading.forall(opening))(leading.size)
    // The runs, the pending layout, the offset, the token index and the
    // closing parentheses since the last name or literal.
    val (runs, pending, _, _, _) = lexemes.foldLeft((Vector.empty[LayoutRun], Vector.empty[Lexeme], 0, 0, Option.empty[Int])) {
      case ((runs, pending, offset, index, closing), token: Lexeme.Token) =>
        (
          if lineBroken(pending) then runs :+ LayoutRun(Some(offset), kept(pending), closing, openingFrom(index)) else runs,
          Vector.empty,
          offset + codePoints(token.written),
          index + 1,
          token.kind match
            case kind if spelled(kind)            => Some(0)
            case kind if closingParenthesis(kind) => closing.map(_ + 1)
            case _                                => None
        )
      case ((runs, pending, offset, index, closing), layout) => (runs, pending :+ layout, offset + codePoints(layout.written), index, closing)
    }
    if lineBroken(pending) then runs :+ LayoutRun(None, kept(pending), None, None) else runs

  /** Whether a token is a name or a literal, which the printer marks where
    * the text spells it.
    */
  private def spelled(kind: TokenKind): Boolean = kind match
    case TokenKind.Name(_) | TokenKind.StringLiteral(_) | TokenKind.CborLiteral(_) => true
    case _                                                                         => false

  /** Whether the white space and comments between two tokens hold a line
    * break; a comment ends with one.
    */
  private def lineBroken(pending: Vector[Lexeme]): Boolean = pending.exists {
    case Lexeme.Comment(_) => true
    case layout            => layout.written.contains('\n')
  }

  private def closingParenthesis(kind: TokenKind): Boolean = kind match
    case TokenKind.CloseParenthesis => true
    case _                          => false

  private def codePoints(written: String): Int = written.codePointCount(0, written.length)

  /** The printed text broken by `ReadableText.Printed.brokenText`, each run
    * inside the text breaking the parts around it, the comments and blank
    * lines of the runs put back before their tokens, wrapped in parentheses
    * when it spans lines and is no right spine (`LambdalatticeLayout.isSpine`),
    * and laid out with `ParameterLists.Prefixed`.
    */
  private def laidOut[C <: gezi.ir.NativeSpecializer & Singleton](printed: ReadableText.Printed[C], runs: Vector[LayoutRun]): String =
    val marks = sourceMarks(printed.pieces)
    // The tokens of the text on one line, which are the broken text's.
    val tokens = Lambdalattice.lexemes(printed.text).collect { case token: Lexeme.Token => token }
    val printedTokens = printed.pieces.collect { case ReadableText.Piece.Token(text) => ReadableText.tokenCount(text) }.sum
    assert(tokens.size == printedTokens, s"the text has ${tokens.size} tokens, the pieces $printedTokens")
    // The name or literal after each run, none after the last.
    val marked = runs.map(run => run.before.flatMap(offset => marks.collectFirst { case (start, index) if start >= offset => index }))
    // The token each run's comments and blank lines stand before.
    val targets = marked.lazyZip(runs).map((mark, run) => mark.map(opened(tokens, _)) -> run.layout)
    // Each run inside the text breaks the parts around it, a run with a
    // comment where the comment stands. Its blank lines stay where its token
    // starts a line, after a line break of the broken text or a comment, and
    // are dropped elsewhere, where they would put a line break of their own.
    val breaks = marked
      .lazyZip(runs)
      .flatMap((mark, run) =>
        val previous = run.before.flatMap(offset => marks.takeWhile(_._1 < offset).lastOption.map(_._2))
        val after = previous.zip(run.closing).map((index, closing) =>
          index + 1 + math.min(closing, tokens.drop(index + 1).takeWhile(token => closingParenthesis(token.kind)).size)
        )
        val before = mark.zip(run.opening).map((index, opening) => index - math.min(opening, index - opened(tokens, index)))
        val commentStands = mark.map(opened(tokens, _))
        (if holdsComment(run.layout) then commentStands else before.orElse(after).orElse(commentStands)).map(index =>
          if index > 0 && index < tokens.size then
            (tokens(index - 1).kind, tokens(index).kind) match
              case (TokenKind.Lambda, TokenKind.Dot) => index + 1
              case _                                 => index
          else index
        )
      )
      .filter(index => index > 0 && index < tokens.size)
      .toSet
    val commented = targets.collect { case (Some(index), layout) if index > 0 && holdsComment(layout) => index }.toSet
    val broken = Lambdalattice.lexemes(printed.brokenText(ReadableText.lineWidth, breaks))
    assert(
      broken.collect { case Lexeme.Token(_, written) => written } == tokens.map(_.written),
      "the broken text has other tokens than the text on one line"
    )
    val lineStarts = commented ++ lineStartsOf(broken)
    val kept = targets.filter((target, layout) =>
      layout.nonEmpty && (holdsComment(layout) || target.forall(index => index == 0 || lineStarts(index)))
    )
    val wrapped = (broken.exists(_.written.contains('\n')) || commented.nonEmpty) && !LambdalatticeLayout.isSpine(broken)
    // The token indices of the wrapped text: a run before the first token
    // stands before the opening parenthesis.
    val shifted = kept.map((target, layout) => (target.map(index => if wrapped && index > 0 then index + 1 else index), layout))
    val body = if wrapped then (Lexeme.Token(TokenKind.OpenParenthesis, "(") +: broken) ++ Vector(
      Lexeme.Space("\n"),
      Lexeme.Token(TokenKind.CloseParenthesis, ")")
    ) else broken
    val before = shifted.collect { case (Some(index), layout) => index -> layout }.groupMapReduce(_._1)(_._2)(_ ++ _)
    val after = shifted.collect { case (None, layout) => layout }.flatten
    val (withRuns, _) = body.foldLeft((Vector.empty[Lexeme], 0)) {
      case ((written, index), token: Lexeme.Token) => (written ++ before.getOrElse(index, Vector.empty) :+ token, index + 1)
      case ((written, index), layout)              => (written :+ layout, index)
    }
    LambdalatticeLayout.laidOut(withRuns ++ after, LambdalatticeLayout.ParameterLists.Prefixed)

  /** The index of the first token of the run of opening tokens (`λ`, `.`,
    * `(`, `+`, `∥`) that ends right before the token at the index, the index
    * itself when no such token is before it: a name or a literal written after
    * them begins the subterm, step or operand they open.
    */
  @scala.annotation.tailrec
  private def opened(tokens: Vector[Lexeme.Token], index: Int): Int =
    if index > 0 && opening(tokens(index - 1).kind) then opened(tokens, index - 1) else index

  private def opening(kind: TokenKind): Boolean = kind match
    case TokenKind.Lambda | TokenKind.Dot | TokenKind.OpenParenthesis | TokenKind.Choice | TokenKind.Parallel => true
    case _                                                                                                   => false

  private def holdsComment(layout: Vector[Lexeme]): Boolean = layout.exists {
    case Lexeme.Comment(_) => true
    case _                 => false
  }

  /** The indices of the tokens of the lexemes that a line break comes right
    * before.
    */
  private def lineStartsOf(lexemes: Vector[Lexeme]): Set[Int] =
    lexemes
      .foldLeft((Set.empty[Int], 0, false)) {
        case ((found, index, broke), _: Lexeme.Token) => (if broke then found + index else found, index + 1, false)
        case ((found, index, broke), layout)          => (found, index, broke || layout.written.contains('\n'))
      }
      ._1

  /** For each source mark of the pieces, in order, the code point offset it
    * marks and the index of the name or literal it marks, after the `(` of a
    * literal written in parentheses.
    */
  private def sourceMarks(pieces: Vector[ReadableText.Piece]): Vector[(Int, Int)] =
    // The marks, the count of tokens, and the offset of a mark whose name or
    // literal is still to come, after the `(` of a literal written in
    // parentheses.
    pieces
      .foldLeft((Vector.empty[(Int, Int)], 0, Option.empty[Int])) {
        case ((marks, count, _), ReadableText.Piece.Source(start)) => (marks, count, Some(start))
        case ((marks, count, Some(start)), ReadableText.Piece.Token(text)) if ReadableText.tokenCount(text) > 0 && text != "(" =>
          (marks :+ (start -> count), count + ReadableText.tokenCount(text), None)
        case ((marks, count, pending), ReadableText.Piece.Token(text)) => (marks, count + ReadableText.tokenCount(text), pending)
        case (state, _)                                                => state
      }
      ._1
