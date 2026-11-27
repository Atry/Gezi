package gezi.frontend

/** The layout of a lambdalattice text (`CONTRIBUTING.md`, "lambdalattice
  * layout: no right-associative parentheses, CPS one step per line"): indent
  * only at parentheses, and break a line only after `.` and before +, ∥, `(`
  * and `)`, a `(` that starts a line followed by a space so that what follows
  * lines up. In detail (the inline rules):
  *
  *   - The places listed are where a line may break, not where it must: the
  *     author's line breaks that stand at such a place (after `.`, before +, ∥,
  *     `(` and `)`) are kept, the others become one space. A comment keeps a
  *     line of its own wherever it stands, and the token after it starts a
  *     line.
  *   - Parentheses whose contents span lines put their `(` and their `)` in one
  *     column: each starts a line, but a `(` that follows only prefixes on its
  *     line. A prefix is a +, a ∥ or a spanning `(` written first on a line or
  *     after other prefixes; an operator before a spanning `(` is moved to the
  *     start of the line, so that the break falls before the operator.
  *   - A line starting with a prefix or with the `)` of spanning parentheses
  *     stands at the column of the parentheses it belongs to, the innermost
  *     spanning ones open (the first column outside all); any other line stands
  *     two columns in from them. A prefix is followed by one space, so that
  *     what follows stands two columns in; ∥ starting a line is written `∥`,
  *     never the two-column `||`.
  *   - Within a line, tokens are one space apart, except none after λ, `(` and
  *     `[`, and none before `)`, `]`, `,` and `.`. Runs of blank lines become
  *     one; none starts or ends the text.
  *   - A list is laid out as parentheses are, for the problems' data files: a
  *     line may also break after `,` and before `[` and `]`, and the `[` and
  *     the `]` of a list whose items span lines stand in one column, the `[`
  *     followed by one space, the items two columns in.
  */
object LambdalatticeLayout:

  /** A token of the text with the pieces of layout before it, white space and
    * comments, in order.
    */
  private final case class Item(
      kind: TokenKind,
      written: String,
      before: Vector[Lexeme]
  )

  /** Where a parameter list may stand on lines of its own.
    *
    *   - `Inline`: the inline rules alone; a parameter list stays on the line
    *     of the `λ` it begins with, and a line may break after its `.`.
    *   - `Prefixed`: the multi-line CPS layout of CONTRIBUTING.md,
    *     "lambdalattice layout: no right-associative parentheses, CPS one step
    *     per line", where siblings have the same indent: a line may also break
    *     before a parameter list's `λ` and before its `.`, and a `λ` or a `.`
    *     that starts a line is a prefix in the column of the block it belongs
    *     to, followed by one space, the rest two columns in. A block is a pair
    *     of spanning parentheses, whose column is two in from its `(` (where +
    *     and ∥ and its `)` stand), or the whole text, whose column is the
    *     first. A line of an expression after the block's first `λ` (since its
    *     last + or ∥) stands two columns in from the block's column, as the
    *     expression after a `.` does; any other line at the block's column. A
    *     `λ` never starts a line after a `(` or an operator, a comment aside:
    *     it stays on their line, a prefix when the operand it begins spans
    *     lines. An operand that spans lines as a right spine (a `λ` or a `.` of
    *     it starts a line) and begins with an expression gets a parameter list
    *     of no binder first, `λ` and a `.` starting the next line (`λ. M` is
    *     M), so that every `.` line of a spine follows a `λ` line.
    */
  enum ParameterLists:
    case Inline
    case Prefixed

  /** The text of the pieces laid out by the inline rules
    * (`ParameterLists.Inline`).
    */
  def laidOut(lexemes: Vector[Lexeme]): String =
    laidOut(lexemes, ParameterLists.Inline)

  /** The text of the pieces laid out, a parameter list standing on lines of its
    * own as `parameterLists` says. Throws `IllegalArgumentException` when the
    * parentheses of the pieces do not pair, which they always do in a text the
    * reader reads.
    */
  def laidOut(lexemes: Vector[Lexeme], parameterLists: ParameterLists): String =
    val prefixedLists = parameterLists == ParameterLists.Prefixed
    val (groupedItems, trailing) = grouped(lexemes)
    val items =
      if prefixedLists then spinesOpened(groupedItems) else groupedItems
    if items.isEmpty then joined(layoutLines(trailing, 0))
    else
      val pairs = paired(items)
      val authored = items.indices
        .map(index =>
          index > 0 && (commented(items(index)) ||
            (authoredBreak(
              items,
              index,
              prefixedLists
            ) && !(prefixedLists && joinedLambda(items, index))))
        )
        .toVector
      val spanning =
        pairs.filter((open, close) => (open + 1 to close).exists(authored))
      val closing = spanning.map(_.swap)
      val (starts, prefixed) =
        lineStarts(items, authored, spanning, closing, prefixedLists)
      joined(
        written(
          items,
          starts,
          prefixed,
          spanning,
          closing,
          prefixedLists
        ) ++ layoutLines(trailing, 0)
      )

  /** The tokens with the layout before each, and the layout after the last. */
  private def grouped(lexemes: Vector[Lexeme]): (Vector[Item], Vector[Lexeme]) =
    lexemes.foldLeft((Vector.empty[Item], Vector.empty[Lexeme])) {
      case ((items, pending), Lexeme.Token(kind, written)) =>
        (items :+ Item(kind, written, pending), Vector.empty)
      case ((items, pending), layout) => (items, pending :+ layout)
    }

  /** The index of each `(` with the index of the `)` that closes it. */
  private def paired(items: Vector[Item]): Map[Int, Int] =
    val (pairs, open) =
      items.zipWithIndex.foldLeft((Map.empty[Int, Int], List.empty[Int])) {
        case ((pairs, open), (Item(TokenKind.OpenParenthesis, _, _), index)) =>
          (pairs, index :: open)
        case (
              (pairs, opening :: rest),
              (Item(TokenKind.CloseParenthesis, _, _), index)
            ) =>
          (pairs.updated(opening, index), rest)
        case ((_, Nil), (Item(TokenKind.CloseParenthesis, _, _), index)) =>
          throw IllegalArgumentException(
            s"the token $index closes no parenthesis"
          )
        case (state, _) => state
      }
    if open.nonEmpty then
      throw IllegalArgumentException(
        s"the tokens $open open parentheses that nothing closes"
      )
    pairs

  /** A comment stands before the token. */
  private def commented(item: Item): Boolean = item.before.exists {
    case Lexeme.Comment(_) => true
    case _                 => false
  }

  /** The author broke the line before the token, at a place a line may break:
    * after `.`, before +, ∥, `(` and `)`, and with `prefixedLists` before `λ`
    * and `.` too.
    */
  private def authoredBreak(
      items: Vector[Item],
      index: Int,
      prefixedLists: Boolean
  ): Boolean =
    items(index).before.exists(_.written.contains('\n')) &&
      (items(index - 1).kind == TokenKind.Dot || isOperator(items(index)) ||
        (prefixedLists && isParameterListMark(items(index))) ||
        (items(index).kind match
          case TokenKind.OpenParenthesis | TokenKind.CloseParenthesis => true
          case _                                                      => false))

  private def isOperator(item: Item): Boolean =
    item.kind == TokenKind.Choice || item.kind == TokenKind.Parallel

  /** The `λ` that begins a parameter list or the `.` that ends it. */
  private def isParameterListMark(item: Item): Boolean =
    item.kind == TokenKind.Lambda || item.kind == TokenKind.Dot

  /** For each token, whether it starts a line, and whether everything before it
    * on its line is prefixes; computed from the left, since each token's
    * answers depend only on those before it.
    */
  private def lineStarts(
      items: Vector[Item],
      authored: Vector[Boolean],
      spanning: Map[Int, Int],
      closing: Map[Int, Int],
      prefixedLists: Boolean
  ): (Vector[Boolean], Vector[Boolean]) =
    val (starts, prefixed, _) = items.indices.foldLeft(
      (Vector.empty[Boolean], Vector.empty[Boolean], false)
    ) { case ((starts, prefixed, onlyPrefixesSoFar), index) =>
      val operatorBeforeSpanning =
        isOperator(items(index)) && spanning.contains(index + 1)
      val starting = index == 0 || authored(index) || closing.contains(
        index
      ) || operatorBeforeSpanning ||
        (spanning.contains(index) && !onlyPrefixesSoFar)
      val joinedMark = prefixedLists && joinedLambda(
        items,
        index
      ) && (index + 1 until operandEnd(items, index)).exists(authored)
      val markPrefix = prefixedLists && isParameterListMark(
        items(index)
      ) && (starting || joinedMark)
      val prefix = (isOperator(items(index)) || spanning.contains(
        index
      ) || markPrefix) && (starting || onlyPrefixesSoFar)
      (starts :+ starting, prefixed :+ (!starting && onlyPrefixesSoFar), prefix)
    }
    (starts, prefixed)

  /** The token is a `λ` right after a `(` or an operator, which stays on their
    * line.
    */
  private def joinedLambda(items: Vector[Item], index: Int): Boolean =
    index > 0 && items(index).kind == TokenKind.Lambda &&
      (items(index - 1).kind == TokenKind.OpenParenthesis || isOperator(
        items(index - 1)
      ))

  /** The index of the token that ends the operand beginning at `start`: the
    * first + or ∥ outside the parentheses begun after `start`, the `)` of the
    * parentheses it is in, or the end of the tokens.
    */
  private def operandEnd(items: Vector[Item], start: Int): Int =
    @scala.annotation.tailrec
    def scanned(index: Int, depth: Int): Int =
      if index >= items.size then index
      else
        items(index).kind match
          case TokenKind.OpenParenthesis => scanned(index + 1, depth + 1)
          case TokenKind.CloseParenthesis if depth == 0 => index
          case TokenKind.CloseParenthesis => scanned(index + 1, depth - 1)
          case _ if depth == 0 && isOperator(items(index)) => index
          case _ => scanned(index + 1, depth)
    scanned(start, 0)

  /** The operand beginning at `start` spans lines as a right spine: a `λ` or a
    * `.` outside the parentheses begun after `start` has a line break or a
    * comment before it.
    */
  private def spineSpansLines(items: Vector[Item], start: Int): Boolean =
    val end = operandEnd(items, start)
    val (found, _) = (start until end).foldLeft((false, 0)) {
      case ((found, depth), index) =>
        items(index).kind match
          case TokenKind.OpenParenthesis  => (found, depth + 1)
          case TokenKind.CloseParenthesis => (found, depth - 1)
          case _                          =>
            (
              found || (index > start && depth == 0 && isParameterListMark(
                items(index)
              ) && breaksBefore(items(index))),
              depth
            )
    }
    found

  /** A line break or a comment stands before the token. */
  private def breaksBefore(item: Item): Boolean =
    commented(item) || item.before.exists(_.written.contains('\n'))

  /** The tokens with a parameter list of no binder, `λ` and `.`, put before
    * each operand that spans lines as a right spine and begins with an
    * expression (`λ. M` is M): at the start of the text, after a `(` and after
    * an operator. The `λ` stays where the operand began, the layout before the
    * operand moves before the `.`, which starts a line; at the start of the
    * text, the layout before it (a file's leading comments) stays before the
    * `λ`.
    */
  private def spinesOpened(items: Vector[Item]): Vector[Item] =
    items.indices.toVector.flatMap(index =>
      val item = items(index)
      val operandStart = index == 0 || items(
        index - 1
      ).kind == TokenKind.OpenParenthesis || isOperator(items(index - 1))
      val opened =
        operandStart && item.kind != TokenKind.Lambda && item.kind != TokenKind.CloseParenthesis &&
          !isOperator(item) && spineSpansLines(items, index)
      if !opened then Vector(item)
      else
        val (lambdaBefore, dotBefore) =
          if index == 0 then (item.before, Vector(Lexeme.Space("\n")))
          else if item.before.exists(_.written.contains('\n')) then
            (Vector.empty, item.before)
          else (Vector.empty, item.before :+ Lexeme.Space("\n"))
        Vector(
          Item(TokenKind.Lambda, "λ", lambdaBefore),
          Item(TokenKind.Dot, ".", dotBefore),
          item.copy(before = Vector(Lexeme.Space(" ")))
        )
    )

  /** Whether the text, laid out with `ParameterLists.Prefixed`, needs no
    * parentheses around it when it spans lines: it is a right spine, a `λ` or a
    * `.` outside its parentheses having a line break or a comment before it,
    * and it holds no + or ∥ outside its parentheses: a text that is a right
    * spine on lines needs no outer parentheses.
    */
  def isSpine(lexemes: Vector[Lexeme]): Boolean =
    val (items, _) = grouped(lexemes)
    items.nonEmpty && operandEnd(
      items,
      0
    ) == items.size && (items.head.kind == TokenKind.Lambda || spineSpansLines(
      items,
      0
    )) &&
    (1 until items.size).exists(index =>
      isParameterListMark(items(index)) && breaksBefore(
        items(index)
      ) && depthAt(items, index) == 0
    )

  /** The number of parentheses open before the token. */
  private def depthAt(items: Vector[Item], index: Int): Int =
    items
      .take(index)
      .foldLeft(0)((depth, item) =>
        item.kind match
          case TokenKind.OpenParenthesis  => depth + 1
          case TokenKind.CloseParenthesis => depth - 1
          case _                          => depth
      )

  /** A line of the output: its column and its text, or a blank line. */
  private enum Line:
    case Text(column: Int, text: String)
    case Blank

  /** The comments and blank lines of a piece of layout, at the column. */
  private def layoutLines(layout: Vector[Lexeme], column: Int): Vector[Line] =
    layout.flatMap {
      case Lexeme.Comment(written) =>
        Vector(Line.Text(column, written.stripTrailing))
      case Lexeme.Space(written) if written.count(_ == '\n') >= 2 =>
        Vector(Line.Blank)
      case _ => Vector.empty
    }

  /** The lines as text, runs of blank lines made one and none at the ends. */
  private def joined(lines: Vector[Line]): String =
    lines
      .foldLeft(Vector.empty[Line])((kept, line) =>
        (kept.lastOption, line) match
          case (Some(Line.Blank) | None, Line.Blank) => kept
          case _                                     => kept :+ line
      )
      .reverse
      .dropWhile(_ == Line.Blank)
      .reverse
      .map {
        case Line.Text(column, text) => " " * column + text
        case Line.Blank              => ""
      }
      .mkString("", "\n", "\n")

  /** A block the walk is in: spanning parentheses, whose `(` stands at
    * `parenthesisColumn`, or the whole text, at -2; whether a `λ` of its own
    * came since its start or its last operator, so that a line of an expression
    * stands two columns in from the block's column (`ParameterLists.Prefixed`);
    * and how many parentheses on one line are open in it.
    */
  private final case class Block(
      parenthesisColumn: Int,
      afterLambda: Boolean,
      nested: Int
  ):

    /** The column of the block: two in from its `(`. */
    def column: Int = parenthesisColumn + 2

  /** The walk over the tokens: the lines finished, the line being written (its
    * column and text), and the blocks open, innermost first, the whole text
    * last.
    */
  private final case class Walk(
      finished: Vector[Line],
      column: Int,
      text: String,
      blocks: List[Block]
  )

  private def written(
      items: Vector[Item],
      starts: Vector[Boolean],
      prefixed: Vector[Boolean],
      spanning: Map[Int, Int],
      closing: Map[Int, Int],
      prefixedLists: Boolean
  ): Vector[Line] =
    val begun =
      Walk(layoutLines(items.head.before, 0), 0, "", List(Block(-2, false, 0)))
    val walked = items.indices.foldLeft(begun)((walk, index) =>
      val current = items(index)
      val block = walk.blocks.head
      val column =
        if !starts(index) then walk.column
        else if closing.contains(index) || isOperator(current) then
          math.max(0, block.parenthesisColumn)
        else if prefixedLists && isParameterListMark(current) then block.column
        else if prefixedLists && block.afterLambda then block.column + 2
        else block.column
      val finished =
        if starts(index) && index > 0 then
          (walk.finished :+ Line.Text(walk.column, walk.text)) ++ layoutLines(
            current.before,
            column
          )
        else walk.finished
      val spelled =
        if starts(index) && current.kind == TokenKind.Parallel then "∥"
        else current.written
      val separator =
        if starts(index) then ""
        else if prefixed(index) then " "
        else spacing(items(index - 1), current)
      val before = if starts(index) then "" else walk.text + separator
      val blocks =
        if spanning.contains(index) then
          Block(column + before.length, false, 0) :: walk.blocks
        else if closing.contains(index) then walk.blocks.drop(1)
        else
          val updated = current.kind match
            case TokenKind.OpenParenthesis =>
              block.copy(nested = block.nested + 1)
            case TokenKind.CloseParenthesis =>
              block.copy(nested = block.nested - 1)
            case _ if block.nested == 0 && isOperator(current) =>
              block.copy(afterLambda = false)
            case TokenKind.Lambda if block.nested == 0 =>
              block.copy(afterLambda = true)
            case _ => block
          updated :: walk.blocks.tail
      Walk(finished, column, before + spelled, blocks)
    )
    walked.finished :+ Line.Text(walked.column, walked.text)

  /** The space between two tokens of a line. */
  private def spacing(previous: Item, next: Item): String =
    (previous.kind, next.kind) match
      case (TokenKind.Lambda | TokenKind.OpenParenthesis, _) => ""
      case (_, TokenKind.CloseParenthesis | TokenKind.Dot)   => ""
      case _                                                 => " "
