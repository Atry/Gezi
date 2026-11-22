package gezi.jupyter.kernel

import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.Expectation
import gezi.frontend.Lambdalattice
import gezi.frontend.LambdalatticeMalformed
import gezi.frontend.LambdalatticeProblem
import gezi.frontend.Lexeme
import gezi.frontend.Literal
import gezi.frontend.Literals
import gezi.frontend.NameSpelling
import gezi.frontend.SyntaxError
import gezi.frontend.TokenKind
import gezi.ir.Instruction

/** A key path a cell writes at its top, the literals of a partial function's
  * leading binders, with their spellings as the cell writes them.
  */
final case class OutputKey(literals: Vector[Literal], spellings: Vector[String]):

  /** Whether the key path is under `"io"`: its member is a Moore machine
    * state the kernel runs by the FFI. The one key the kernel reserves.
    * DOWNGRADE: it weakens the rule that the host dispatches on no
    * lambdalattice string, and the rule that the kernel enforces no naming
    * of what a cell binds. It reads only the literals the cell's text writes,
    * never a string a reading computes, and changes no term's meaning: an
    * output key changes only what the kernel outputs.
    */
  def isIo: Boolean = literals.headOption.contains(OutputKey.io)

  /** The key path as the cell writes it. */
  def shown: String = spellings.mkString(" ")

object OutputKey:
  val io: Literal = Literal.text("io")

/** The output keys of a cell's content. A cell may be any closed term, and
  * every cell is joined with the others by choice, but only a content that
  * is a chain of + of partial functions outputs anything, so an import a
  * member needs is written inside the partial function that outputs it:
  * when the content is a chain of + whose every operand is a partial
  * function, an abstraction whose first binder is a literal, written bare
  * or in parentheses, the key path of each, its leading literal binders;
  * none otherwise. Read off the cell's tokens, as the text writes them: a
  * key a reading would compute is no output key.
  */
object CellContent:

  def outputKeys(content: String): Vector[OutputKey] = outputKeys(Lambdalattice.lexemes(content))

  /** `outputKeys` of the content whose lexemes these are. */
  def outputKeys(lexemes: Vector[Lexeme]): Vector[OutputKey] =
    val tokens = lexemes.collect { case Lexeme.Token(kind, written) if kind != TokenKind.End => (kind, written) }
    if tokens.isEmpty || topLevel(tokens).exists(_._1 == TokenKind.Parallel) then Vector.empty
    else
      val keys = operands(tokens).map(operand => partialFunctionKey(unparenthesized(operand)))
      if keys.forall(_.nonEmpty) then keys.flatten else Vector.empty

  private type Token = (TokenKind, String)

  /** The tokens at parenthesis depth 0. */
  private def topLevel(tokens: Vector[Token]): Vector[Token] =
    depths(tokens).zip(tokens).collect { case (0, token) => token }

  /** The parenthesis depth each token stands at, a parenthesis at the depth
    * outside it.
    */
  private def depths(tokens: Vector[Token]): Vector[Int] =
    tokens
      .scanLeft((0, 0)) { case ((_, depth), (kind, _)) =>
        kind match
          case TokenKind.OpenParenthesis  => (depth, depth + 1)
          case TokenKind.CloseParenthesis => (depth - 1, depth - 1)
          case _                          => (depth, depth)
      }
      .drop(1)
      .map(_._1)

  /** The operands of the chain of + at depth 0. */
  private def operands(tokens: Vector[Token]): Vector[Vector[Token]] =
    depths(tokens).zip(tokens).foldLeft(Vector(Vector.empty[Token])) {
      case (done, (0, (TokenKind.Choice, _))) => done :+ Vector.empty
      case (done, (_, token))                 => done.init :+ (done.last :+ token)
    }

  /** The operand without the parentheses written around the whole of it. */
  @annotation.tailrec
  private def unparenthesized(operand: Vector[Token]): Vector[Token] =
    val wrapped = operand.size >= 2 && operand.head._1 == TokenKind.OpenParenthesis && operand.last._1 == TokenKind.CloseParenthesis &&
      depths(operand).zipWithIndex.forall((depth, index) => index == operand.size - 1 || index == 0 || depth >= 1)
    if wrapped then unparenthesized(operand.slice(1, operand.size - 1)) else operand

  /** The key path of a partial function, `λ L1 … Ln B… . M` with n ≥ 1, each
    * Li a literal, bare or in parentheses; none for any other operand.
    */
  private def partialFunctionKey(operand: Vector[Token]): Option[OutputKey] =
    operand.headOption match
      case Some((TokenKind.Lambda, _)) =>
        val literals = leadingLiterals(operand.drop(1), Vector.empty)
        Option.when(literals.nonEmpty && operand.exists(_._1 == TokenKind.Dot))(OutputKey(literals.map(_._1), literals.map(_._2)))
      case _ => None

  @annotation.tailrec
  private def leadingLiterals(binders: Vector[Token], found: Vector[(Literal, String)]): Vector[(Literal, String)] =
    binders match
      case (TokenKind.StringLiteral(text), written) +: rest => leadingLiterals(rest, found :+ (Literal.text(text) -> written))
      case (TokenKind.CborLiteral(literal), written) +: rest => leadingLiterals(rest, found :+ (literal -> written))
      case (TokenKind.OpenParenthesis, _) +: (TokenKind.StringLiteral(text), written) +: (TokenKind.CloseParenthesis, _) +: rest =>
        leadingLiterals(rest, found :+ (Literal.text(text) -> s"($written)"))
      case (TokenKind.OpenParenthesis, _) +: (TokenKind.CborLiteral(literal), written) +: (TokenKind.CloseParenthesis, _) +: rest =>
        leadingLiterals(rest, found :+ (literal -> s"($written)"))
      case _ => found

/** Where a notebook stands in the tree of URIs: the keys of its `file:`
  * URI's mixin path, `file` and then the levels of its absolute path from the
  * file system's root, the notebook's own without the extension `.ipynb`.
  */
final case class NotebookLocation(keys: Vector[String]):

  /** The text the kernel writes before a cell's content: each level's self
    * then its key, the root's self `uri` first, each self named by the
    * name that spells its key (`NameSpelling.escaped`): the cell
    * `\"io" "key1" jvm. ...` of the notebook `/path/to/demo.ipynb` is read as
    * `\uri "file" file "path" path "to" to "demo" demo. \"io" "key1" jvm. ...`,
    * so that the content names the levels as the files of the tree name theirs.
    */
  def prefix: String =
    keys.map(key => s"${NotebookLocation.written(key)} ${NameSpelling.escaped(key)}").mkString("λuri ", " ", ".")

object NotebookLocation:

  val extension: String = ".ipynb"

  /** The location of the notebook at the path. */
  def of(notebook: Path): NotebookLocation =
    val absolute = notebook.toAbsolutePath.normalize
    val levels = (0 until absolute.getNameCount).map(index => absolute.getName(index).toString).toVector
    NotebookLocation("file" +: (if levels.isEmpty then levels else levels.init :+ levels.last.stripSuffix(extension)))

  /** The text string of CBOR's diagnostic notation that spells the key: its
    * quotation marks and backslashes escaped, and its control characters
    * written as `\u` escapes.
    */
  def written(key: String): String =
    key.flatMap {
      case '"'                       => "\\\""
      case '\\'                      => "\\\\"
      case character if character < ' ' => f"\\u${character.toInt}%04x"
      case character                 => character.toString
    }.mkString("\"", "", "\"")

/** A cell of the notebook: its Jupyter cell id, its term (its content read
  * after the notebook's prefix) and its output keys.
  */
final case class NotebookCell(id: String, term: Instruction, outputs: Vector[OutputKey])

object NotebookCell:

  /** The cell of the content, read after the location's prefix. Throws
    * `gezi.frontend.LambdalatticeMalformed` for a content that does not read
    * there.
    *
    * COST. Each key of the prefix is a literal binder of a variable arguments
    * partial function, an abstraction for each of its bits, so a read costs
    * in proportion to the bits of the location's keys. MEASURED 2026-11-20
    * (a scratch probe on 1d679efda, warm, CPUs 8 to 11, nice 10): a content
    * of two partial functions after the prefix of
    * `file:///tmp/notebook16823966089698366501/law.ipynb`, its keys 37 bytes,
    * read in 95 to 161 ms; reading one member of it took 3,171 steps.
    * MEASURED 2026-11-20 again (a scratch probe on f8ea90699, warm, 200
    * rounds each, CPUs 10 and 11 shared with two other JVMs, load about 12):
    * the content `(λ"ab". (λx. x))` after the prefix of the keys `file`,
    * `n`, `law`: the parse 10.2 ms and the conversion to the IR 13.9 ms. The
    * content is lexed once for both of its checks.
    */
  def read(id: String, content: String, location: NotebookLocation): NotebookCell =
    val lexemes = Lambdalattice.lexemes(content)
    closingTooMany(lexemes).foreach(position =>
      throw LambdalatticeMalformed(
        LambdalatticeProblem.Syntax(SyntaxError.Expected(Expectation.End, TokenKind.CloseParenthesis), openingLength(location) + position)
      )
    )
    val term = Defunctionalization.thunkInstruction(Lambdalattice.term(s"${opening(location)}$content\n)"))
    NotebookCell(id, term, CellContent.outputKeys(lexemes))

  /** The text the kernel writes before a cell's content, the location's
    * prefix and an opening parenthesis on a line of its own; the offsets of
    * `read`'s syntax errors are counted from its start.
    */
  def opening(location: NotebookLocation): String = s"${location.prefix} (\n"

  /** The code points of `opening`. */
  def openingLength(location: NotebookLocation): Int = codePoints(opening(location))

  /** Whether the problem of a content that does not read is that the content
    * ends too soon, so that more text could make it read: a string literal
    * left open, or a syntax error at the end of the content, where the
    * kernel's closing parenthesis stands. A console asks for another line
    * then (`CellInterpreter.isComplete`).
    */
  def endsTooSoon(problem: LambdalatticeProblem, content: String, location: NotebookLocation): Boolean = problem match
    case LambdalatticeProblem.Syntax(SyntaxError.UnterminatedString, _) => true
    case LambdalatticeProblem.Syntax(_, position)                     => position >= openingLength(location) + codePoints(content)
    case LambdalatticeProblem.UnboundName(_)                          => false

  private def codePoints(text: String): Int = text.codePointCount(0, text.length)

  /** The offset, in code points from 0, of the first `)` of the content,
    * given by its lexemes, that closes no `(` of the content. The content is read inside the
    * parentheses the kernel writes around it, so without this check a
    * content such as `f) (g` would close them and read as the term `(f) (g)`;
    * the content read alone has a syntax error there.
    */
  private def closingTooMany(lexemes: Vector[Lexeme]): Option[Int] =
    lexemes
      .foldLeft((0, 0, Option.empty[Int])) {
        case (found @ (_, _, Some(_)), _) => found
        case ((offset, depth, None), lexeme) =>
          val written = lexeme.written
          val next = lexeme match
            case Lexeme.Token(TokenKind.OpenParenthesis, _)  => depth + 1
            case Lexeme.Token(TokenKind.CloseParenthesis, _) => depth - 1
            case _                                           => depth
          (offset + codePoints(written), next, Option.when(next < 0)(offset))
      }
      ._3

/** The notebook: the tree of URIs, whose visible subtree is a directory
  * (`DirectoryTree.rootOf`), joined by choice with its cells, each a mixin
  * at the notebook's location, so that each cell is a mixin based on partial
  * functions that reaches the other cells through its self reference; the
  * choice includes the expansion of the tree's URIs.
  *
  * A cell run again under its id replaces the cell of that id, after the
  * persistent cell ids of David Koop's dfkernel and the cells as definitions
  * of Pluto.jl. Replacing a cell undoes no call its earlier version made.
  */
final case class Notebook(location: NotebookLocation, tree: Instruction, cells: Vector[NotebookCell]):

  /** The notebook with the cell, which replaces the cell of its id. */
  def added(cell: NotebookCell): Notebook =
    val at = cells.indexWhere(_.id == cell.id)
    copy(cells = if at < 0 then cells :+ cell else cells.updated(at, cell))

  /** The tree and the cells joined by choice. */
  def mixin: Instruction = cells.foldLeft(tree)((joined, cell) => Instruction.Choice(joined, cell.term))

  /** The member at the output key: the notebook's level reached by the
    * projections of the location's keys (`DirectoryTree.lookedUp`), then one
    * more self-application and the key path's literals spread into their
    * elements. Nothing is evaluated.
    */
  def member(key: OutputKey): Instruction =
    val level = DirectoryTree.lookedUp(mixin, location.keys)
    key.literals
      .flatMap(Literals.arguments)
      .foldLeft(Instruction.Apply(level, level))((function, element) => Instruction.Apply(function, Defunctionalization.thunkInstruction(element)))

