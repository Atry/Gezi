package com.yang_bo.gezi.frontend

import parsley.errors.ErrorBuilder
import parsley.errors.tokenextractors.SingleChar

/** Where a Parsley parse failed and why, as the lambdalattice reader
  * (`Lambdalattice`) reads it back: the line of the failure (counted from 1),
  * the caret, its offset in that line in UTF-16 code units, the messages of the
  * failure (`parsley.errors.combinator.fail` and the filters' messages) and the
  * items the parser expected there. The reader raises every syntax error of its
  * grammar as a message at a chosen position, with `amend`, and reads it back
  * from this value. A syntax error thrown from a parser's action is lost under
  * Parsley, whose optimizer takes actions to be pure: it drops the action of a
  * result it discards, and may run an action before a parser sequenced after it
  * (2026-11-09: a first version of the reader that threw from actions read
  * `(λx.x` and `λx.x λy.y` without an error, and threw `UnterminatedString`
  * inside a closed string).
  */
private[frontend] final case class ParsleyFailure(
    line: Int,
    caret: Int,
    messages: Vector[String],
    expected: Vector[String]
):

  /** The failure's offset in the text, in UTF-16 code units: the start of its
    * line and the caret.
    */
  def offset(text: String): Int =
    (1 until line).foldLeft(0)((lineStart, _) =>
      text.indexOf('\n', lineStart) + 1
    ) + caret

  /** The one message of the failure; a failure with none or several is a defect
    * of the grammar that raised it.
    */
  def message: String = messages match
    case Vector(only) => only
    case _            =>
      throw IllegalStateException(
        s"a parse failed with ${messages.size} messages instead of one: $this"
      )

private[frontend] object ParsleyFailure:

  /** The error builder whose errors are `ParsleyFailure`s. */
  given ErrorBuilder[ParsleyFailure] = new ErrorBuilder[ParsleyFailure]
    with SingleChar:
    type Position = Int
    type Source = Unit
    type ErrorInfoLines = ParsleyFailure
    type ExpectedItems = Vector[String]
    type Messages = Vector[String]
    type UnexpectedLine = Unit
    type ExpectedLine = Vector[String]
    type Message = String
    type LineInfo = Int
    type Item = String
    type Raw = String
    type Named = String
    type EndOfInput = String

    override def format(
        position: Position,
        source: Source,
        lines: ErrorInfoLines
    ): ParsleyFailure =
      lines.copy(line = position)
    override def pos(line: Int, column: Int): Position = line
    override def source(sourceName: Option[String]): Source = ()
    override def vanillaError(
        unexpected: UnexpectedLine,
        expected: ExpectedLine,
        reasons: Messages,
        caret: LineInfo
    ): ErrorInfoLines = ParsleyFailure(0, caret, reasons, expected)
    override def specialisedError(
        messages: Messages,
        caret: LineInfo
    ): ErrorInfoLines =
      ParsleyFailure(0, caret, messages, Vector.empty)
    override def combineExpectedItems(alternatives: Set[Item]): ExpectedItems =
      alternatives.toVector.sorted
    override def combineMessages(alternatives: Seq[Message]): Messages =
      alternatives.toVector
    override def unexpected(item: Option[Item]): UnexpectedLine = ()
    override def expected(alternatives: ExpectedItems): ExpectedLine =
      alternatives
    override def reason(reason: String): Message = reason
    override def message(message: String): Message = message
    override val numLinesBefore: Int = 0
    override val numLinesAfter: Int = 0
    override def lineInfo(
        line: String,
        linesBefore: Seq[String],
        linesAfter: Seq[String],
        errorPointsAt: Int,
        errorWidth: Int
    ): LineInfo = errorPointsAt
    override def raw(item: String): Raw = item
    override def named(item: String): Named = item
    override val endOfInput: EndOfInput = "end of input"
