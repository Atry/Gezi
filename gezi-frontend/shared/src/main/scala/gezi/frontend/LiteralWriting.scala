package gezi.frontend

import io.bullet.borer.Cbor
import io.bullet.borer.Dom
import io.bullet.borer.SimpleValue
import io.bullet.borer.Tag
import parsley.Parsley
import parsley.Parsley.eof
import scala.annotation.tailrec

/** The writer of literals in CBOR's diagnostic notation, the way back of the
  * reader `DiagnosticNotation`: the printer (`ReadableText`) writes a complete
  * literal, one no sharing cut, back as its notation.
  *
  * An item is written only when its text reads back, by `DiagnosticNotation`,
  * to the very bytes it was decoded from; any other item (a non-preferred
  * serialization, an indefinite string, an item that no literal can start with,
  * such as `true` alone) is not a literal of the text, and its bits stay terms.
  */
private[frontend] object LiteralWriting:

  /** A complete item: its text and the bytes it reads back to. */
  final case class Written(text: String, literal: Literal)

  /** The complete items the bytes start with, in order, up to the first part
    * that is not an item whose text reads back to its bytes.
    */
  def items(bytes: Vector[Byte]): Vector[Written] =
    @tailrec
    def collected(rest: Vector[Byte], found: Vector[Written]): Vector[Written] =
      item(rest) match
        case Some(written) =>
          collected(rest.drop(written.literal.bytes.length), found :+ written)
        case None => found
    collected(bytes, Vector.empty)

  /** The text of a literal standing as an argument: bare when it reads back so,
    * else in parentheses, where a number touching `(` is a tag.
    */
  def argument(written: Written): String =
    if readBack(wholeArgument, written.text).contains(written.literal) then
      written.text
    else s"(${written.text})"

  /** The text of a literal standing as a binder: bare when it reads back so,
    * else in parentheses, as `λ(3.0). M` must be written.
    */
  def binder(written: Written): String =
    if readBack(wholeBinder, written.text).contains(written.literal) then
      written.text
    else s"(${written.text})"

  /** Whether the text of a literal, which means what it means in parentheses,
    * means the same literal bare as an argument: not a tag such as `30([1])`,
    * which bare is the number 30 and an argument after it.
    */
  def bareArgument(text: String): Boolean = bare(wholeArgument, text)

  /** Whether the text of a literal means the same literal bare as a binder: not
    * a number with a fraction such as `0.5`, which as a binder is written
    * `(0.5)`.
    */
  def bareBinder(text: String): Boolean = bare(wholeBinder, text)

  private def bare(
      parser: Parsley[(Dom.Element, Literal)],
      text: String
  ): Boolean =
    readBack(parser, text).exists(literal =>
      readBack(wholeParenthesized, text).contains(literal)
    )

  /** The base of the name of a bit of a literal's bits, counted from 0, the
    * high bit of the first byte, so that the bit 5 of the literal 42 is
    * `number_42_digit_5`: the item's kind and its value, `number_42`,
    * `string_a$u002Eb`, `bytes_00ff`, or `literal_` and its notation, or the
    * bytes in hexadecimal where the bytes are no item this writer writes; then
    * `_digit_` and the bit, escaped by `NameSpelling` into a name.
    */
  def bitName(bytes: Vector[Byte], bit: Int): String =
    val element = item(bytes)
      .filter(_.literal.bytes.length == bytes.length)
      .flatMap(_ => decoded(bytes))
    val base = element match
      case Some(
            number @ (_: Dom.IntElem | _: Dom.LongElem | _: Dom.OverLongElem)
          ) =>
        written(number).map(text => s"number_$text")
      case Some(
            number @ (_: Dom.Float16Elem | _: Dom.FloatElem | _: Dom.DoubleElem)
          ) =>
        written(number).map(text => s"number_$text")
      case Some(
            big @ Dom.TaggedElem(Tag.PositiveBigNum | Tag.NegativeBigNum, _)
          ) =>
        written(big).map(text => s"number_$text")
      case Some(Dom.StringElem(value))         => Some(s"string_$value")
      case Some(byteString: Dom.ByteArrayElem) =>
        Some(s"bytes_${hexadecimalDigits(byteString.bytes.toVector)}")
      case Some(other) => written(other).map(text => s"literal_$text")
      case None        => None
    NameSpelling.escaped(
      s"${base.getOrElse(s"literal_${hexadecimalDigits(bytes)}")}_digit_$bit"
    )

  /** The item the bytes start with, when its text reads back to its bytes. */
  private def item(bytes: Vector[Byte]): Option[Written] =
    if bytes.isEmpty then None
    else
      for
        element <- decoded(bytes)
        literal <- Literal.encoding(element).toOption
        if bytes.take(literal.bytes.length) == literal.bytes.toVector
        text <- written(element)
        if readBack(wholeParenthesized, text).contains(literal)
      yield Written(text, literal)

  /** The item the bytes start with, decoded by borer, the bytes after it
    * ignored. The bytes are handed to borer as the `Array[Byte]` it decodes
    * from, an exception to NoArray for exchange with a library.
    */
  @SuppressWarnings(
    Array("gezi.warts.NoArray")
  ) // "NoArray wart可以有例外。如果用于和外部库交换，需要Array完全可以理解。我们自己当然还是优先用IArray" (the user, 2026-11-16)
  private def decoded(bytes: Vector[Byte]): Option[Dom.Element] =
    Cbor
      .decode(bytes.toArray)
      .withPrefixOnly
      .to[Dom.Element]
      .valueEither
      .toOption

  // The readers of a whole text, each made once: Parsley compiles a parser
  // the first time it runs, so a parser made per call is compiled per call.
  private val wholeArgument: Parsley[(Dom.Element, Literal)] =
    DiagnosticNotation.argumentLiteral <~ eof
  private val wholeBinder: Parsley[(Dom.Element, Literal)] =
    DiagnosticNotation.binderLiteral <~ eof
  private val wholeParenthesized: Parsley[(Dom.Element, Literal)] =
    DiagnosticNotation.parenthesizedLiteral <~ eof

  /** The literal the text reads to by the parser of a whole text. */
  private def readBack(
      parser: Parsley[(Dom.Element, Literal)],
      text: String
  ): Option[Literal] =
    parser.parse[ParsleyFailure](text).toOption.map(_._2)

  /** The notation of the item, when it has one this writer writes. */
  private def written(element: Dom.Element): Option[String] = element match
    case Dom.IntElem(value)                => Some(value.toString)
    case Dom.LongElem(value)               => Some(value.toString)
    case Dom.OverLongElem(negative, value) =>
      val magnitude = BigInt(java.lang.Long.toUnsignedString(value))
      Some((if negative then -magnitude - 1 else magnitude).toString)
    case Dom.Float16Elem(value)   => Some(floating(value.toDouble))
    case Dom.FloatElem(value)     => Some(floating(value.toDouble))
    case Dom.DoubleElem(value)    => Some(floating(value))
    case Dom.StringElem(value)    => Some(quoted(value))
    case bytes: Dom.ByteArrayElem => Some(hexadecimal(bytes.bytes))
    case Dom.BooleanElem(value)   => Some(value.toString)
    case Dom.NullElem             => Some("null")
    case Dom.UndefinedElem        => Some("undefined")
    case Dom.SimpleValueElem(SimpleValue(number)) => Some(s"simple($number)")
    case Dom.ArrayElem.Sized(elements)            =>
      all(elements.map(written)).map(_.mkString("[", ", ", "]"))
    case Dom.ArrayElem.Unsized(elements) =>
      all(elements.map(written)).map(_.mkString("[_ ", ", ", "]"))
    case map: Dom.MapElem =>
      val opening = map match
        case _: Dom.MapElem.Unsized => "{_ "
        case _                      => "{"
      all(
        map.members.toVector.map((key, value) =>
          written(key)
            .zip(written(value))
            .map((keyText, valueText) => s"$keyText: $valueText")
        )
      )
        .map(_.mkString(opening, ", ", "}"))
    case Dom.TaggedElem(tag, content) => tagged(tag, content)
    case _                            => None

  /** A tag over its content; a big integer, tag 2 or 3 over the bytes of its
    * magnitude, written as its numeral where that is the item the numeral
    * gives.
    */
  private def tagged(tag: Tag, content: Dom.Element): Option[String] =
    (tag, content) match
      case (Tag.PositiveBigNum | Tag.NegativeBigNum, bytes: Dom.ByteArrayElem)
          if bytes.bytes.nonEmpty && bytes.bytes.head != 0 && BigInt(
            1,
            bytes.bytes
          ).bitLength > 64 =>
        val magnitude = BigInt(1, bytes.bytes)
        Some((if tag == Tag.PositiveBigNum then magnitude
              else -magnitude - 1).toString)
      case _ => written(content).map(inner => s"${tag.code}($inner)")

  /** Every notation, when each item has one. */
  private def all(texts: Vector[Option[String]]): Option[Vector[String]] =
    texts.foldLeft(Option(Vector.empty[String]))((found, text) =>
      found.zip(text).map(_ :+ _)
    )

  /** A floating point value, with a point or an exponent so that it is not read
    * as an integer; the reader picks the width (`DiagnosticNotation`).
    */
  private def floating(value: Double): String =
    if value.isNaN then "NaN"
    else if value.isPosInfinity then "Infinity"
    else if value.isNegInfinity then "-Infinity"
    else
      val text = value.toString.replace('E', 'e')
      if text.exists(character => character == '.' || character == 'e') then
        text
      else s"$text.0"

  /** A text string in double quotes: a quote, a backslash and every control
    * character escaped, so that the text stays on one line.
    */
  private def quoted(value: String): String =
    val codePoints = Vector.unfold(0)(index =>
      Option
        .when(index < value.length)(value.codePointAt(index))
        .map(codePoint => (codePoint, index + Character.charCount(codePoint)))
    )
    codePoints
      .map {
        case '"'                                          => "\\\""
        case '\\'                                         => "\\\\"
        case '\n'                                         => "\\n"
        case '\r'                                         => "\\r"
        case '\t'                                         => "\\t"
        case control if control < 0x20 || control == 0x7f => f"\\u$control%04x"
        case other => Character.toString(other)
      }
      .mkString("\"", "", "\"")

  /** A byte string in hexadecimal, `h'…'`. */
  private def hexadecimal(bytes: Array[Byte]): String =
    s"h'${hexadecimalDigits(bytes.toVector)}'"

  /** The bytes in hexadecimal digits, two to a byte. */
  private def hexadecimalDigits(bytes: Vector[Byte]): String =
    bytes.map(byte => f"${byte & 0xff}%02x").mkString
