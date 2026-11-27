package gezi.frontend

import io.bullet.borer.Dom
import io.bullet.borer.SimpleValue
import io.bullet.borer.Tag
import java.nio.charset.StandardCharsets
import parsley.Parsley
import parsley.Parsley.atomic
import parsley.Parsley.eof
import parsley.Parsley.lookAhead
import parsley.Parsley.many
import parsley.Parsley.notFollowedBy
import parsley.Parsley.some
import parsley.character.char
import parsley.character.oneOf
import parsley.character.satisfy
import parsley.character.string
import parsley.combinator.exactly
import parsley.combinator.ifS
import parsley.combinator.option
import parsley.errors.combinator.ErrorMethods
import parsley.errors.combinator.amend
import parsley.errors.combinator.fail
import parsley.position.offset
import parsley.syntax.zipped.Zipped2
import parsley.syntax.zipped.Zipped3
import parsley.unicode

/** The reader of the literals of lambdalattice text: CBOR's diagnostic
  * notation, Concise Diagnostic Notation (CDN), draft-ietf-cbor-edn-literals-29
  * (2026-10-31), its ABNF of section 5.1 transcribed rule by rule into Parsley
  * parsers named after the rules, each producing borer's data model
  * (`Dom.Element`), whose bytes borer writes (`Literal.encoding`). The one
  * notation is the surface syntax of every literal, the variable arguments' and
  * the partial functions' keys alike.
  *
  * The rules are read as a parsing expression grammar, as the draft's
  * implementation note of section 5 intends: an alternative is committed once
  * it has read, and a repetition takes what it can. Where the ABNF repeats
  * `item *(MSC item) SOC`, the reader reads the separator first and then
  * decides by the next code point (`elements`), which accepts the same texts.
  *
  * THE SUBSET. Integers (decimal, `0x`, `0o`, `0b`, an optional `-`); floating
  * point values, decimal with `.` or an exponent and hexadecimal with a `p`
  * exponent, `Infinity`, `-Infinity`, `NaN`; text strings `"…"` and byte
  * strings `'…'` with the draft's escapes; the prefixed byte strings `h'…'` and
  * `b64'…'`; arrays and maps, definite and indefinite (`[_ …]`, `{_ …}`); tags
  * `uint(item)`; `false`, `true`, `null`, `undefined` and `simple(n)`; blank
  * space and comments (`#` to the end of the line, `/…/`, `/* … */`). The rest
  * is reported as `UnsupportedDiagnosticNotation` at its start: an encoding
  * indicator other than the `_` of an indefinite array or map, an
  * application-extension prefix other than `h` and `b64` (string concatenation
  * `t1''`, `b1''` among them), a raw string, embedded CBOR `<<…>>`, an
  * indefinite string `(_ …)`, an ellipsis in `h''`, a tag number above 2^63 − 1
  * (borer's `Tag` holds a `Long`), and an item borer does not write (nested
  * deeper than its bound of 1,000). `dt''`, `ip''` and the other prefixes are
  * added when they are needed.
  *
  * THE BYTES. Without an encoding indicator CDN gives the preferred
  * serialization (draft, section 5.1, items 3.iii and 3.iv): an integer within
  * 64 bits is major type 0 or 1 with the shortest argument, a negative one
  * written −1 − n; beyond, tag 2 or 3 over the big-endian bytes of n with no
  * leading zero byte (RFC 8949, section 3.4.3), built here because borer's
  * `BigInt` encoder keeps the leading zero of `BigInteger.toByteArray`. A
  * floating point value is rounded to binary64, then written at the shortest of
  * half, single and double precision that holds it exactly, NaN as the half
  * `0x7e00`; borer's own choice of the width is turned off
  * (`Literal.encoding`). A map keeps its written order.
  *
  * A deviation from the draft's words: the draft says that `//` "raises an
  * error"; it is read as a malformed literal, and so is a C-style comment
  * inside `h''`, which the draft's note on Figure 5 makes an error as well.
  *
  * A malformed literal fails the parse with `Raised.malformedLiteral` where the
  * reading stops, a part outside the subset with `Raised.unsupportedNotation`
  * at its start, an unclosed string with `Raised.unterminatedString` and an
  * unknown escape with `Raised.unknownEscape`; `Lambdalattice` reads them back
  * into syntax errors. No error is thrown from an action (`ParsleyFailure`).
  */
private[frontend] object DiagnosticNotation:

  import Lambdalattice.Raised

  // ---- failures ----

  private val malformed: Parsley[Nothing] = fail(Raised.malformedLiteral)

  private val unsupported: Parsley[Nothing] = fail(Raised.unsupportedNotation)

  /** The parser, or, where it fails without reading, a malformed literal there.
    */
  private def required[A](parser: Parsley[A]): Parsley[A] = parser | malformed

  /** The parser, an alternative that reads nothing when it fails, its error
    * where it started.
    */
  private def backtracking[A](parser: Parsley[A]): Parsley[A] = amend(
    atomic(parser)
  )

  /** The value the parser's result holds, or the failure its left side names,
    * at the start of the parser.
    */
  private def validated[A](parser: Parsley[Either[String, A]]): Parsley[A] =
    parser.collectMsg(result =>
      Seq(result.fold(identity, _ => Raised.malformedLiteral))
    ) { case Right(value) => value }

  // ---- character classes (the ABNF's core rules) ----

  private def within(codePoint: Int, low: Int, high: Int): Boolean =
    codePoint >= low && codePoint <= high

  /** DIGIT = %x30-39 */
  private def isDigit(codePoint: Int): Boolean = within(codePoint, '0', '9')

  /** HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F", case-insensitive as a
    * quoted ABNF string is.
    */
  private def isHexadecimalDigit(codePoint: Int): Boolean =
    isDigit(codePoint) || within(codePoint, 'a', 'f') || within(
      codePoint,
      'A',
      'F'
    )

  /** lcalpha = %x61-7A */
  private def isLowercase(codePoint: Int): Boolean = within(codePoint, 'a', 'z')

  /** ucalpha = %x41-5A */
  private def isUppercase(codePoint: Int): Boolean = within(codePoint, 'A', 'Z')

  /** wordchar = "_" / ALPHA / DIGIT */
  def isWordCharacter(codePoint: Int): Boolean =
    codePoint == '_' || isLowercase(codePoint) || isUppercase(
      codePoint
    ) || isDigit(codePoint)

  /** NONASCII = %x80-D7FF / %xE000-10FFFF */
  private def isNonAscii(codePoint: Int): Boolean =
    within(codePoint, 0x80, 0xd7ff) || within(codePoint, 0xe000, 0x10ffff)

  /** blank = %x09 / %x0A / %x0D / %x20 */
  private def isBlank(codePoint: Int): Boolean =
    codePoint == 0x09 || codePoint == 0x0a || codePoint == 0x0d || codePoint == 0x20

  private val digit: Parsley[Char] = satisfy(character => isDigit(character))

  private val hexadecimalDigit: Parsley[Char] =
    satisfy(character => isHexadecimalDigit(character))

  // ---- blank space and comments ----

  private val blank: Parsley[Unit] =
    satisfy(character => isBlank(character)).void

  /** non-slash = blank / %x21-2e / %x30-7F / NONASCII */
  private val nonSlash: Parsley[Unit] =
    unicode
      .satisfy(codePoint =>
        isBlank(codePoint) || within(codePoint, 0x21, 0x2e) || within(
          codePoint,
          0x30,
          0x7f
        ) || isNonAscii(codePoint)
      )
      .void

  /** non-slash-star = blank / %x21-29 / %x2b-2e / %x30-7F / NONASCII */
  private val nonSlashStar: Parsley[Unit] =
    unicode
      .satisfy(codePoint =>
        isBlank(codePoint) || within(codePoint, 0x21, 0x29) || within(
          codePoint,
          0x2b,
          0x2e
        ) ||
          within(codePoint, 0x30, 0x7f) || isNonAscii(codePoint)
      )
      .void

  /** non-star = blank / %x21-29 / %x2b-7F / NONASCII */
  private val nonStar: Parsley[Unit] =
    unicode
      .satisfy(codePoint =>
        isBlank(codePoint) || within(codePoint, 0x21, 0x29) || within(
          codePoint,
          0x2b,
          0x7f
        ) || isNonAscii(codePoint)
      )
      .void

  /** ends-in-star = *non-star 1*"*" */
  private val endsInStar: Parsley[Unit] =
    many(nonStar) ~> required(some(char('*'))).void

  /** non-lf = %x09 / %x0D / %x20-7F / NONASCII */
  private val nonLineFeed: Parsley[Unit] =
    unicode
      .satisfy(codePoint =>
        codePoint == 0x09 || codePoint == 0x0d || within(
          codePoint,
          0x20,
          0x7f
        ) || isNonAscii(codePoint)
      )
      .void

  /** eol-comment *non-lf, a comment to the end of the line without the line
    * feed that ends it, which must come next; eol-comment = "#" / "//", where
    * "//" raises an error.
    */
  private val lineComment: Parsley[Unit] =
    (char('#') ~> many(nonLineFeed) ~> required(lookAhead(char('\n')))).void |
      amend(atomic(string("//")) ~> malformed)

  /** The block comments, "/" non-slash-star *non-slash "/" and "/\*"
    * ends-in-star *(non-slash-star ends-in-star) "/" (the second's opening
    * written `/\*` here, since a Scala comment nests).
    */
  private val blockComment: Parsley[Unit] =
    char('/') ~> required(
      (char('*') ~> endsInStar ~> many(nonSlashStar ~> endsInStar) ~> required(
        char('/')
      )).void |
        (nonSlashStar ~> many(nonSlash) ~> required(char('/'))).void
    )

  /** comment = "/" non-slash-star *non-slash "/" / "/\*" ends-in-star
    * *(non-slash-star ends-in-star) "/" / eol-comment *non-lf %x0A
    */
  private val comment: Parsley[Unit] =
    (lineComment ~> char('\n')).void | blockComment

  /** A comment of lambdalattice text outside its literals: the rule `comment`,
    * with the line feed that ends a comment to the end of the line left to the
    * white space after it, where `Lambdalattice.lexemes` keeps it as a line
    * break of the layout. The text's comments are the notation's.
    */
  private[frontend] val commentBeforeLineFeed: Parsley[Unit] =
    lineComment | blockComment

  /** S = *blank *(comment *blank), optional space. */
  private val optionalSpace: Parsley[Unit] = many(blank | comment).void

  /** MS = (blank / comment) S, mandatory space: whether optional space read
    * any.
    */
  private val spaceRead: Parsley[Boolean] =
    (offset, optionalSpace, offset).zipped((start, _, end) => end > start)

  /** SOC = S ["," S], an optional comma and space; whether it read any, which
    * is whether it was MSC = ("," S) / (MS ["," S]), a mandatory one.
    */
  private val optionalCommaOrSpace: Parsley[Boolean] =
    (offset, optionalSpace ~> option(char(',') ~> optionalSpace), offset)
      .zipped((start, _, end) => end > start)

  // ---- numbers ----

  /** A number as written, before its bytes: an integer, with whether it is
    * written as `uint` (the number of a tag), a floating point value rounded to
    * binary64, or a floating point value out of binary64's range.
    */
  private enum Numeral:
    case Integer(value: BigInt, unsignedInteger: Boolean)
    case Floating(value: Double)
    case OutOfRange

  private def floating(value: Double): Numeral =
    if value.isInfinite then Numeral.OutOfRange else Numeral.Floating(value)

  private def negated(numeral: Numeral): Numeral = numeral match
    case Numeral.Integer(value, _) => Numeral.Integer(-value, false)
    case Numeral.Floating(value)   => Numeral.Floating(-value)
    case Numeral.OutOfRange        => Numeral.OutOfRange

  /** The decimal digits of an exponent, `[sign] 1*DIGIT`, with its sign. */
  private val exponentDigits: Parsley[String] =
    (option(oneOf('+', '-')), some(digit)).zipped((sign, digits) =>
      sign.fold("")(_.toString) + digits.mkString
    )

  /** hexfloat = "0x" (1*HEXDIG ["." *HEXDIG] / "." 1*HEXDIG) "p" [sign]
    * 1*DIGIT, after its "0x"; with no "." where `withPoint` does not hold
    * (`binderLiteral`).
    */
  private def hexadecimalFloat(withPoint: Boolean): Parsley[Numeral] =
    (
      if withPoint then
        (some(hexadecimalDigit).map(_.mkString) <~> option(
          char('.') ~> many(hexadecimalDigit).map(_.mkString)
        )) |
          (char('.') ~> some(hexadecimalDigit).map(digits =>
            ("", Some(digits.mkString))
          ))
      else
        some(hexadecimalDigit).map(digits =>
          (digits.mkString, Option.empty[String])
        )
      ,
      oneOf('p', 'P') ~> exponentDigits
    ).zipped { case ((whole, fraction), exponent) =>
      floating(
        java.lang.Double.parseDouble(
          s"0x${if whole.isEmpty then "0" else whole}.${fraction.getOrElse("0")}p$exponent"
        )
      )
    }

  /** hexint = "0x" 1*HEXDIG, after its "0x". */
  private val hexadecimalInteger: Parsley[Numeral] =
    required(some(hexadecimalDigit)).map(digits =>
      Numeral.Integer(BigInt(digits.mkString, 16), false)
    )

  /** octint = "0o" 1*ODIGIT, after its "0o". */
  private val octalInteger: Parsley[Numeral] =
    required(some(satisfy(character => within(character, '0', '7'))))
      .map(digits => Numeral.Integer(BigInt(digits.mkString, 8), false))

  /** binint = "0b" 1*BDIGIT, after its "0b". */
  private val binaryInteger: Parsley[Numeral] =
    required(some(oneOf('0', '1'))).map(digits =>
      Numeral.Integer(BigInt(digits.mkString, 2), false)
    )

  /** The exponent of a decimal number, `"e" [sign] 1*DIGIT`. */
  private val decimalExponent: Parsley[String] = backtracking(
    oneOf('e', 'E') ~> exponentDigits
  )

  /** decnumber = (("0" / DIGIT1 *DIGIT) ["." *DIGIT] / "." 1*DIGIT) ["e" [sign]
    * 1*DIGIT], unsigned: an integer unless "." or "e" is present; with no "."
    * where `withPoint` does not hold (`binderLiteral`).
    */
  private def decimalNumber(withPoint: Boolean): Parsley[Numeral] =
    val whole: Parsley[String] =
      char('0').as("0") | (satisfy(character =>
        within(character, '1', '9')
      ) <::> many(digit)).map(_.mkString)
    (
      if withPoint then
        (whole <~> option(char('.') ~> many(digit).map(_.mkString))) |
          backtracking(
            char('.') ~> some(digit).map(digits => ("", Some(digits.mkString)))
          )
      else whole.map((_, Option.empty[String])),
      option(decimalExponent)
    ).zipped {
      case ((written, None), None) => Numeral.Integer(BigInt(written), true)
      case ((written, fraction), exponent) =>
        floating(
          java.lang.Double.parseDouble(
            s"${if written.isEmpty then "0" else written}.${fraction.filter(_.nonEmpty).getOrElse("0")}" +
              exponent.fold("")(power => s"e$power")
          )
        )
    }

  /** number = hexfloat / hexint / octint / binint / decnumber, unsigned: the
    * sign and nonfin are `number`'s. With no "." where `withPoint` does not
    * hold.
    */
  private def unsignedNumber(withPoint: Boolean): Parsley[Numeral] =
    backtracking(char('0') ~> oneOf('x', 'X')) ~> (backtracking(
      hexadecimalFloat(withPoint)
    ) | hexadecimalInteger) |
      backtracking(char('0') ~> oneOf('o', 'O')) ~> octalInteger |
      backtracking(char('0') ~> oneOf('b', 'B')) ~> binaryInteger |
      decimalNumber(withPoint)

  /** The data item of a floating point value in its preferred serialization:
    * the shortest of half, single and double precision that holds it exactly,
    * NaN as a half.
    */
  private[frontend] def floatingElement(value: Double): Dom.Element =
    val single = value.toFloat
    if value.isNaN then Dom.Float16Elem(Float.NaN)
    else if java.lang.Double.doubleToRawLongBits(
        single.toDouble
      ) != java.lang.Double.doubleToRawLongBits(value)
    then Dom.DoubleElem(value)
    else if !halfPrecisionHolds(single) then Dom.FloatElem(single)
    else Dom.Float16Elem(single)

  /** Whether binary16, IEEE 754's half precision, holds the single precision
    * value, not a NaN, exactly: a zero or an infinity; a normal value whose
    * exponent is −14 to 15 and whose 23 fraction bits end in 13 zeros, since
    * binary16 keeps 10; or a value whose exponent is −24 to −15, a subnormal of
    * binary16, that is a multiple of 2^−24, its least subnormal, so that the
    * significand with its leading one ends in −exponent − 1 zeros. Read from
    * the bits rather than by `Float.floatToFloat16` and `Float.float16ToFloat`,
    * which Scala.js's Java library lacks (the project `frontend-js`).
    */
  private def halfPrecisionHolds(value: Float): Boolean =
    val bits = java.lang.Float.floatToRawIntBits(value)
    val biasedExponent = (bits >>> 23) & 0xff
    val fraction = bits & 0x7fffff
    if biasedExponent == 0xff || biasedExponent == 0 then fraction == 0
    else
      val exponent = biasedExponent - 127
      val droppedBits = if exponent >= -14 then 13 else -exponent - 1
      exponent <= 15 && exponent >= -24 && ((fraction | 0x800000) & ((1 << droppedBits) - 1)) == 0

  private def numeralElement(numeral: Numeral): Either[String, Dom.Element] =
    numeral match
      case Numeral.Integer(value, _) => Right(Literal.integerElement(value))
      case Numeral.Floating(value)   => Right(floatingElement(value))
      case Numeral.OutOfRange        => Left(Raised.malformedLiteral)

  /** spec = ["_" [specchar]], an encoding indicator, which this reader does not
    * support after a number or a string: nothing, or the unsupported notation
    * at the `_`.
    */
  private val noEncodingIndicator: Parsley[Unit] =
    amend(char('_') ~> unsupported) | Parsley.unit

  /** The item a tag takes, `"(" S item S ")"`. */
  private lazy val tagContent: Parsley[Dom.Element] =
    char('(') ~> optionalSpace ~> taggingItem <~ optionalSpace <~ required(
      char(')')
    )

  /** The tag of the number over the item: a `uint` up to 2^63 − 1; above, an
    * unsupported tag, and from 2^64 a malformed one.
    */
  private def tagged(
      numeral: Numeral,
      content: Dom.Element
  ): Either[String, Dom.Element] = numeral match
    case Numeral.Integer(value, true) if value.isValidLong =>
      Right(Dom.TaggedElem(Tag.Other(value.toLong), content))
    case Numeral.Integer(value, true) if value.bitLength <= 64 =>
      Left(Raised.unsupportedNotation)
    case _ => Left(Raised.malformedLiteral)

  /** A number, `(number) spec` and `tagged = uint spec "(" S item S ")"`: `+`
    * raises an error, `-` before a number or `Infinity` negates it, and `NaN`
    * and `Infinity` are nonfin. A `uint` followed by `(` is a tag where
    * `takesTag` holds, everywhere inside a literal and where the literal stands
    * at the head of its own position (`Lambdalattice`'s LITERALS). A number
    * holds a "." only where `withPoint` holds, which it does but for a bare
    * binder (`binderLiteral`).
    */
  private def number(
      takesTag: Boolean,
      withPoint: Boolean
  ): Parsley[Dom.Element] =
    val signed: Parsley[Numeral] =
      backtracking(string("Infinity")).as(
        Numeral.Floating(Double.PositiveInfinity)
      ) |
        backtracking(string("NaN")).as(Numeral.Floating(Double.NaN)) |
        (char('-') ~> required(
          backtracking(string("Infinity"))
            .as(Numeral.Floating(Double.NegativeInfinity)) |
            unsignedNumber(withPoint).map(negated)
        )) |
        unsignedNumber(withPoint)
    amend(char('+') ~> malformed) |
      validated(
        if takesTag then
          (signed <~ noEncodingIndicator, option(tagContent)).zipped {
            case (numeral, None)          => numeralElement(numeral)
            case (numeral, Some(content)) => tagged(numeral, content)
          }
        else (signed <~ noEncodingIndicator).map(numeralElement)
      )

  // ---- strings ----

  /** The closing quote, or at the end of the text an unterminated string, or
    * elsewhere a code point no string holds.
    */
  private def closingQuote(quote: Char): Parsley[Unit] =
    char(quote).void | ifS(
      option(eof).map(_.isDefined),
      fail(Raised.unterminatedString),
      malformed
    )

  /** unescaped = %x0A / %x0D / %x20-21 / %x23-26 / %x28-5B / %x5D-7F /
    * NONASCII, a carriage return ignored on input (draft, section 2.3.1).
    */
  private val unescaped: Parsley[String] =
    unicode
      .satisfy(codePoint =>
        codePoint == 0x0a || codePoint == 0x0d || within(
          codePoint,
          0x20,
          0x21
        ) || within(codePoint, 0x23, 0x26) ||
          within(codePoint, 0x28, 0x5b) || within(
            codePoint,
            0x5d,
            0x7f
          ) || isNonAscii(codePoint)
      )
      .map(codePoint =>
        if codePoint == 0x0d then "" else Character.toString(codePoint)
      )

  /** escapable1 = "b" / "f" / "n" / "r" / "t" / "\" */
  private val commonEscapable: Parsley[String] =
    char('b').as("\b") | char('f').as("\f") | char('n').as("\n") | char('r').as(
      "\r"
    ) | char('t').as("\t") |
      char('\\').as("\\")

  /** Four hexadecimal digits, the value of a `\u` escape. */
  private val fourHexadecimalDigits: Parsley[Int] =
    exactly(4, required(hexadecimalDigit)).map(digits =>
      Integer.parseInt(digits.mkString, 16)
    )

  private def isHighSurrogate(value: Int): Boolean =
    within(value, 0xd800, 0xdbff)

  private def isLowSurrogate(value: Int): Boolean =
    within(value, 0xdc00, 0xdfff)

  /** hexchar = "{" (1*"0" [hexscalar] / hexscalar) "}" / non-surrogate /
    * two-surrogate hexchar-s = the same with no scalar value from U+0020 to
    * U+007E: the code point of a `\u` escape, after its `u`. A scalar value in
    * braces is up to U+10FFFF and no surrogate, with leading zeros, as the
    * rules hexscalar and hexscalar-s spell it; four digits are a scalar value
    * that is no surrogate, or a high surrogate followed by `\u` and a low one.
    */
  private def hexadecimalCharacter(excluded: Int => Boolean): Parsley[String] =
    val braced: Parsley[Either[String, Int]] =
      (char('{') ~> required(some(hexadecimalDigit)) <~ required(char('}')))
        .map(digits =>
          val significant = digits.mkString.dropWhile(_ == '0')
          if significant.length > 6 then Left(Raised.malformedLiteral)
          else
            val value = if significant.isEmpty then 0
            else Integer.parseInt(significant, 16)
            if value > 0x10ffff || within(value, 0xd800, 0xdfff) then
              Left(Raised.malformedLiteral)
            else Right(value)
        )
    // A `\u` escape of a low surrogate right after is taken with the four
    // digits whatever they are: after a high surrogate it completes the pair,
    // and after anything else it is a lone low surrogate, malformed either
    // way, so the language read is the rule's. No Parsley reference holds the
    // first digits: a reference made inside this object is shared by every
    // top-level parser that reads a literal (the lexer, the grammar, the
    // token found at an error), and one compiled into another parser's
    // registers ran out of a smaller parser's register array
    // (ArrayIndexOutOfBoundsException, LiteralSyntaxLawTest, 2026-11-16).
    val lowSurrogate: Parsley[Int] =
      backtracking(
        (string("\\u") ~> exactly(4, hexadecimalDigit))
          .map(digits => Integer.parseInt(digits.mkString, 16))
          .filter(isLowSurrogate)
      )
    val unbraced: Parsley[Either[String, Int]] =
      (fourHexadecimalDigits, option(lowSurrogate))
        .zipped((_, _))
        .map {
          case (high, Some(low)) if isHighSurrogate(high) =>
            Right(Character.toCodePoint(high.toChar, low.toChar))
          case (single, None)
              if !isHighSurrogate(single) && !isLowSurrogate(single) =>
            Right(single)
          case _ => Left(Raised.malformedLiteral)
        }
    validated(
      (braced | unbraced).map(
        _.flatMap(value =>
          if excluded(value) then Left(Raised.malformedLiteral)
          else Right(Character.toString(value))
        )
      )
    )

  /** An escape after its `\`: one of the escapable ones, an unterminated string
    * at the end of the text, or an unknown escape at the code point.
    */
  private def escape(escapable: Parsley[String]): Parsley[String] =
    (eof ~> fail(Raised.unterminatedString)) | escapable |
      amend(
        unicode.item.collectMsg(_ => Seq(Raised.unknownEscape))(
          PartialFunction.empty
        )
      )

  /** escapable-d = escapable1 / DQUOTE / "/" / ("u" hexchar) */
  private val doubleEscapable: Parsley[String] =
    commonEscapable | char('"').as("\"") | char('/').as("/") | (char(
      'u'
    ) ~> hexadecimalCharacter(_ => false))

  /** escapable-s = escapable1 / SQUOTE / ("u" hexchar-s) */
  private val singleEscapable: Parsley[String] =
    commonEscapable | char('\'').as("'") | (char('u') ~> hexadecimalCharacter(
      value => within(value, 0x20, 0x7e)
    ))

  /** double-quoted = unescaped / SQUOTE / "\" escapable-d */
  private val doubleQuoted: Parsley[String] =
    unescaped | char('\'').as("'") | (char('\\') ~> escape(doubleEscapable))

  /** single-quoted = unescaped / DQUOTE / "\" escapable-s */
  private val singleQuoted: Parsley[String] =
    unescaped | char('"').as("\"") | (char('\\') ~> escape(singleEscapable))

  /** dqstr = DQUOTE *double-quoted DQUOTE, the text it holds. */
  private val doubleQuotedString: Parsley[String] =
    char('"') ~> many(doubleQuoted).map(_.mkString) <~ closingQuote('"')

  /** sqstr = SQUOTE *single-quoted SQUOTE, the text it holds. */
  private val singleQuotedString: Parsley[String] =
    char('\'') ~> many(singleQuoted).map(_.mkString) <~ closingQuote('\'')

  // ---- the content of prefixed strings (section 5.2) ----

  /** The content of `h''` (app-string-h, section 5.2.1), read from the text the
    * single-quoted string holds: its hexadecimal digits, or the unsupported
    * notation for an ellipsis.
    *
    * {{{
    * app-string-h = S *(HEXDIG S HEXDIG S / ellipsis S) [eol-comment *non-lf]
    * S            = *lblank *(comment *lblank)        lblank = %x0A / %x20
    * }}}
    *
    * with the comments of section 5.1 over lblank and with non-lf = %x20-7f /
    * NONASCII; "//" and the C-style comment raise an error.
    */
  private object HexadecimalContent:

    private val lineBlank: Parsley[Unit] = oneOf('\n', ' ').void

    private val nonSlash: Parsley[Unit] =
      unicode
        .satisfy(codePoint =>
          codePoint == 0x0a || codePoint == 0x20 || within(
            codePoint,
            0x21,
            0x2e
          ) || within(codePoint, 0x30, 0x7f) ||
            isNonAscii(codePoint)
        )
        .void

    private val nonSlashStar: Parsley[Unit] =
      unicode
        .satisfy(codePoint =>
          codePoint == 0x0a || codePoint == 0x20 || within(
            codePoint,
            0x21,
            0x29
          ) || within(codePoint, 0x2b, 0x2e) ||
            within(codePoint, 0x30, 0x7f) || isNonAscii(codePoint)
        )
        .void

    private val nonLineFeed: Parsley[Unit] =
      unicode
        .satisfy(codePoint =>
          within(codePoint, 0x20, 0x7f) || isNonAscii(codePoint)
        )
        .void

    private val comment: Parsley[Unit] =
      (char('#') ~> many(nonLineFeed) ~> char('\n')).void |
        (char('/') ~> nonSlashStar ~> many(nonSlash) ~> char('/')).void

    private val space: Parsley[Unit] = many(lineBlank | atomic(comment)).void

    private val ellipsis: Parsley[Unit] =
      (char('.') ~> char('.') ~> some(char('.'))).void

    val content: Parsley[Either[String, String]] =
      (
        space ~> many(
          (hexadecimalDigit <~ space, hexadecimalDigit <~ space).zipped(
            (high, low) => Right(s"$high$low")
          ) |
            (ellipsis <~ space).as(Left(Raised.unsupportedNotation))
        ) <~ option(char('#') ~> many(nonLineFeed)) <~ eof
      ).map(pieces =>
        pieces
          .collectFirst { case Left(problem) => problem }
          .toLeft(pieces.collect { case Right(pair) => pair }.mkString)
      )

  /** The content of `b64''` (app-string-b64, section 5.2.2), read from the text
    * the single-quoted string holds: its base64 digits, classic or URL-safe,
    * mapped to the classic alphabet, padding left out.
    *
    * {{{
    * app-string-b64 = B *(4(b64dig B))
    *                  [b64dig B b64dig B ["=" B "=" / b64dig B ["="]] B]
    *                  ["#" *non-lf]
    * b64dig         = ALPHA / DIGIT / "-" / "_" / "+" / "/"
    * B              = *lblank *(comment *lblank)
    * comment        = "#" *non-lf %x0A
    * }}}
    *
    * read as the digits and the padding with B between them, then checked: the
    * digits are 0, 2 or 3 more than a multiple of 4, padded by none, `==` or
    * `=` respectively, or by nothing.
    */
  private object Base64Content:

    private val nonLineFeed: Parsley[Unit] =
      unicode
        .satisfy(codePoint =>
          within(codePoint, 0x20, 0x7f) || isNonAscii(codePoint)
        )
        .void

    private val space: Parsley[Unit] =
      many(
        oneOf('\n', ' ').void | atomic(
          char('#') ~> many(nonLineFeed) ~> char('\n')
        ).void
      ).void

    private val base64Digit: Parsley[Char] =
      satisfy(character =>
        isLowercase(character) || isUppercase(character) || isDigit(
          character
        ) || "-_+/".contains(character)
      )

    val content: Parsley[Option[String]] =
      (
        space ~> many(base64Digit <~ space).map(_.mkString),
        many(char('=') <~ space).map(_.size) <~ option(
          char('#') ~> many(nonLineFeed)
        ) <~ eof
      ).zipped((digits, padding) =>
        val allowed = digits.length % 4 match
          case 0 => Set(0)
          case 2 => Set(0, 2)
          case 3 => Set(0, 1)
          case _ => Set.empty[Int]
        Option.when(allowed.contains(padding))(digits.map {
          case '-'   => '+'
          case '_'   => '/'
          case other => other
        })
      )

  /** The bytes of an even number of hexadecimal digits, two to a byte, the high
    * digit first, what `java.util.HexFormat.parseHex` gives, a class Scala.js's
    * Java library lacks (the project `frontend-js`). The bytes are made as the
    * `Array[Byte]` that borer's `Dom.ByteArrayElem` holds, an exception to
    * NoArray for exchange with a library.
    */
  @SuppressWarnings(
    Array("gezi.warts.NoArray")
  ) // "NoArray wart可以有例外。如果用于和外部库交换，需要Array完全可以理解。我们自己当然还是优先用IArray" (the user, 2026-11-16)
  private def hexadecimalBytes(digits: String): Array[Byte] =
    Vector
      .tabulate(digits.length / 2)(index =>
        Integer.parseInt(digits.substring(2 * index, 2 * index + 2), 16).toByte
      )
      .toArray

  /** The bytes of the content of `h''` or `b64''`, or what is wrong with it. */
  private def prefixedBytes(
      prefix: String,
      content: String
  ): Either[String, Dom.Element] = prefix match
    case "h" =>
      HexadecimalContent.content.parse[ParsleyFailure](content).toOption match
        case Some(Right(digits)) =>
          Right(Dom.ByteArrayElem(hexadecimalBytes(digits)))
        case Some(Left(problem)) => Left(problem)
        case None                => Left(Raised.malformedLiteral)
    case "b64" =>
      Base64Content.content
        .parse[ParsleyFailure](content)
        .toOption
        .flatten match
        case Some(digits) =>
          Right(Dom.ByteArrayElem(java.util.Base64.getDecoder.decode(digits)))
        case None => Left(Raised.malformedLiteral)
    case _ => Left(Raised.unsupportedNotation)

  // ---- words: simple values and prefixes ----

  /** simple-number, the number of `simple(…)`, spelled with no leading zero: 0
    * to 23 and 32 to 255. The values 20 to 23 are false, true, null and
    * undefined, which borer writes as the elements of those.
    */
  private val simpleNumber: Parsley[Dom.Element] =
    validated(
      some(digit)
        .map(_.mkString)
        .map(written =>
          val value = BigInt(written)
          if written != value.toString || !(value <= 23 || (value >= 32 && value <= 255))
          then Left(Raised.malformedLiteral)
          else
            Right(value.toInt match
              case 20    => Dom.BooleanElem(false)
              case 21    => Dom.BooleanElem(true)
              case 22    => Dom.NullElem
              case 23    => Dom.UndefinedElem
              case other => Dom.SimpleValueElem(SimpleValue(other)))
        )
    )

  /** simple = "simple(" S simple-number S ")", after "simple(". */
  private val simple: Parsley[Dom.Element] =
    backtracking(string("simple(")) ~> optionalSpace ~> required(
      simpleNumber
    ) <~ optionalSpace <~ required(char(')'))

  /** What follows a prefix: a single-quoted string's text, or the unsupported
    * notation at a raw string or an embedded CBOR sequence.
    */
  private val prefixedString: Parsley[String] =
    singleQuotedString | amend(char('`') ~> unsupported) | amend(
      atomic(string("<<")) ~> unsupported
    )

  /** prefix = lcalpha *lcldh, followed by a prefixed string, and the keywords
    * false, true, null and undefined: a prefixed string `h''` or `b64''`,
    * another prefix being unsupported, or a keyword.
    */
  private val lowercaseWord: Parsley[Dom.Element] =
    validated(
      (
        (satisfy(character => isLowercase(character)) <::>
          many(
            satisfy(character =>
              isLowercase(character) || isDigit(character) || character == '-'
            )
          )).map(_.mkString),
        option(prefixedString <~ noEncodingIndicator)
      ).zipped {
        case (prefix, Some(content)) => prefixedBytes(prefix, content)
        case ("false", None)         => Right(Dom.BooleanElem(false))
        case ("true", None)          => Right(Dom.BooleanElem(true))
        case ("null", None)          => Right(Dom.NullElem)
        case ("undefined", None)     => Right(Dom.UndefinedElem)
        case _                       => Left(Raised.malformedLiteral)
      }
    )

  /** prefix = ucalpha *ucldh before a string: unsupported, every uppercase
    * prefix of the draft being one this reader does not take; any other
    * uppercase word is malformed. Either is reported at the word's start.
    */
  private val uppercaseWord: Parsley[Nothing] =
    amend(
      satisfy(character => isUppercase(character)) ~>
        many(
          satisfy(character =>
            isUppercase(character) || isDigit(character) || character == '-'
          )
        ) ~>
        ifS(
          option(lookAhead(oneOf('\'', '`').void | atomic(string("<<")).void))
            .map(_.isDefined),
          unsupported,
          malformed
        )
    )

  // ---- arrays and maps ----

  /** The items of an array or the pairs of a map after its opening bracket and
    * its encoding indicator: `S item *(MSC item) SOC close` or `S close` when
    * `first` holds, else what follows the `_` of an indefinite one,
    * `MS item *(MSC item) SOC close` or `S close`.
    */
  private def elements[A](
      element: => Parsley[A],
      close: Char,
      first: Boolean
  ): Parsley[List[A]] =
    val closing: Parsley[List[A]] = char(close).as(Nil)
    lazy val following: Parsley[List[A]] =
      ifS(
        optionalCommaOrSpace,
        closing | (element <::> following),
        closing | malformed
      )
    if first then optionalSpace ~> (closing | (element <::> following))
    else ifS(spaceRead, closing | (element <::> following), closing | malformed)

  /** An encoding indicator after `[` or `{` other than the `_` alone:
    * unsupported, at the `_`.
    */
  private val bracketEncodingIndicator: Parsley[Nothing] =
    amend(
      atomic(
        char('_') ~> satisfy(character => isWordCharacter(character))
      ) ~> unsupported
    )

  /** array = "[" (specms S item *(MSC item) SOC / spec S) "]" */
  private lazy val array: Parsley[Dom.Element] =
    char('[') ~> (
      bracketEncodingIndicator |
        (char('_') ~> elements(taggingItem, ']', first = false)).map(items =>
          Dom.ArrayElem.Unsized(items.toVector)
        ) |
        elements(taggingItem, ']', first = true).map(items =>
          Dom.ArrayElem.Sized(items.toVector)
        )
    )

  /** keyp = item S ":" S item */
  private lazy val keyValue: Parsley[(Dom.Element, Dom.Element)] =
    (
      taggingItem <~ optionalSpace <~ required(char(':')) <~ optionalSpace,
      taggingItem
    ).zipped((_, _))

  /** map = "{" (specms S keyp *(MSC keyp) SOC / spec S) "}", the pairs in their
    * written order.
    *
    * TODO (https://github.com/Atry/private-overlay/issues/1514; the linter
    * waits for the source locations of debug information): a linter warns where
    * a map literal's keys are not written in the deterministic order of RFC
    * 8949, section 4.2.1 (by their encoded bytes), since a literal is encoded
    * in its written order and a library's `to_cbor` in the deterministic one,
    * and the two then do not match. No linter is built yet.
    */
  private lazy val map: Parsley[Dom.Element] =
    char('{') ~> (
      bracketEncodingIndicator |
        (char('_') ~> elements(keyValue, '}', first = false)).map(pairs =>
          Dom.MapElem.Unsized[Dom.Element](pairs*)
        ) |
        elements(keyValue, '}', first = true).map(pairs =>
          Dom.MapElem.Sized[Dom.Element](pairs*)
        )
    )

  // ---- items ----

  /** item = map / array / tagged / (number / string / prefixed) spec / simple /
    * streamstring, with the parts outside the subset reported where they start:
    * a stream string `(_`, embedded CBOR `<<`, a raw string.
    */
  private def item(
      numberTakesTag: Boolean,
      numberWithPoint: Boolean
  ): Parsley[Dom.Element] =
    map | array |
      (doubleQuotedString.map(Dom.StringElem(_)) <~ noEncodingIndicator) |
      (singleQuotedString.map(text =>
        Dom.ByteArrayElem(text.getBytes(StandardCharsets.UTF_8))
      ) <~ noEncodingIndicator) |
      amend(atomic(string("(_")) ~> unsupported) |
      amend(atomic(string("<<")) ~> unsupported) |
      amend(char('`') ~> unsupported) |
      number(numberTakesTag, numberWithPoint) |
      simple |
      lowercaseWord |
      uppercaseWord |
      malformed

  /** An item inside a literal, where a `uint` followed by `(` is a tag. */
  private lazy val taggingItem: Parsley[Dom.Element] =
    item(numberTakesTag = true, numberWithPoint = true)

  // ---- a literal of lambdalattice text ----

  /** Where a literal of lambdalattice text starts, read ahead: `"`, `'`, `[`,
    * `{`, a digit, `-` touching a digit, `h'` or `b64'`. Nothing else starts
    * one, so `true` and `Infinity` are no literals there, and a name `h` or
    * `b64` not touching `'` stays a name.
    */
  val literalStart: Parsley[Unit] =
    amend(
      lookAhead(
        oneOf('"', '\'', '[', '{').void | digit.void | atomic(
          char('-') ~> digit
        ).void | atomic(string("h'")).void |
          atomic(string("b64'")).void
      )
    )

  /** A literal of lambdalattice text and its bytes: an item that starts as
    * `literalStart` says, not followed by a code point a name goes on with
    * (`NameSpelling.isContinuation`: a letter, a digit, `_` or `$`), which
    * would otherwise be read as a name or another number touching it (`030`
    * would be 0 and 30). A number takes a following `(` as a tag where
    * `numberTakesTag` holds, and holds a "." where `numberWithPoint` does.
    */
  private def literal(
      numberTakesTag: Boolean,
      numberWithPoint: Boolean
  ): Parsley[(Dom.Element, Literal)] =
    validated(
      (literalStart ~> item(numberTakesTag, numberWithPoint) <~ (notFollowedBy(
        unicode.satisfy(NameSpelling.isContinuation)
      ) | malformed))
        .map(element =>
          Literal
            .encoding(element)
            .left
            .map(_ => Raised.unsupportedNotation)
            .map(read => (element, read))
        )
    )

  /** A literal where a number never takes a following `(`: a bare argument of
    * an application, so that `f 30(x)` is `f 30 (x)`.
    */
  lazy val argumentLiteral: Parsley[(Dom.Element, Literal)] =
    literal(numberTakesTag = false, numberWithPoint = true)

  /** A literal where a number touching `(` is a tag: a literal alone in
    * parentheses, as an argument or as a binder, so that `f (30([1, 2]))` is
    * the tag 30 and `λ(3.0). M` the partial function of 3.0. The lexer reads a
    * literal where a head stands this way as well, so that the grammar then
    * reports the literal, not the text after a number.
    */
  lazy val parenthesizedLiteral: Parsley[(Dom.Element, Literal)] =
    literal(numberTakesTag = true, numberWithPoint = true)

  /** A bare binder `λL. M`: a number touching `(` is a tag, `λ30([1, 2]). M`,
    * and the literal holds no "." outside its quotes and brackets, so that a
    * number stops before the "." that ends the binders: `λ3. M` and `λ12. M`
    * are the partial functions of the integers 3 and 12, while `λ1e3. M` is
    * that of the floating point value 1000.0, and 3.0 is the binder
    * `λ(3.0). M`. A deliberate departure from the notation, whose `3.` is 3.0:
    * in a pattern, a `.` stands only inside quotes and brackets.
    */
  lazy val binderLiteral: Parsley[(Dom.Element, Literal)] =
    literal(numberTakesTag = true, numberWithPoint = false)
