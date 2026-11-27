package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import io.bullet.borer.Cbor
import io.bullet.borer.Dom
import io.bullet.borer.SimpleValue
import io.bullet.borer.Tag
import java.nio.charset.StandardCharsets
import gezi.generatedinputs.GeneratedProperties

/** The laws of the literals of lambdalattice text, CBOR's diagnostic notation
  * (`Lambdalattice`'s LITERALS, `DiagnosticNotation`).
  *
  * The inputs are data items of the reader's subset drawn in their preferred
  * serialization, each with a text of the diagnostic notation drawn among its
  * spellings: integers in four radixes and four sizes, floating point values of
  * the three widths in decimal and hexadecimal, text and byte strings with
  * escapes, `h''` and `b64''` with blank space and comments, simple values,
  * arrays and maps definite and indefinite with every kind of separator, tags.
  *
  * (1) A literal read as an argument spreads into the bits of the bytes borer
  * writes for the item, each floating point value at the width drawn
  * (`compressFloatingPointValues = false`). Its purpose is to catch a rule of
  * the notation transcribed wrong (an escape, a radix, a separator, a comment)
  * and an item encoded other than in its preferred serialization (an integer's
  * argument not the shortest, a big number with a leading zero byte, a floating
  * point value wider than it needs). (2) The variable arguments of a literal
  * are its bits, high bit first; a literal between two arguments spreads in
  * place; the body of `λL. M` sees the outer binders at the abstraction's own
  * depth. Its purpose is to catch a bit order, an argument lost or reordered
  * around the spread, and a body read at the wrong depth. (3) A number touching
  * `(` is a tag in parentheses and as a binder, and a bare argument followed by
  * a term in parentheses elsewhere. Its purpose is to catch the positional
  * reading of `f 30(x)` applied in the wrong place. (4) A part of the notation
  * outside the subset is `UnsupportedDiagnosticNotation` at its start, and a
  * literal where a head stands is `Expected(Atom, …)` at the literal. Its
  * purpose is to catch an unsupported part read as something else, and a
  * literal read as a term of its own, though a literal is never a head.
  */
class LiteralSyntaxLawTest extends GeneratedProperties:

  /** A data item in its preferred serialization and a text of it. */
  private final case class Written(element: Dom.Element, text: String)

  private def parsed(text: String): DeBruijnTerm = Lambdalattice.term(text)

  private def problem(text: String): Option[LambdalatticeProblem] =
    try
      parsed(text)
      None
    catch case malformed: LambdalatticeMalformed => Some(malformed.problem)

  private def codePoints(text: String): Int =
    text.codePointCount(0, text.length)

  /** The bytes borer writes for the item, each floating point value at the
    * width of its element.
    */
  private def encoded(element: Dom.Element): Literal =
    Literal(
      IArray.unsafeFromArray(
        Cbor
          .encode(element)
          .withConfig(Cbor.EncodingConfig(compressFloatingPointValues = false))
          .toByteArray
      )
    )

  /** `λf. f x1 … xn` of the arguments. */
  private def spread(arguments: Vector[DeBruijnTerm]): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      arguments.foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)(
        DeBruijnTerm.Apply(_, _)
      )
    )

  private def hexadecimal(bytes: Vector[Int]): String =
    bytes.map(byte => f"$byte%02x").mkString

  private val byteValue: Gen[Int] = Gen.int(Range.constant(0, 255))

  /** Optional blank space or a comment, the rule S. */
  private val optionalSpace: Gen[String] =
    Gen.element1(
      "",
      " ",
      "\n  ",
      " /a comment/ ",
      " /* a * / comment */ ",
      "# a remark\n"
    )

  /** Mandatory blank space or a comment, the rule MS. */
  private val mandatorySpace: Gen[String] = Gen.element1(
    " ",
    "\n",
    " /a comment/ ",
    "/* a comment */",
    " # a remark\n "
  )

  /** A separator between items, the rule MSC. */
  private val separator: Gen[String] =
    Gen.choice1(mandatorySpace, Gen.element1(",", ", ", " ,\n", ",/c/"))

  /** The ASCII letters of a spelling in upper or lower case. */
  private def anyCase(text: String): Gen[String] =
    Gen.boolean
      .list(Range.singleton(text.length))
      .map(uppers =>
        text
          .zip(uppers)
          .map((character, upper) =>
            if upper then character.toUpper else character.toLower
          )
          .mkString
      )

  // ---- integers ----

  /** A spelling of the integer in one of the four radixes; the letters of a
    * prefix and of hexadecimal digits are case-insensitive, as a quoted ABNF
    * string is.
    */
  private def integerText(value: BigInt): Gen[String] =
    for
      radix <- Gen.element1(10, 16, 8, 2)
      digits <- anyCase(value.abs.toString(radix))
      prefix <- anyCase(radix match
        case 16 => "0x"
        case 8  => "0o"
        case 2  => "0b"
        case _  => "")
    yield (if value < 0 then "-" else "") + prefix + digits

  private val twoToThe64: BigInt = BigInt(1) << 64

  /** An integer of each size: small, within 64 bits signed, within 64 bits of
    * argument beyond a `Long` (`OverLongElem`), and a big number over its
    * minimal bytes.
    */
  private val integer: Gen[Written] =
    for
      size <- Gen.int(Range.constant(0, 3))
      (element, value) <- size match
        case 0 =>
          Gen
            .long(Range.linearFrom(0L, -1000L, 1000L))
            .map(value => (Dom.LongElem(value), BigInt(value)))
        case 1 =>
          Gen
            .long(Range.constant(Long.MinValue, Long.MaxValue))
            .map(value => (Dom.LongElem(value), BigInt(value)))
        case 2 =>
          for
            argument <- Gen.long(Range.constant(Long.MinValue, -1L))
            negative <- Gen.boolean
          yield
            val unsigned = BigInt(argument) + twoToThe64
            (
              Dom.OverLongElem(negative, argument),
              if negative then -unsigned - 1 else unsigned
            )
        case _ =>
          for
            first <- Gen.int(Range.constant(1, 255))
            rest <- byteValue.list(Range.linear(8, 20))
            negative <- Gen.boolean
          yield
            val written = hexadecimal(first +: rest.toVector)
            val magnitude = BigInt(written, 16)
            (
              Dom.TaggedElem(
                if negative then Tag.NegativeBigNum else Tag.PositiveBigNum,
                Dom.ByteArrayElem(java.util.HexFormat.of().parseHex(written))
              ),
              if negative then -magnitude - 1 else magnitude
            )
      text <- integerText(value)
    yield Written(element, text)

  // ---- floating point values ----

  private def sameBits(left: Float, right: Float): Boolean =
    java.lang.Float.floatToRawIntBits(left) == java.lang.Float
      .floatToRawIntBits(right)

  /** A spelling of the value, decimal or hexadecimal, each parsing back to the
    * value as binary64; `NaN`, `Infinity` and `-Infinity` as they are.
    */
  private def floatingText(value: Double): Gen[String] =
    if value.isNaN || value.isInfinite then Gen.constant(value.toString)
    else
      Gen
        .element1(
          java.lang.Double.toString(value),
          java.lang.Double.toHexString(value)
        )
        .flatMap(anyCase)

  /** A half precision value, NaN as its one preferred pattern. */
  private val half: Gen[Dom.Element] =
    Gen
      .int(Range.constant(0, 0xffff))
      .map(bits => java.lang.Float.float16ToFloat(bits.toShort))
      .map(value =>
        if value.isNaN then Dom.Float16Elem(Float.NaN)
        else Dom.Float16Elem(value)
      )

  /** A single precision value that no half holds. */
  private val single: Gen[Dom.Element] =
    Gen
      .int(Range.constant(Int.MinValue, Int.MaxValue))
      .map(java.lang.Float.intBitsToFloat)
      .filter(value =>
        !value.isNaN && !sameBits(
          java.lang.Float.float16ToFloat(java.lang.Float.floatToFloat16(value)),
          value
        )
      )
      .map(Dom.FloatElem(_))

  /** A double precision value that no single holds. */
  private val double: Gen[Dom.Element] =
    Gen
      .long(Range.constant(Long.MinValue, Long.MaxValue))
      .map(java.lang.Double.longBitsToDouble)
      .filter(value =>
        !value.isNaN &&
          java.lang.Double.doubleToRawLongBits(
            value.toFloat.toDouble
          ) != java.lang.Double.doubleToRawLongBits(value)
      )
      .map(Dom.DoubleElem(_))

  private val floating: Gen[Written] =
    for
      element <- Gen.choice1(half, single, double)
      value = element match
        case Dom.Float16Elem(value) => value.toDouble
        case Dom.FloatElem(value)   => value.toDouble
        case Dom.DoubleElem(value)  => value
        case other                  =>
          throw IllegalStateException(s"no floating point element: $other")
      text <- floatingText(value)
    yield Written(element, text)

  // ---- strings ----

  private val codePoint: Gen[Int] =
    Gen.frequency1(
      6 -> Gen.int(Range.constant(0x20, 0x7f)),
      1 -> Gen.int(Range.constant(0, 0x1f)),
      1 -> Gen.int(Range.constant(0x80, 0xd7ff)),
      1 -> Gen.int(Range.constant(0xe000, 0x10ffff))
    )

  /** The `\u` escapes of a code point: braced, with and without leading zeros,
    * and four digits, a surrogate pair beyond the BMP.
    */
  private def unicodeEscapes(value: Int): List[String] =
    val braced = List(f"\\u{$value%x}", f"\\u{00$value%X}")
    if value > 0xffff then
      braced :+ f"\\u${Character.highSurrogate(value).toInt}%04x\\u${Character.lowSurrogate(value).toInt}%04X"
    else braced :+ f"\\u$value%04x"

  private val shortEscapes: Map[Int, String] =
    Map(
      '\b'.toInt -> "\\b",
      '\f'.toInt -> "\\f",
      '\n'.toInt -> "\\n",
      '\r'.toInt -> "\\r",
      '\t'.toInt -> "\\t",
      '\\'.toInt -> "\\\\"
    )

  /** Whether the code point stands unescaped in a string of the quote: a line
    * feed, printable ASCII and DEL, and beyond ASCII, but not the quote and the
    * backslash. A carriage return is escaped, since a raw one is dropped.
    */
  private def rawInString(value: Int, quote: Char): Boolean =
    value != quote && value != '\\' && (value == 0x0a || (value >= 0x20 && value <= 0x7f) || value >= 0x80)

  /** The spellings of a code point inside a string of the quote; a `\u` escape
    * in a single-quoted string is never of printable ASCII.
    */
  private def spellings(value: Int, quote: Char): List[String] =
    (if rawInString(value, quote) then List(Character.toString(value))
     else Nil) ++
      shortEscapes.get(value).toList ++
      (if value == quote then List(s"\\$quote") else Nil) ++
      (if quote == '"' && value == '/' then List("\\/") else Nil) ++
      (if quote == '"' || value < 0x20 || value > 0x7e then
         unicodeEscapes(value)
       else Nil)

  private def quoted(text: Vector[Int], quote: Char): Gen[String] =
    text
      .foldLeft(Gen.constant(Vector.empty[String]))((before, value) =>
        spellings(value, quote) match
          case first :: rest =>
            for
              written <- before
              spelled <- Gen.element1(first, rest*)
            yield written :+ spelled
          case Nil =>
            throw IllegalStateException(s"no spelling of the code point $value")
      )
      .map(_.mkString(quote.toString, "", quote.toString))

  private def utf8(text: Vector[Int]): Array[Byte] =
    text.map(Character.toString(_)).mkString.getBytes(StandardCharsets.UTF_8)

  private val textString: Gen[Written] =
    for
      text <- codePoint.list(Range.linear(0, 8)).map(_.toVector)
      written <- quoted(text, '"')
    yield Written(
      Dom.StringElem(text.map(Character.toString(_)).mkString),
      written
    )

  /** A byte string: single-quoted text, `h''` with blank space and comments
    * between the digits, or `b64''`, classic or URL-safe, padded or not.
    */
  private val byteString: Gen[Written] =
    Gen.choice1(
      for
        text <- codePoint.list(Range.linear(0, 8)).map(_.toVector)
        written <- quoted(text, '\'')
      yield Written(Dom.ByteArrayElem(utf8(text)), written),
      for
        bytes <- byteValue.list(Range.linear(0, 8)).map(_.toVector)
        spaces <- Gen
          .element1("", " ", "\n", " /c/ ", "# remark\n")
          .list(Range.singleton(bytes.size * 2 + 1))
        digits <- anyCase(hexadecimal(bytes))
      yield
        val spaced = spaces.headOption.getOrElse("") + digits
          .zip(spaces.drop(1))
          .map((digit, space) => s"$digit$space")
          .mkString
        Written(
          Dom.ByteArrayElem(
            java.util.HexFormat.of().parseHex(hexadecimal(bytes))
          ),
          s"h'$spaced'"
        )
      ,
      for
        bytes <- byteValue.list(Range.linear(0, 8)).map(_.toVector)
        urlSafe <- Gen.boolean
        padded <- Gen.boolean
      yield
        val decoded = java.util.HexFormat.of().parseHex(hexadecimal(bytes))
        val encoder = if urlSafe then java.util.Base64.getUrlEncoder
        else java.util.Base64.getEncoder
        Written(
          Dom.ByteArrayElem(decoded),
          s"b64'${(if padded then encoder else encoder.withoutPadding).encodeToString(decoded)}'"
        )
    )

  // ---- simple values ----

  /** A keyword or `simple(n)`; the simple values 20 to 23 are false, true, null
    * and undefined (RFC 8949, section 3.3).
    */
  private val simple: Gen[Written] =
    Gen.choice1(
      Gen.element1(
        Written(Dom.BooleanElem(false), "false"),
        Written(Dom.BooleanElem(true), "true"),
        Written(Dom.NullElem, "null"),
        Written(Dom.UndefinedElem, "undefined")
      ),
      Gen
        .choice1(
          Gen.int(Range.constant(0, 23)),
          Gen.int(Range.constant(32, 255))
        )
        .map(value =>
          val element = value match
            case 20    => Dom.BooleanElem(false)
            case 21    => Dom.BooleanElem(true)
            case 22    => Dom.NullElem
            case 23    => Dom.UndefinedElem
            case other => Dom.SimpleValueElem(SimpleValue(other))
          Written(element, s"simple($value)")
        )
    )

  // ---- arrays, maps and tags ----

  private def joined(items: List[String]): Gen[String] =
    items match
      case Nil           => Gen.constant("")
      case first :: rest =>
        separator
          .list(Range.singleton(rest.size))
          .map(separators =>
            first + separators
              .zip(rest)
              .map((between, item) => between + item)
              .mkString
          )

  /** The text of brackets around the items: `S items SOC` inside a definite
    * one, `MS items SOC` or `S` after the `_` of an indefinite one.
    */
  private def bracketed(
      open: Char,
      close: Char,
      items: List[String],
      indefinite: Boolean
  ): Gen[String] =
    for
      inside <- joined(items)
      leading <-
        if indefinite && items.nonEmpty then mandatorySpace else optionalSpace
      trailing <- Gen.element1("", " ", ",", ", ", " ,/c/")
    yield
      val body = if items.isEmpty then leading else leading + inside + trailing
      s"$open${if indefinite then "_" else ""}$body$close"

  private def array(depth: Int): Gen[Written] =
    for
      items <- written(depth - 1).list(Range.linear(0, 3))
      indefinite <- Gen.boolean
      text <- bracketed('[', ']', items.map(_.text), indefinite)
    yield
      val elements = items.map(_.element).toVector
      Written(
        if indefinite then Dom.ArrayElem.Unsized(elements)
        else Dom.ArrayElem.Sized(elements),
        text
      )

  private def map(depth: Int): Gen[Written] =
    val pair =
      for
        key <- written(depth - 1)
        value <- written(depth - 1)
        before <- optionalSpace
        after <- optionalSpace
      yield (key, value, s"${key.text}$before:$after${value.text}")
    for
      pairs <- pair.list(Range.linear(0, 3))
      indefinite <- Gen.boolean
      text <- bracketed('{', '}', pairs.map(_._3), indefinite)
    yield
      val entries = pairs.map((key, value, _) => (key.element, value.element))
      Written(
        if indefinite then Dom.MapElem.Unsized[Dom.Element](entries*)
        else Dom.MapElem.Sized[Dom.Element](entries*),
        text
      )

  private def tagged(depth: Int): Gen[Written] =
    for
      number <- Gen.long(Range.linear(0L, Long.MaxValue))
      content <- written(depth - 1)
      before <- optionalSpace
      after <- optionalSpace
    yield Written(
      Dom.TaggedElem(Tag.Other(number), content.element),
      s"$number($before${content.text}$after)"
    )

  private val leaf: Gen[Written] =
    Gen.choice1(integer, floating, textString, byteString, simple)

  private def written(depth: Int): Gen[Written] =
    if depth <= 0 then leaf
    else
      Gen.frequency1(
        4 -> leaf,
        1 -> array(depth),
        1 -> map(depth),
        1 -> tagged(depth)
      )

  /** Whether the text starts a literal where lambdalattice text stands. */
  private def startsLiteral(text: String): Boolean =
    text.headOption.exists(first => "\"'[{".contains(first) || first.isDigit) ||
      (text.startsWith("-") && text.lift(1).exists(_.isDigit)) || text
        .startsWith("h'") || text.startsWith("b64'")

  /** A literal that lambdalattice text may hold where a literal stands, up to
    * two levels deep.
    */
  private val literal: Gen[Written] =
    written(2).filter(item => startsLiteral(item.text))

  /** The literal as an argument: bare, or alone in parentheses; a tag only in
    * parentheses, since a bare number takes no `(`.
    */
  private def asArgument(item: Written): Gen[String] =
    item.element match
      case Dom.TaggedElem(Tag.Other(_), _) => Gen.constant(s"(${item.text})")
      case _ => Gen.element1(item.text, s"(${item.text})", s"( ${item.text} )")

  property(
    "a literal as an argument spreads into the bits of the bytes borer writes for its item"
  ) {
    for
      item <- literal.forAllWithLog(_.text)
      argument <- asArgument(item).forAll
    yield Result
      .diff(
        parsed(s"λf. f $argument"),
        spread(Literals.arguments(encoded(item.element)))
      )(_ == _)
      .log(argument)
  }

  /** The big-endian bytes of the low `count` bytes of the bits. */
  private def bigEndian(bits: Long, count: Int): Vector[Int] =
    (count - 1 to 0 by -1)
      .map(index => ((bits >>> (8 * index)) & 0xff).toInt)
      .toVector

  /** A floating point value of each width drawn by its bits, a text of it in an
    * array, and the bytes RFC 8949 gives the array, computed here without
    * borer: 0x81, then 0xf9, 0xfa or 0xfb and the value's bits big-endian, NaN
    * as the half 0x7e00. Its purpose is to keep the law (1) from being
    * circular, since borer's own conversion to half precision writes both the
    * expected and the read bytes there.
    */
  private val floatingBits: Gen[(String, Vector[Int])] =
    Gen.choice1(
      Gen
        .int(Range.constant(0, 0xffff))
        .flatMap(bits =>
          val value = java.lang.Float.float16ToFloat(bits.toShort)
          floatingText(value.toDouble).map(text =>
            (
              text,
              if value.isNaN then Vector(0xf9, 0x7e, 0x00)
              else 0xf9 +: bigEndian(bits.toLong, 2)
            )
          )
        ),
      Gen
        .int(Range.constant(Int.MinValue, Int.MaxValue))
        .filter(bits =>
          val value = java.lang.Float.intBitsToFloat(bits)
          !value.isNaN && !sameBits(
            java.lang.Float
              .float16ToFloat(java.lang.Float.floatToFloat16(value)),
            value
          )
        )
        .flatMap(bits =>
          floatingText(java.lang.Float.intBitsToFloat(bits).toDouble)
            .map(text => (text, 0xfa +: bigEndian(bits.toLong, 4)))
        ),
      Gen
        .long(Range.constant(Long.MinValue, Long.MaxValue))
        .filter(bits =>
          val value = java.lang.Double.longBitsToDouble(bits)
          !value.isNaN && java.lang.Double
            .doubleToRawLongBits(value.toFloat.toDouble) != bits
        )
        .flatMap(bits =>
          floatingText(java.lang.Double.longBitsToDouble(bits))
            .map(text => (text, 0xfb +: bigEndian(bits, 8)))
        )
    )

  property(
    "a floating point value is written at the width drawn, its bits big-endian, without borer's conversion"
  ) {
    for (text, bytes) <- floatingBits.forAllWithLog(_._1)
    yield
      val expected = Literal(IArray.from((0x81 +: bytes).map(_.toByte)))
      Result.diff(
        parsed(s"λf. f [$text]"),
        spread(Literals.arguments(expected))
      )(_ == _)
  }

  property("the variable arguments of a literal are its bits, high bit first") {
    for item <- literal.forAllWithLog(_.text)
    yield
      val literalRead = encoded(item.element)
      val bits = Literals.arguments(literalRead).map {
        case DeBruijnTerm.Lambda(
              DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1))
            ) =>
          Some(1)
        case DeBruijnTerm.Lambda(
              DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))
            ) =>
          Some(0)
        case _ => None
      }
      val bytes = bits
        .grouped(8)
        .map(
          _.foldLeft(Option(0))((value, bit) => value.zip(bit).map(_ * 2 + _))
        )
        .toVector
      Result.diff(
        bytes,
        literalRead.bytes.toVector.map(byte => Some(byte & 0xff))
      )(_ == _)
  }

  property("a literal between two arguments spreads in place") {
    for
      first <- literal.forAllWithLog(_.text)
      second <- literal.forAllWithLog(_.text)
      firstArgument <- asArgument(first).forAll
      secondArgument <- asArgument(second).forAll
    yield
      val arguments =
        Vector(DeBruijnTerm.Variable(1)) ++ Literals.arguments(
          encoded(first.element)
        ) ++ Vector(DeBruijnTerm.Variable(1)) ++
          Literals.arguments(encoded(second.element))
      val expected = DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          arguments.foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)(
            DeBruijnTerm.Apply(_, _)
          )
        )
      )
      Result.diff(
        parsed(s"λx. λf. f x $firstArgument x $secondArgument"),
        expected
      )(_ == _)
  }

  /** Whether the literal is a number written with a `.`, which a bare binder
    * does not hold: `λ3.0.` is written `λ(3.0).`.
    */
  private def numberWithPoint(item: Written): Boolean =
    item.text.headOption.exists(first =>
      first.isDigit || first == '-'
    ) && item.text.contains('.') &&
      !item.element.isInstanceOf[Dom.TaggedElem]

  property(
    "a partial function's body sees the outer binders at its own depth, its binder bare or in parentheses"
  ) {
    for
      item <- literal.forAllWithLog(_.text)
      first <- Gen.boolean.forAll
    yield
      val body = if first then "a" else "b"
      val expected = DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          Literals.partialFunction(
            encoded(item.element),
            DeBruijnTerm.Variable(if first then 1 else 0)
          )
        )
      )
      val parenthesized = List(
        s"λa. λb. λ(${item.text}). $body",
        s"λa. λb. λ( ${item.text} ) . $body"
      )
      val bare = if numberWithPoint(item) then Nil
      else
        List(s"λa. λb. λ${item.text}. $body", s"λa. λb. λ${item.text} . $body")
      Result.all(
        (parenthesized ++ bare).map(text =>
          Result.diff(parsed(text), expected)(_ == _).log(text)
        )
      )
  }

  property(
    "a number in a bare binder stops before the dot, and a number with a fraction is no bare binder"
  ) {
    for
      whole <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      fraction <- Gen.int(Range.linear(0, 999)).forAll
    yield
      val integer = s"λa. λ$whole. a"
      val withFraction = s"λa. λ$whole.$fraction. a"
      Result.all(
        List(
          Result
            .diff(
              parsed(integer),
              DeBruijnTerm.Lambda(
                Literals.partialFunction(
                  encoded(Dom.LongElem(whole)),
                  DeBruijnTerm.Variable(0)
                )
              )
            )(
              _ == _
            )
            .log(integer),
          // The binder is the integer, its body `fraction. a`, a literal
          // where a head stands.
          Result
            .assert(problem(withFraction).exists {
              case LambdalatticeProblem
                    .Syntax(SyntaxError.Expected(Expectation.Atom, _), _) =>
                true
              case _ => false
            })
            .log(withFraction)
        )
      )
  }

  property(
    "a number touching ( is a tag in parentheses and as a binder, and an argument when bare"
  ) {
    for
      number <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      content <- literal.forAllWithLog(_.text)
    yield
      val tag = encoded(Dom.TaggedElem(Tag.Other(number), content.element))
      val bare = DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(
          (Literals.arguments(encoded(Dom.LongElem(number))) :+ DeBruijnTerm
            .Variable(0))
            .foldLeft(DeBruijnTerm.Variable(1): DeBruijnTerm)(
              DeBruijnTerm.Apply(_, _)
            )
        )
      )
      Result.all(
        List(
          Result
            .diff(parsed(s"λf. λx. f $number(x)"), bare)(_ == _)
            .log("bare"),
          Result
            .diff(
              parsed(s"λf. f ($number(${content.text}))"),
              spread(Literals.arguments(tag))
            )(_ == _)
            .log("in parentheses"),
          Result
            .diff(
              parsed(s"λa. λ$number(${content.text}). a"),
              DeBruijnTerm.Lambda(
                Literals.partialFunction(tag, DeBruijnTerm.Variable(0))
              )
            )(
              _ == _
            )
            .log("a binder")
        )
      )
  }

  /** A literal holding a part outside the reader's subset: the text before the
    * part, the part, and the text after it.
    */
  private val unsupported: Gen[(String, String, String)] =
    for
      item <- leaf
      digit <- Gen.int(Range.constant(0, 3))
      prefix <- Gen.element1(
        "dt",
        "ip",
        "t1",
        "b1",
        "hash",
        "float",
        "DT",
        "IP",
        "H"
      )
      shape <- Gen.int(Range.constant(0, 8))
    yield shape match
      case 0 => (s"[${item.text}, 1", s"_$digit", "]")
      case 1 => ("[", s"_$digit", s" ${item.text}]")
      case 2 => ("[\"a\"", "_", s", ${item.text}]")
      case 3 => (s"[${item.text}, ", s"$prefix'0'", "]")
      case 4 => ("[", s"<<${item.text}>>", "]")
      case 5 => (s"[${item.text}, ", "`a`", "]")
      case 6 => ("[", "(_ \"a\", \"b\")", "]")
      case 7 => (s"[${item.text}, ", "h'00 ... ff'", "]")
      case _ =>
        ("[", s"${BigInt(Long.MaxValue) + 1 + digit}(${item.text})", "]")

  property("a part outside the subset is reported at its start") {
    for (before, part, after) <- unsupported.forAllWithLog(
        (before, part, after) => before + part + after
      )
    yield
      val text = s"λf. f $before$part$after"
      Result.diff(
        problem(text),
        Some(
          LambdalatticeProblem.Syntax(
            SyntaxError.UnsupportedDiagnosticNotation,
            codePoints(s"λf. f $before")
          )
        )
      )(_ == _)
  }

  property("a name touching a quote is an unsupported prefix, at the name") {
    for name <- Gen.element1("dt", "x", "ip", "t1", "hello").forAll
    yield
      val text = s"λf. f $name'00'"
      Result.diff(
        problem(text),
        Some(
          LambdalatticeProblem
            .Syntax(SyntaxError.UnsupportedDiagnosticNotation, "λf. f ".length)
        )
      )(
        _ == _
      )
  }

  property(
    "an item nested deeper than borer writes is unsupported, at the literal"
  ) {
    // borer refuses an item nested more than 1,000 levels below its root;
    // the innermost array of no item enters no level of its own.
    for depth <- Gen.int(Range.linear(1100, 1200)).forAll
    yield
      val text = s"λf. f ${"[" * depth}${"]" * depth}"
      Result.diff(
        problem(text),
        Some(
          LambdalatticeProblem
            .Syntax(SyntaxError.UnsupportedDiagnosticNotation, "λf. f ".length)
        )
      )(
        _ == _
      )
  }

  /** Where a head stands, as `%s` marks it in each context. */
  private val headContexts: Vector[String] =
    Vector(
      "%s",
      "λx. %s",
      "λx. (x + %s)",
      "λx. (%s + x)",
      "λx. (x ∥ %s)",
      "(%s)",
      "λx. (%s) x"
    )

  property("a literal where a head stands is a syntax error at the literal") {
    for
      context <- Gen.element1(headContexts.head, headContexts.tail*).forAll
      item <- literal.forAllWithLog(_.text)
    yield
      val text = context.format(item.text)
      val atom = problem(text).collect {
        case LambdalatticeProblem.Syntax(
              SyntaxError.Expected(Expectation.Atom, _),
              position
            ) =>
          position
      }
      Result.diff(atom, Some(context.indexOf("%s")))(_ == _).log(text)
  }

  /** An integer of each size `integer` draws: within 64 bits signed, beyond a
    * `Long` within 64 bits of argument, and a big number.
    */
  private val integerValue: Gen[BigInt] =
    Gen.choice1(
      Gen.long(Range.constant(Long.MinValue, Long.MaxValue)).map(BigInt(_)),
      Gen
        .long(Range.constant(Long.MinValue, -1L))
        .map(argument => BigInt(argument) + twoToThe64),
      byteValue
        .list(Range.linear(9, 20))
        .flatMap(bytes =>
          Gen.boolean.map(negative =>
            val magnitude =
              bytes.foldLeft(BigInt(0))((high, byte) => high * 256 + byte)
            if negative then -magnitude - 1 else magnitude
          )
        )
    )

  /** Purpose: catch a decoder of a trace's integer scalars
    * (`Literal.integerRead`) that reads an integer's literal as another
    * integer.
    */
  property("the literal of an integer decodes to the integer") {
    for value <- integerValue.forAll
    yield Result.diff(
      Literal.integerRead(Literal.of(Literal.integerElement(value))),
      Right(value)
    )(_ == _)
  }

  /** Purpose: catch a decoder that accepts an integer spelled in more bytes
    * than its preferred serialization, so that two literals would decode to one
    * integer.
    */
  property(
    "an integer in a longer head than its preferred serialization decodes to no integer"
  ) {
    for value <- Gen.int(Range.constant(0, 23)).forAll
    yield
      val longer = Literal(IArray(0x18.toByte, value.toByte))
      Result.assert(Literal.integerRead(longer).isLeft).log(longer.toString)
  }
