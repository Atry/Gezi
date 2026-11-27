package com.yang_bo.gezi.frontend

import io.bullet.borer.Cbor
import io.bullet.borer.Dom
import io.bullet.borer.Tag
import com.yang_bo.gezi.frontend.Term.λ
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A literal of lambdalattice text: the bytes of one CBOR data item (RFC 8949),
  * the bytes the diagnostic notation of the literal gives. A literal that no
  * library module reads is no error: it is passed and matched like any other.
  * Two literals are equal when their bytes are.
  */
final case class Literal(bytes: IArray[Byte]):

  override def equals(other: Any): Boolean = other match
    case literal: Literal => bytes.toVector == literal.bytes.toVector
    case _                => false

  override def hashCode: Int = bytes.toVector.hashCode

  override def toString: String = bytes.toVector
    .map(byte => f"${byte & 0xff}%02x")
    .mkString("Literal(h'", "", "')")

object Literal:

  /** The CBOR text string (major type 3) of the text, its UTF-8 bytes after the
    * head: the literal `"…"` of the text, a module's name.
    */
  def text(written: String): Literal =
    of(Dom.StringElem(written))

  /** The text of a literal that is one CBOR text string in its preferred
    * serialization, the bytes `text` gives for it, decoded by borer; borer's
    * message, or the reason, for any other bytes (another kind of item, an item
    * followed by more bytes, an indefinite length). The bytes are handed to
    * borer as the `Array[Byte]` it decodes from, an exception to NoArray for
    * exchange with a library.
    */
  @SuppressWarnings(
    Array("com.yang_bo.gezi.warts.NoArray")
  ) // "NoArray wart可以有例外。如果用于和外部库交换，需要Array完全可以理解。我们自己当然还是优先用IArray" (the user, 2026-11-16)
  def textRead(literal: Literal): Either[String, String] =
    Cbor
      .decode(IArray.genericWrapArray(literal.bytes).toArray)
      .to[String]
      .valueEither
      .left
      .map(_.getMessage)
      .flatMap(read =>
        if text(read) == literal then Right(read)
        else
          Left(
            s"$literal is no CBOR text string in its preferred serialization alone"
          )
      )

  /** The data item of an integer in its preferred serialization: within 64
    * bits, major type 0 or 1, a negative value written −1 − n; beyond, tag 2 or
    * 3 over the big-endian bytes of n with no leading zero byte. The item a
    * numeral of the diagnostic notation gives (`DiagnosticNotation`), and the
    * item of an integer in a literal the host builds, as the laws of the
    * library's `from_cbor` and `to_cbor` do.
    */
  def integerElement(value: BigInt): Dom.Element =
    val magnitude = if value >= 0 then value else -value - 1
    if value.isValidLong then Dom.LongElem(value.toLong)
    else if magnitude.bitLength <= 64 then
      Dom.OverLongElem(value < 0, magnitude.toLong)
    else
      val written = magnitude.toByteArray
      val bytes = if written(0) == 0 then
        java.util.Arrays.copyOfRange(written, 1, written.length)
      else written
      Dom.TaggedElem(
        if value >= 0 then Tag.PositiveBigNum else Tag.NegativeBigNum,
        Dom.ByteArrayElem(bytes)
      )

  /** The integer of a literal that is one integer in its preferred
    * serialization, the bytes `of(integerElement(n))` gives for it: the inverse
    * of `integerElement`, so that the host reads a scalar the text writes as a
    * literal, such as the trace player, written in Scala.js, which decodes its
    * scalars there and not in lambdalattice; or borer's message, or the reason,
    * for any other bytes. The bytes are handed to borer as `textRead` hands
    * them.
    */
  @SuppressWarnings(
    Array("com.yang_bo.gezi.warts.NoArray")
  ) // "NoArray wart可以有例外。如果用于和外部库交换，需要Array完全可以理解。我们自己当然还是优先用IArray" (the user, 2026-11-16)
  def integerRead(literal: Literal): Either[String, BigInt] =
    def unsigned(value: Long): BigInt = BigInt(
      java.lang.Long.toUnsignedString(value)
    )
    Cbor
      .decode(IArray.genericWrapArray(literal.bytes).toArray)
      .to[Dom.Element]
      .valueEither
      .left
      .map(_.getMessage)
      .flatMap {
        case Dom.IntElem(value)                => Right(BigInt(value))
        case Dom.LongElem(value)               => Right(BigInt(value))
        case Dom.OverLongElem(negative, value) =>
          Right(if negative then -unsigned(value) - 1 else unsigned(value))
        case Dom.TaggedElem(Tag.PositiveBigNum, Dom.ByteArrayElem(bytes)) =>
          Right(BigInt(1, bytes))
        case Dom.TaggedElem(Tag.NegativeBigNum, Dom.ByteArrayElem(bytes)) =>
          Right(-BigInt(1, bytes) - 1)
        case other => Left(s"$literal is no CBOR integer: $other")
      }
      .flatMap(read =>
        if of(integerElement(read)) == literal then Right(read)
        else
          Left(
            s"$literal is no CBOR integer in its preferred serialization alone"
          )
      )

  /** The bytes borer writes for the data item (`encoding`). Throws
    * `IllegalArgumentException` for an item borer does not write.
    */
  def of(element: Dom.Element): Literal =
    encoding(element).fold(
      problem => throw IllegalArgumentException(problem),
      identity
    )

  /** The bytes borer writes for the data item, every floating point value at
    * the width its element gives (`compressFloatingPointValues = false`, since
    * the reader of the notation chooses the shortest exact width itself), or
    * borer's message for an item it does not write, such as one nested deeper
    * than its configured bound.
    */
  def encoding(element: Dom.Element): Either[String, Literal] =
    Cbor
      .encode(element)
      .withConfig(Cbor.EncodingConfig(compressFloatingPointValues = false))
      .toByteArrayEither
      .map(written => Literal(IArray.unsafeFromArray(written)))
      .left
      .map(_.getMessage)

/** The variable arguments of literals, the variable arguments partial functions
  * of literals (`CONTRIBUTING.md`, "Terms"), and the library's Scott values the
  * host builds.
  *
  * VARIABLE ARGUMENTS (`arguments`): a literal stands only as an argument of an
  * application, or as a binder, and spreads there into the bits of its CBOR
  * bytes, each byte high bit first, each bit a closed Scott boolean,
  * `λt. λf. t` for 1 and `λt. λf. f` for 0; it is never a term of its own,
  * never a head, and spreading it into bits is its serialization.
  *
  * A VARIABLE ARGUMENTS PARTIAL FUNCTION `λL. M` (`partialFunction`) takes L's
  * bits one by one, one abstraction for each, `λx. x K top` where the bit is 1
  * and `λx. x top K` where it is 0, K the abstractions of the bits after it and
  * M after the last, so that a bit that differs gives `top`. There is no
  * checker of the whole key and no check of one byte shared by the keys.
  * Applied to the bits of a key, a choice of partial functions is looked up one
  * bit at a time and, under the tabled evaluator, the tables of `R e1 … ep` are
  * the nodes of a binary trie. A CBOR data item's encoding is never a proper
  * prefix of another's, so the partial function of L applied to the bits of
  * another literal reads top. The partial function and the arguments of one
  * literal come from one encoding, its bytes. Nothing but the β rule is used,
  * no library function and no fixed point.
  *
  * THE LIBRARY'S VALUES (`naturalTerm`, `integerTerm`, `rationalTerm`,
  * `textTerm`) are the Scott data of the library's modules, a `binary` natural,
  * low bit outermost, an integer `λp. λq. p n` or `λp. λq. q n`, a rational
  * `λk. k n d`, a Scott list of bytes. The front end never writes them for a
  * literal: a literal is bits, read into a module's value by the module's
  * `from_cbor`; they are for the host, which builds and reads library data.
  */
object Literals:

  private def closed(term: Term): DeBruijnTerm = term.deBruijnTerm(Map.empty)

  /** top (`Term.top`), the term that stands for no answer: the miss of every
    * partial function of a literal.
    */
  val top: DeBruijnTerm = closed(Term.top)

  private val truth: Term = λ(t => λ(_ => t))

  private val falsity: Term = λ(_ => λ(f => f))

  /** `λt. λf. t`, the bit 1. */
  private[frontend] val one: DeBruijnTerm = closed(truth)

  /** `λt. λf. f`, the bit 0. */
  private[frontend] val zero: DeBruijnTerm = closed(falsity)

  /** The bits of the literal's bytes, each byte high bit first. */
  private[frontend] def bits(literal: Literal): Vector[Boolean] =
    literal.bytes.toVector.flatMap(byte =>
      (7 to 0 by -1).map(position => ((byte >> position) & 1) == 1)
    )

  /** The variable arguments of the literal: the bits of its bytes, each the
    * closed Scott boolean `λt. λf. t` (1) or `λt. λf. f` (0), in order.
    */
  def arguments(literal: Literal): Vector[DeBruijnTerm] =
    bits(literal).map(bit => if bit then one else zero)

  /** The variable arguments partial function `λL. M` of the literal (see the
    * object's Scaladoc). The body is a term read at the partial function's own
    * depth; it stands under the abstractions of the bits, its free variables
    * shifted past them.
    */
  def partialFunction[K](
      literal: Literal,
      body: DeBruijnTermOf[K]
  ): DeBruijnTermOf[K] =
    partialFunctionUnderBits(
      literal,
      shiftedDeeper(body, 0, bits(literal).size).result
    )

  /** The term with every variable free at `depth` made `count` deeper. */
  private def shiftedDeeper[K](
      term: DeBruijnTermOf[K],
      depth: Int,
      count: Int
  ): TailRec[DeBruijnTermOf[K]] = term match
    case DeBruijnTerm.Variable(index) =>
      done(DeBruijnTerm.Variable[K](if index >= depth then index + count
      else index))
    case DeBruijnTerm.Lambda(body) =>
      tailcall(shiftedDeeper(body, depth + 1, count))
        .map(DeBruijnTerm.Lambda(_))
    case DeBruijnTerm.Apply(left, right) =>
      for
        leftShifted <- tailcall(shiftedDeeper(left, depth, count));
        rightShifted <- tailcall(shiftedDeeper(right, depth, count))
      yield DeBruijnTerm.Apply(leftShifted, rightShifted)
    case DeBruijnTerm.Choice(left, right) =>
      for
        leftShifted <- tailcall(shiftedDeeper(left, depth, count));
        rightShifted <- tailcall(shiftedDeeper(right, depth, count))
      yield DeBruijnTerm.Choice(leftShifted, rightShifted)
    case DeBruijnTerm.Parallel(left, right) =>
      for
        leftShifted <- tailcall(shiftedDeeper(left, depth, count));
        rightShifted <- tailcall(shiftedDeeper(right, depth, count))
      yield DeBruijnTerm.Parallel(leftShifted, rightShifted)
    case _ => done(term)

  /** `partialFunction` of a body already read under the abstractions of the
    * literal's bits, as the reader reads it, so that it needs no shift.
    */
  private[frontend] def partialFunctionUnderBits[K](
      literal: Literal,
      matched: DeBruijnTermOf[K]
  ): DeBruijnTermOf[K] =
    bits(literal).foldRight(matched)((bit, rest) =>
      DeBruijnTerm.Lambda[K](
        DeBruijnTerm.Apply[K](
          DeBruijnTerm
            .Apply[K](DeBruijnTerm.Variable[K](0), if bit then rest else top),
          if bit then top else rest
        )
      )
    )

  /** `λs. s b7 … b0`, the 8-tuple of the byte's bits, high bit first: an item
    * of the library's list of bytes (`textTerm`).
    */
  def byteElement(byte: Byte): DeBruijnTerm =
    closed(
      λ(s =>
        (7 to 0 by -1).foldLeft(s)((tuple, position) =>
          tuple(if ((byte >> position) & 1) == 1 then truth else falsity)
        )
      )
    )

  /** `λz. λe. λo. z`, the library's zero (`binary/binary_zero`), a normal form.
    */
  private val binaryZero: DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(2)))
    )

  /** `λz. λe. λo. e h`, twice h (`binary/binary_even` applied to h, β reduced),
    * a normal form for a closed normal h.
    */
  private def binaryEven(half: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(1), half))
      )
    )

  /** `λz. λe. λo. o h`, twice h and one (`binary/binary_odd` applied to h, β
    * reduced), a normal form for a closed normal h.
    */
  private def binaryOdd(half: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), half))
      )
    )

  /** The library's canonical binary natural of the value, its βη normal form,
    * the low bit outermost and no even over zero. Throws
    * `IllegalArgumentException` for a negative value.
    */
  def naturalTerm(value: BigInt): DeBruijnTerm =
    if value < 0 then
      throw IllegalArgumentException(s"a natural is not negative: $value")
    bitsApplied(value, value.bitLength - 1, binaryZero)

  /** The natural whose bits above the position are those of `above`, built from
    * the high bit down, so that the low bit is outermost.
    */
  @tailrec
  private def bitsApplied(
      value: BigInt,
      position: Int,
      above: DeBruijnTerm
  ): DeBruijnTerm =
    if position < 0 then above
    else
      bitsApplied(
        value,
        position - 1,
        if value.testBit(position) then binaryOdd(above) else binaryEven(above)
      )

  /** The library's integer of the value, its βη normal form: `λp. λq. p n` for
    * a natural n (`integer/integer_nonnegative` applied to n, β reduced) and
    * `λp. λq. q n` for −(n + 1) (`integer/integer_negative_successor`).
    */
  def integerTerm(value: BigInt): DeBruijnTerm =
    val (selected, natural) = if value >= 0 then (1, value) else (0, -value - 1)
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Variable(selected),
          naturalTerm(natural)
        )
      )
    )

  /** The library's rational of the fraction, reduced to lowest terms with a
    * positive denominator, its βη normal form `λk. k n d` (`rational/rational`
    * applied to n and d, β reduced). Throws `IllegalArgumentException` for a
    * zero denominator.
    */
  def rationalTerm(numerator: BigInt, denominator: BigInt): DeBruijnTerm =
    if denominator == 0 then
      throw IllegalArgumentException("a rational's denominator is not zero")
    val divisor = numerator.gcd(denominator) * denominator.signum
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Apply(
        DeBruijnTerm
          .Apply(DeBruijnTerm.Variable(0), integerTerm(numerator / divisor)),
        naturalTerm(denominator / divisor)
      )
    )

  /** The empty Scott list, `λn. λc. n`. */
  private val nil: DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  /** The Scott list cell `λn. λc. c e t` of the closed element and tail. */
  private def cell(element: DeBruijnTerm, tail: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), element),
          tail
        )
      )
    )

  /** The library's Scott list of the bytes, each its 8-tuple (`byteElement`).
    */
  def textTerm(bytes: IArray[Byte]): DeBruijnTerm =
    bytes.foldRight(nil)((byte, tail) => cell(byteElement(byte), tail))
