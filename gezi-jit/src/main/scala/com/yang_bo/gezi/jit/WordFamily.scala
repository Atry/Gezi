package com.yang_bo.gezi.jit

/** A word of the family `word`: its width, any natural, and its bits, the least
  * significant first, as the natural below 2^width they spell. A word of every
  * width a program can write is represented; the natives at 32 and 16 bits hold
  * their operands as `Int` and `Short` themselves.
  */
final case class Word(width: BigInt, bits: BigInt) extends NativeValue[Nothing]:
  require(width >= 0, s"a word of width $width")
  require(
    bits >= 0 && bits.bitLength <= width,
    s"a word of width $width with the bits $bits"
  )

/** The parameter of the family `word`: the width, a natural, written
  * `word_type W` in the criterion.
  */
final case class WordWidth(width: BigInt) extends FamilyParameter[Nothing]:
  require(width >= 0, s"a word of width $width")

/** The family `word` of the fixed-width integers: the words of the knowledge
  * module fixed_width, a word of width w being w cells `word_cell b r`, the
  * least significant bit b first, ending in `word_end`. Both constructors have
  * one alternative, so a layer's constructor is told by the width, the family's
  * parameter, a natural of `big_integer` read from the decoding criterion
  * `word_type W`: at w > 0 the one constructor is `word_cell`, whose fields are
  * a boolean and the word of width w - 1, and at 0 it is `word_end`, with no
  * field. It reads no type: it says how the backend holds a value the term
  * already asserts to be a word of the width.
  *
  * THE SHAPE CHECK covers every width at two: `word_end` is the constructor at
  * 0 alone, and `word_cell` the constructor at every w > 0, whose layer (a
  * boolean and the word above, applied to the one case) has the same shape at
  * every w ≥ 1 as at 1, since the parameter changes only the field's parameter,
  * not the define or its fields' count.
  */
object WordFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("word")

  val parameterFamily: Option[FamilyIdentity] = Some(BigIntegerFamily.identity)

  /** The native names the codec encodes the two constructors with: the family's
    * identity and each constructor's position in the `data_family` of
    * `word_type` (`fixed_width_prolog_backend`), `word_end` at 0 and
    * `word_cell` at 1, never a string of their own ([[FamilyIdentity]]). Which
    * of the two a layer has is the width's, the family's parameter: the
    * declaration lists both, and `constructors` gives the one the width admits,
    * so the backend's check reads both over `shapeParameters`.
    */
  val endNative: NativeName = NativeName.Constructor(identity, 0)
  val cellNative: NativeName = NativeName.Constructor(identity, 1)

  private val end: DataConstructor = DataConstructor(endNative, Vector.empty)

  private val cell: DataConstructor = DataConstructor(
    cellNative,
    Vector(
      DataField.unparameterised(BooleanFamily.identity),
      DataField(identity, parameter => Some(WordWidth(width(parameter) - 1)))
    )
  )

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] =
    if width(parameter) == 0 then Vector(end) else Vector(cell)

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] =
    (width(parameter), layer) match
      case (atWidth, DataLayer(0, Vector())) if atWidth == 0 => Word(0, 0)
      case (
            atWidth,
            DataLayer(0, Vector(NativeValue.Truth(bit), Word(above, bits)))
          ) if above == atWidth - 1 =>
        Word(atWidth, (bits << 1) | (if bit then 1 else 0))
      case (atWidth, other) =>
        throw IllegalArgumentException(
          s"no layer of a word of width $atWidth: $other"
        )

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] =
    (width(parameter), value) match
      case (atWidth, Word(found, _)) if atWidth == 0 && found == 0 =>
        DataLayer(0, Vector.empty)
      case (atWidth, Word(found, bits)) if found == atWidth =>
        DataLayer(
          0,
          Vector(
            NativeValue.Truth(bits.testBit(0)),
            Word(atWidth - 1, bits >> 1)
          )
        )
      case (atWidth, other) =>
        throw IllegalArgumentException(s"no word of width $atWidth: $other")

  /** `word_end` is a layer at width 0, and `word_cell` over a boolean and a
    * word of width w at width w + 1.
    */
  override def builtParameter[Term](
      native: NativeName,
      fields: Vector[NativeValue[Term]]
  ): Option[Option[FamilyParameter[Term]]] =
    (native, fields) match
      case (`endNative`, Vector()) => Some(Some(WordWidth(0)))
      case (`cellNative`, Vector(NativeValue.Truth(_), Word(above, _))) =>
        Some(Some(WordWidth(above + 1)))
      case _ => None

  /** The constructors at widths 0 (`word_end`) and 1 (`word_cell`), which cover
    * every width (THE SHAPE CHECK).
    */
  override val shapeParameters: Vector[Option[FamilyParameter[Nothing]]] =
    Vector(Some(WordWidth(0)), Some(WordWidth(1)))

  override def parameterOf[Term](
      value: NativeValue[Term]
  ): FamilyParameter[Term] = value match
    case NativeValue.Natural(width) => WordWidth(width)
    case other => throw IllegalArgumentException(s"no width of a word: $other")

  override def parameterValue[Term](
      parameter: FamilyParameter[Term]
  ): NativeValue[Term] = parameter match
    case WordWidth(width) => NativeValue.Natural(width)
    case other => throw IllegalArgumentException(s"no width of a word: $other")

  /** The width the parameter gives. Throws `IllegalArgumentException` for no
    * parameter or one that is no width: the JIT gives the family only
    * parameters it decoded in `big_integer`, every one of which is a width.
    */
  private def width(parameter: Option[FamilyParameter[Any]]): BigInt =
    parameter match
      case Some(WordWidth(value)) => value
      case other                  =>
        throw IllegalArgumentException(s"no width of a word: $other")
