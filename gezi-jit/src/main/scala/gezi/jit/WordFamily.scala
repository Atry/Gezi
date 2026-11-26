package gezi.jit

/** A word of the family `word`: its width, any natural, and its bits, the
  * least significant first, as the natural below 2^width they spell. A
  * word of every width a program can write is represented; the natives at
  * 32 and 16 bits hold their operands as `Int` and `Short` themselves.
  */
final case class Word(width: BigInt, bits: BigInt) extends NativeValue:
  require(width >= 0, s"a word of width $width")
  require(bits >= 0 && bits.bitLength <= width, s"a word of width $width with the bits $bits")

/** The family `word` of the fixed-width integers: the words of the
  * knowledge module fixed_width, a word of width w being w cells
  * `word_cell b r`, the least significant bit b first, ending in
  * `word_end`. Both constructors have one alternative, so a layer's
  * constructor is told by the width, the family's parameter, a natural of
  * `big_integer` read from the decoding criterion `word_type W`: at w > 0
  * the one constructor is `word_cell`, whose fields are a boolean and the
  * word of width w - 1, and at 0 it is `word_end`, with no field. It reads
  * no type: it says how the backend holds a value the term already asserts
  * to be a word of the width.
  *
  * THE SHAPE CHECK covers every width at two: `word_end` is the constructor
  * at 0 alone, and `word_cell` the constructor at every w > 0, whose layer
  * (a boolean and the word above, applied to the one case) has the same
  * shape at every w ≥ 1 as at 1, since the parameter changes only the
  * field's parameter, not the define or its fields' count.
  */
object WordFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("word")

  val parameterFamily: Option[FamilyIdentity] = Some(BigIntegerFamily.identity)

  /** The native names the codec encodes the two constructors with.
    *
    * FIXME ([[FamilyIdentity]]): these constructors https://github.com/Atry/private-overlay/issues/2041
    * are still named by strings,
    * which the knowledge binds with `native` declarations
    * (`fixed_width_prolog_backend`), where the constructors of big_integer,
    * boolean and list are their family's representation and their position
    * in their type's `data_family`. Only the six constructor natives of
    * those three families were moved so, and moving these
    * needs a `data_family` on `word_type` whose constructors depend on the
    * width, a value decoded in big_integer (`word_end` alone at 0,
    * `word_cell` alone above), which no reading of the declaration gives.
    */
  val endNative: NativeName = NativeName.Function("word_end")
  val cellNative: NativeName = NativeName.Function("word_cell")

  private val end: DataConstructor = DataConstructor(endNative, Vector.empty)

  private val cell: DataConstructor = DataConstructor(
    cellNative,
    Vector(DataField.unparameterised(BooleanFamily.identity), DataField(identity, parameter => Some(NativeValue.Natural(width(parameter) - 1))))
  )

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] =
    if width(parameter) == 0 then Vector(end) else Vector(cell)

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue =
    (width(parameter), layer) match
      case (atWidth, DataLayer(0, Vector())) if atWidth == 0 => Word(0, 0)
      case (atWidth, DataLayer(0, Vector(NativeValue.Truth(bit), Word(above, bits)))) if above == atWidth - 1 =>
        Word(atWidth, (bits << 1) | (if bit then 1 else 0))
      case (atWidth, other) => throw IllegalArgumentException(s"no layer of a word of width $atWidth: $other")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer =
    (width(parameter), value) match
      case (atWidth, Word(found, _)) if atWidth == 0 && found == 0 => DataLayer(0, Vector.empty)
      case (atWidth, Word(found, bits)) if found == atWidth =>
        DataLayer(0, Vector(NativeValue.Truth(bits.testBit(0)), Word(atWidth - 1, bits >> 1)))
      case (atWidth, other) => throw IllegalArgumentException(s"no word of width $atWidth: $other")

  /** `word_end` is a layer at width 0, and `word_cell` over a boolean and a
    * word of width w at width w + 1.
    */
  override def builtParameter(native: NativeName, fields: Vector[NativeValue]): Option[Option[NativeValue]] =
    (native, fields) match
      case (`endNative`, Vector())                                   => Some(Some(NativeValue.Natural(0)))
      case (`cellNative`, Vector(NativeValue.Truth(_), Word(above, _))) => Some(Some(NativeValue.Natural(above + 1)))
      case _                                                         => None

  /** The constructors at widths 0 (`word_end`) and 1 (`word_cell`), which
    * cover every width (THE SHAPE CHECK).
    */
  override val shapeParameters: Vector[Option[NativeValue]] =
    Vector(Some(NativeValue.Natural(0)), Some(NativeValue.Natural(1)))

  /** The width the parameter gives. Throws `IllegalArgumentException` for no
    * parameter or one that is no natural: the JIT gives the family only
    * parameters it decoded in `big_integer`, every one of which is a width.
    */
  private def width(parameter: Option[NativeValue]): BigInt = parameter match
    case Some(NativeValue.Natural(value)) if value >= 0 => value
    case other => throw IllegalArgumentException(s"no width of a word: $other")
