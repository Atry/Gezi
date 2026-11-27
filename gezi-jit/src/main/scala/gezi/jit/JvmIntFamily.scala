package gezi.jit

/** The family `jvm_int` of the 32-bit words held as the JVM's `int`
  * (`corpora/library/fixed_width/jvm_int_type`, the knowledge module
  * `jvm_int`): a value is `JvmBits(32, bits)`, whose storage is one `int`
  * (`IntStorage`, the value class it shares with the Java FFI's `jvm_bits_32`,
  * the family told apart by the representation). Its one constructor is
  * `word_type`'s `word_cell`, the `data_family` of `jvm_int_type` listing it at
  * 0, of the fields the least significant bit, a boolean, and the word of the
  * 31 bits above it, of the family `word` at the width 31: a layer is the
  * 32-bit word's, so the unique spelling of a stored int is
  * `word_cell (b ∥ boolean_type) (w ∥ word_type 31) ∥ jvm_int_type`, one layer
  * viewed in O(1).
  *
  * The family registers no native of its constructor: `word_cell` in the head
  * position is the family `word`'s, which builds a 32-bit `Word`, so a term
  * evaluated outside a filter by `jvm_int_type` gives a word, and only a
  * construction site that reads its fields already stored, a native's result or
  * a decode point gives an int. The JVM type of the storage is the codec's own,
  * as a native's static method has its own signature; the family reads no type.
  */
object JvmIntFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("jvm_int")

  val parameterFamily: Option[FamilyIdentity] = None

  override val jvmPrimitive: Option[JvmPrimitive] = Some(JvmPrimitive.Int)

  /** The width of the word above the least significant bit. */
  private val aboveWidth: BigInt = BigInt(31)

  private val cell: DataConstructor = DataConstructor(
    NativeName.Constructor(identity, 0),
    Vector(
      DataField.unparameterised(BooleanFamily.identity),
      DataField(WordFamily.identity, _ => Some(WordWidth(aboveWidth)))
    )
  )

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] = Vector(cell)

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] = layer match
    case DataLayer(0, Vector(NativeValue.Truth(bit), Word(width, bits)))
        if width == aboveWidth =>
      JvmBits(32, (bits.toLong << 1) | (if bit then 1L else 0L))
    case other =>
      throw IllegalArgumentException(s"no layer of a jvm_int: $other")

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] = value match
    case JvmBits(32, bits) =>
      DataLayer(
        0,
        Vector(
          NativeValue.Truth((bits & 1L) == 1L),
          Word(aboveWidth, BigInt(bits >>> 1))
        )
      )
    case other => throw IllegalArgumentException(s"no value of jvm_int: $other")
