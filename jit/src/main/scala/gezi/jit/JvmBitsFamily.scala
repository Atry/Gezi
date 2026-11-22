package gezi.jit

/** A value of a JVM value type of `width` bits: the bits, the low `width` bits
  * of a `long` and every bit above them clear. How they are read (signed or
  * not, an integer or an IEEE 754 number) is the descriptor's at the position
  * they are used, as an opcode says how a JVM instruction reads a slot.
  */
final case class JvmBits(width: Int, bits: Long) extends NativeValue:
  require(JvmBitsFamily.widths.contains(width), s"no JVM value type has $width bits")
  require(width == java.lang.Long.SIZE || (bits >>> width) == 0L, s"the value $bits has bits above its width $width")

/** The family of the Java FFI's bit tuples of one width
  * (`corpora/library/java_ffi/bits`), held as the JVM value `JvmBits`, so that
  * a value the FFI passes on costs no encoding. It has one constructor, the
  * tuple maker, of `width` boolean fields, the high bit first. The Scott tuple
  * is read or written only where a program takes the tuple apart.
  *
  * A knowledge file names a family by its codec name (`jvm_bits_8`,
  * `jvm_bits_16`, `jvm_bits_32`, `jvm_bits_64`). The name says how the backend
  * holds a value the term already asserts to be a tuple of the width; the
  * family reads no type.
  */
final case class JvmBitsFamily(width: Int) extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec(s"jvm_bits_$width")

  val parameterFamily: Option[FamilyIdentity] = None

  private val constructor: DataConstructor = DataConstructor(
    NativeName.Constructor(identity, 0),
    Vector.fill(width)(DataField.unparameterised(BooleanFamily.identity))
  )

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] = Vector(constructor)

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue = layer match
    case DataLayer(0, fields) if fields.size == width =>
      JvmBits(
        width,
        fields.foldLeft(0L) {
          case (sofar, NativeValue.Truth(bit)) => (sofar << 1) | (if bit then 1L else 0L)
          case (_, other)                      => throw IllegalArgumentException(s"a bit of ${identity.name} is $other")
        }
      )
    case other => throw IllegalArgumentException(s"no layer of ${identity.name}: $other")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer = value match
    case JvmBits(`width`, bits) =>
      DataLayer(0, (width - 1 to 0 by -1).toVector.map(bit => NativeValue.Truth(((bits >>> bit) & 1L) == 1L)))
    case other => throw IllegalArgumentException(s"no value of ${identity.name}: $other")

object JvmBitsFamily:

  /** The widths of the JVM's value types. */
  val widths: Vector[Int] = Vector(8, 16, 32, 64)

  /** The families of the four widths. */
  val all: Vector[JvmBitsFamily] = widths.map(JvmBitsFamily(_))

  /** The bits of the value as a `JvmBits` of the width, those above it dropped. */
  def masked(width: Int, value: Long): JvmBits =
    JvmBits(width, if width == java.lang.Long.SIZE then value else value & ((1L << width) - 1L))

  /** The natives of the tuple makers. They give no result's parameter from
    * their operands (`Native.resultParameter` is `None`), so the JIT calls one
    * only where a decoding point reads the family from a filter written in the
    * term: a tuple maker of w fields is one instruction with every other
    * library term of its shape, and a native called bottom-up on represented
    * fields would conclude the family from the value.
    */
  val constructorNatives: Map[NativeName, Native] =
    all.map { family =>
      val constructor = family.constructors(None) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"${family.identity.name} has the constructors $other")
      constructor.native -> Native(
        constructor.fields.map(field => NativePlace.OfParameter(field.representation)),
        NativePlace.Parameter(family.identity),
        arguments =>
          family.built(
            None,
            DataLayer(
              0,
              arguments.map {
                case NativeArgument.Represented(value) => value
                case other => throw IllegalArgumentException(s"a field of ${family.identity.name} that is not a native value: $other")
              }
            )
          ),
        _ => true,
        _ => None
      )
    }.toMap
