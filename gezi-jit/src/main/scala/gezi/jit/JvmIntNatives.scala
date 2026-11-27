package gezi.jit

/** The natives of the 32-bit words held as the JVM's `int` (`JvmIntFamily`),
  * bound by the knowledge module `jvm_int` to the thin defines of
  * `corpora/library/fixed_width/int32_arithmetic` and `int32_comparison`:
  * each takes its operands in the family `jvm_int` and computes what its
  * define computes on two 32-bit words, `word_add`, `word_subtract`,
  * `word_multiply` and `word_negate` at the width 32 being the JVM's `int`
  * arithmetic, which wraps modulo 2³², `word_equal` the equality of the bits
  * and `word_less_than` the signed comparison of two's complement words, as
  * that define's comment states. A sum, a difference, a product or a negation
  * is a value of the family again; a comparison is a boolean of the standard
  * set's family.
  *
  * Under the dispatch strategy `fallback` the JIT calls a native only on
  * operands already in the family's representation, so a native never
  * decides what an operand is. A result's view `r ∥ jvm_int_type` is r by
  * theorem (S) of `docs/design/gezi-type-preservation-proofs.md`, the
  * criterion's row of its table resting on lemma 25.3 of
  * `docs/design/gezi-set-equations-proofs.md`.
  *
  * Each implementation is also a `StaticBlockMethod`, a static method of
  * `JvmIntOperations` over JVM `int`s, which a block may call directly.
  */
object JvmIntNatives:

  /** The representation of the family. */
  val jvmInt: Representation[Nothing] = Representation.Data(JvmIntFamily.identity, None)

  /** The six natives, part of the standard set: lazy, as
    * `BinaryNaturalNatives.operations` is, since the standard set reads them
    * while it is made.
    */
  lazy val operations: NativeBackend = NativeBackend.functions(
    Map(
      "jvm_int_add"       -> binary("add", JvmIntOperations.add),
      "jvm_int_subtract"  -> binary("subtract", JvmIntOperations.subtract),
      "jvm_int_multiply"  -> binary("multiply", JvmIntOperations.multiply),
      "jvm_int_negate"    -> Native(Vector(NativePlace.Fixed(jvmInt)), NativePlace.Fixed(jvmInt), JvmIntUnary("negate", JvmIntOperations.negate)),
      "jvm_int_equal"     -> comparison("equal", JvmIntOperations.equal),
      "jvm_int_less_than" -> comparison("lessThan", JvmIntOperations.lessThan)
    ),
    Vector.empty
  )

  private def binary(methodName: String, operation: (Int, Int) => Int): Native =
    Native(Vector(NativePlace.Fixed(jvmInt), NativePlace.Fixed(jvmInt)), NativePlace.Fixed(jvmInt), JvmIntBinary(methodName, operation))

  private def comparison(methodName: String, operation: (Int, Int) => Boolean): Native =
    Native(Vector(NativePlace.Fixed(jvmInt), NativePlace.Fixed(jvmInt)), NativePlace.Fixed(Representation.Truth), JvmIntComparison(methodName, operation))

  /** The bits of a value of the family as the JVM's `int`. Throws
    * `IllegalArgumentException` for any other argument: the JIT passes a
    * native only operands of its places.
    */
  def bits(argument: NativeArgument[Any]): Int = argument match
    case NativeArgument.Represented(JvmBits(32, bits)) => bits.toInt
    case other                                        => throw IllegalArgumentException(s"a jvm_int operand, not $other")

  /** The value of the family of the JVM `int`'s bits. */
  def value(bits: Int): NativeValue[Nothing] = JvmBits(32, Integer.toUnsignedLong(bits))

/** The six operations on 32-bit words as public static methods over JVM
  * `int`s, a comparison's result a JVM `boolean` (Scala emits a static
  * forwarder for each method of a top-level object with no companion
  * class): what a block calls with `invokestatic`.
  */
object JvmIntOperations:

  /** The sum modulo 2³². */
  def add(left: Int, right: Int): Int = left + right

  /** The difference modulo 2³². */
  def subtract(left: Int, right: Int): Int = left - right

  /** The product modulo 2³². */
  def multiply(left: Int, right: Int): Int = left * right

  /** The negation modulo 2³². */
  def negate(value: Int): Int = -value

  /** Whether the two have the same bits. */
  def equal(left: Int, right: Int): Boolean = left == right

  /** Whether the left is below the right as two's complement words. */
  def lessThan(left: Int, right: Int): Boolean = left < right

/** An operation on two 32-bit words as a native's implementation and as
  * the static method of `JvmIntOperations` named `methodName`.
  */
private final class JvmIntBinary(val methodName: String, operation: (Int, Int) => Int)
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val className: String = classOf[JvmIntOperations.type].getName.stripSuffix("$")

  override val result: StaticBlockResult = StaticBlockResult.JvmInt

  override val operands: StaticBlockOperands = StaticBlockOperands.JvmInts

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] = arguments match
    case Vector(left, right) => JvmIntNatives.value(operation(JvmIntNatives.bits(left), JvmIntNatives.bits(right)))
    case other               => throw IllegalArgumentException(s"a jvm_int operation of two operands, not $other")

  override def toString: String = s"a jvm_int operation ($methodName)"

/** An operation on one 32-bit word as a native's implementation and as the
  * static method of `JvmIntOperations` named `methodName`.
  */
private final class JvmIntUnary(val methodName: String, operation: Int => Int)
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val className: String = classOf[JvmIntOperations.type].getName.stripSuffix("$")

  override val result: StaticBlockResult = StaticBlockResult.JvmInt

  override val operands: StaticBlockOperands = StaticBlockOperands.JvmInts

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] = arguments match
    case Vector(operand) => JvmIntNatives.value(operation(JvmIntNatives.bits(operand)))
    case other           => throw IllegalArgumentException(s"a jvm_int operation of one operand, not $other")

  override def toString: String = s"a jvm_int operation ($methodName)"

/** A comparison of two 32-bit words as a native's implementation, giving a
  * boolean of the standard set's family, and as the static method of
  * `JvmIntOperations` named `methodName`, giving a JVM `boolean`.
  */
private final class JvmIntComparison(val methodName: String, comparison: (Int, Int) => Boolean)
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val className: String = classOf[JvmIntOperations.type].getName.stripSuffix("$")

  override val result: StaticBlockResult = StaticBlockResult.Truth

  override val operands: StaticBlockOperands = StaticBlockOperands.JvmInts

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] = arguments match
    case Vector(left, right) => NativeValue.Truth(comparison(JvmIntNatives.bits(left), JvmIntNatives.bits(right)))
    case other               => throw IllegalArgumentException(s"a jvm_int comparison of two operands, not $other")

  override def toString: String = s"a jvm_int comparison ($methodName)"
