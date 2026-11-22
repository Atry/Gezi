package gezi.jit

import java.math.BigInteger

/** The natives of four operations of the standard library's module
  * binary, bound to their defines by the knowledge module
  * `binary_operations_wren_backend`: each takes two canonical binary
  * naturals, held as one `BigInt` each by the framework's family
  * `binary_natural` at the parameter true (`BinaryNaturalFamily`), and gives
  * one. Each computes what its define file's comment claims the define
  * computes on canonical binary naturals: `merge_binary_plus` the sum,
  * `binary_maximum` the larger, `binary_minimum` the smaller and
  * `binary_bitwise_or` the bitwise or; each result is a canonical binary
  * natural, a `BigInt` that is not negative. Two more, written for the
  * narrow blocks, take one or two: `wren_binary_increment`, the natural after
  * the operand, `merge_binary_increment`'s value, and `wren_binary_equality`,
  * whether the two are equal, `merge_binary_equality`'s value, a boolean of
  * the standard set's family `boolean`. Under the dispatch strategy
  * `fallback` the JIT calls a native only on operands already in this
  * representation, so a native never decides what an operand is; any other
  * call runs the define's body. No type is held here: the place of each
  * parameter names a representation, as the standard set's natives do.
  *
  * Each implementation is also a `StaticBlockMethod`, a static method of
  * `BinaryNaturalOperations`, which a narrow block calls directly.
  *
  * They were a contributed module until 2026-11-07, when the base
  * knowledge's natives became framework natives: they are in the standard set
  * (`NativeBackend.standard`), so every entry whose library enables
  * `binary_operations_wren_backend` or `wren_typed_natives` finds them.
  */
object BinaryNaturalNatives:

  /** The canonical binary naturals' representation. */
  val canonical: Representation = Representation.Data(BinaryNaturalFamily.identity, Some(NativeValue.Truth(true)))

  /** The positive binary naturals' representation, the one `binary_set false` names. */
  val positive: Representation = Representation.Data(BinaryNaturalFamily.identity, Some(NativeValue.Truth(false)))

  /** The six natives, part of the standard set. */
  val operations: NativeBackend = NativeBackend.functions(
    Map(
      "wren_binary_plus"       -> binary("plus", BinaryNaturalOperations.plus),
      "wren_binary_maximum"    -> binary("maximum", BinaryNaturalOperations.maximum),
      "wren_binary_minimum"    -> binary("minimum", BinaryNaturalOperations.minimum),
      "wren_binary_bitwise_or" -> binary("bitwiseOr", BinaryNaturalOperations.bitwiseOr),
      "wren_binary_increment" -> Native(
        Vector(NativePlace.Fixed(canonical)),
        NativePlace.Fixed(canonical),
        UnaryOperation("increment", BinaryNaturalOperations.increment)
      ),
      "wren_binary_equality" -> Native(
        Vector(NativePlace.Fixed(canonical), NativePlace.Fixed(canonical)),
        NativePlace.Fixed(Representation.Truth),
        NaturalComparison("equality", BinaryNaturalOperations.equality)
      )
    ),
    Vector.empty
  )

  /** The native of an operation on two canonical binary naturals, the
    * static method of `BinaryNaturalOperations` of that name.
    */
  private def binary(methodName: String, operation: (BigInteger, BigInteger) => BigInteger): Native =
    Native(
      Vector(NativePlace.Fixed(canonical), NativePlace.Fixed(canonical)),
      NativePlace.Fixed(canonical),
      Pairwise(methodName, operation)
    )

/** The six operations on canonical binary naturals as public static
  * methods over `java.math.BigInteger`, equality's result a JVM `boolean`
  * (Scala emits a static forwarder for
  * each method of a top-level object with no companion class): what a
  * narrow block calls with `invokestatic`.
  */
object BinaryNaturalOperations:

  /** The sum. */
  def plus(left: BigInteger, right: BigInteger): BigInteger = left.add(right)

  /** The larger. */
  def maximum(left: BigInteger, right: BigInteger): BigInteger = left.max(right)

  /** The smaller. */
  def minimum(left: BigInteger, right: BigInteger): BigInteger = left.min(right)

  /** The bitwise or. */
  def bitwiseOr(left: BigInteger, right: BigInteger): BigInteger = left.or(right)

  /** The natural after the operand, `merge_binary_increment`'s value on a
    * canonical binary natural.
    */
  def increment(value: BigInteger): BigInteger = value.add(BigInteger.ONE)

  /** Whether the two are equal, `merge_binary_equality`'s value on two
    * canonical binary naturals: true and false of native_types, the boolean
    * family's values.
    */
  def equality(left: BigInteger, right: BigInteger): Boolean = left.equals(right)

/** An operation on two canonical binary naturals as a native's
  * implementation, on its argument vector, and as the static method of
  * `BinaryNaturalOperations` named `methodName`, which computes the same.
  */
private final class Pairwise(val methodName: String, operation: (BigInteger, BigInteger) => BigInteger)
    extends (Vector[NativeArgument] => NativeValue),
      StaticBlockMethod:

  val className: String = classOf[BinaryNaturalOperations.type].getName.stripSuffix("$")

  def apply(arguments: Vector[NativeArgument]): NativeValue = arguments match
    case Vector(NativeArgument.Represented(BinaryNatural(left)), NativeArgument.Represented(BinaryNatural(right))) =>
      BinaryNatural(BigInt(operation(left.bigInteger, right.bigInteger)))
    case other => throw IllegalArgumentException(s"a binary natural operation of two canonical binary naturals, not $other")

  override def toString: String = s"a binary natural operation ($methodName)"

/** An operation on one canonical binary natural as a native's
  * implementation, on its argument vector, and as the static method of
  * `BinaryNaturalOperations` named `methodName`, which computes the same.
  */
private final class UnaryOperation(val methodName: String, operation: BigInteger => BigInteger)
    extends (Vector[NativeArgument] => NativeValue),
      StaticBlockMethod:

  val className: String = classOf[BinaryNaturalOperations.type].getName.stripSuffix("$")

  def apply(arguments: Vector[NativeArgument]): NativeValue = arguments match
    case Vector(NativeArgument.Represented(BinaryNatural(value))) => BinaryNatural(BigInt(operation(value.bigInteger)))
    case other => throw IllegalArgumentException(s"a binary natural operation of one canonical binary natural, not $other")

  override def toString: String = s"a binary natural operation ($methodName)"

/** A comparison of two canonical binary naturals as a native's
  * implementation, on its argument vector, giving a boolean of the standard
  * set's family, and as the static method of `BinaryNaturalOperations` named
  * `methodName`, which computes the same as a JVM `boolean`.
  */
private final class NaturalComparison(val methodName: String, comparison: (BigInteger, BigInteger) => Boolean)
    extends (Vector[NativeArgument] => NativeValue),
      StaticBlockMethod:

  val className: String = classOf[BinaryNaturalOperations.type].getName.stripSuffix("$")

  override val result: StaticBlockResult = StaticBlockResult.Truth

  def apply(arguments: Vector[NativeArgument]): NativeValue = arguments match
    case Vector(NativeArgument.Represented(BinaryNatural(left)), NativeArgument.Represented(BinaryNatural(right))) =>
      NativeValue.Truth(comparison(left.bigInteger, right.bigInteger))
    case other => throw IllegalArgumentException(s"a comparison of two canonical binary naturals, not $other")

  override def toString: String = s"a comparison of binary naturals ($methodName)"
