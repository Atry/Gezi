package gezi.jit

import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType
import java.math.BigInteger
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.NoFacts

/** The law of `StaticBlockMethod`: for every native of a backend whose
  * implementation is one, the static method a narrow block calls gives, on
  * canonical binary naturals, the value the implementation gives on its
  * argument vector. Its purpose is to catch a static method that computes
  * something else than its native (a wrong method name, operands swapped in a
  * non-commutative operation, a method of another class), which the blocks' own
  * law would catch only on programs that call that native with operands where
  * the two differ. Checked on the standard set (`NativeBackend.standard`); the
  * operands are generated in the method's convention
  * (`StaticBlockMethod.operands`): canonical binary naturals of up to about 360
  * binary digits, or JVM `int`s, whose edges are drawn often.
  */
class StaticBlockMethodLawTest extends GeneratedProperties:

  /** The natives of the backend whose implementation a block may call. */
  private def staticNatives(
      backend: NativeBackend
  ): Vector[(NativeName, Int, StaticBlockMethod)] =
    backend.natives.toVector
      .sortBy(_._1.toString)
      .flatMap((name, native) =>
        native.implementation match
          case method: StaticBlockMethod =>
            Some((name, native.parameters.size, method))
          case _ => None
      )

  /** A canonical binary natural: a long shifted by up to 300 digits. */
  private val natural: Gen[BigInt] =
    for
      digits <- Gen.long(Range.linear(0L, Long.MaxValue))
      shift <- Gen.int(Range.linear(0, 300))
    yield BigInt(digits) << shift

  /** A JVM `int`, its edges drawn often. */
  private val jvmInt: Gen[Int] =
    Gen.frequency1(
      3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)),
      1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue)
    )

  /** An operand of the convention: a canonical binary natural, or the bits of a
    * 32-bit word.
    */
  private def operand(
      convention: StaticBlockOperands
  ): Gen[NativeValue[Nothing]] = convention match
    case StaticBlockOperands.Naturals => natural.map(BinaryNatural(_))
    case StaticBlockOperands.JvmInts  => jvmInt.map(JvmIntNatives.value)

  /** The static method called on the operands, by its class and name, its
    * operands and its result of the JVM conventions the method declares, the
    * result read as the value of its family.
    */
  private def calledStatically(
      method: StaticBlockMethod,
      operands: Vector[NativeValue[Nothing]]
  ): NativeValue[Nothing] =
    val resultClass: Class[?] = method.result match
      case StaticBlockResult.Natural | StaticBlockResult.NaturalOrNoAnswer =>
        classOf[BigInteger]
      case StaticBlockResult.Truth       => java.lang.Boolean.TYPE
      case StaticBlockResult.Constructed => classOf[ConstructedNaturals]
      case StaticBlockResult.NaturalList => classOf[Vector[?]]
      case StaticBlockResult.JvmInt      => java.lang.Integer.TYPE
      case StaticBlockResult.Lattice     => classOf[NaturalLattice]
    val convention: (Class[?], Vector[AnyRef]) = method.operands match
      case StaticBlockOperands.Naturals =>
        (
          classOf[BigInteger],
          operands.map {
            case BinaryNatural(value) => value.bigInteger
            case other                =>
              throw IllegalStateException(s"a natural operand, not $other")
          }
        )
      case StaticBlockOperands.JvmInts =>
        (
          java.lang.Integer.TYPE,
          operands.map(value =>
            Integer.valueOf(
              JvmIntNatives.bits(NativeArgument.Represented(value))
            )
          )
        )
    val (operandClass, passed) = convention
    val handle = MethodHandles
      .publicLookup()
      .findStatic(
        Class.forName(method.className),
        method.methodName,
        MethodType.methodType(
          resultClass,
          java.util.List.of(Vector.fill(operands.size)(operandClass)*)
        )
      )
    (method.result, handle.invokeWithArguments(passed*)) match
      case (StaticBlockResult.JvmInt, result: java.lang.Integer) =>
        JvmIntNatives.value(result.intValue)
      case (_, result: BigInteger)        => BinaryNatural(BigInt(result))
      case (_, result: java.lang.Boolean) =>
        NativeValue.Truth(result.booleanValue)
      case (_, other) =>
        throw IllegalStateException(
          s"a static block method gave no BigInteger, boolean or int: $other"
        )

  test("the standard set has static block methods") {
    assert(staticNatives(NativeBackend.standard).nonEmpty)
  }

  property("aStaticBlockMethodComputesWhatItsNativeComputes") {
    val natives = staticNatives(NativeBackend.standard)
    for
      position <- Gen.int(Range.linear(0, natives.size - 1)).forAll
      (name, places, method) = natives(position)
      drawn <- Gen
        .list(operand(method.operands), Range.singleton(places))
        .forAll
      // Half the time every operand is the first, so that a comparison is
      // checked where its operands are equal too.
      repeated <- Gen.boolean.forAll
      operands =
        if repeated then
          drawn.headOption.fold(drawn)(first => drawn.map(_ => first))
        else drawn
    yield
      val byVector = NativeBackend.standard
        .natives(name)
        .implementation[NoFacts.type](
          operands.toVector.map(NativeArgument.Represented(_))
        )(using NoFacts)
      Result
        .diff(calledStatically(method, operands.toVector), byVector)(_ == _)
        .log(name.toString)
  }
