package gezi.jit

import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType
import java.math.BigInteger
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law of `StaticBlockMethod`: for every native of a backend whose
  * implementation is one, the static method a narrow block calls gives, on
  * canonical binary naturals, the value the implementation gives on its
  * argument vector. Its purpose is to catch a static method that computes
  * something else than its native (a wrong method name, operands swapped
  * in a non-commutative operation, a method of another class), which the
  * blocks' own law would catch only on programs that call that native with
  * operands where the two differ. Checked on the standard set
  * (`NativeBackend.standard`); the operands are generated, of up to
  * about 360 binary digits.
  */
class StaticBlockMethodLawTest extends GeneratedProperties:

  /** The natives of the backend whose implementation a block may call. */
  private def staticNatives(backend: NativeBackend): Vector[(NativeName, Int, StaticBlockMethod)] =
    backend.natives.toVector.sortBy(_._1.toString).flatMap((name, native) =>
      native.implementation match
        case method: StaticBlockMethod => Some((name, native.parameters.size, method))
        case _                         => None
    )

  /** A canonical binary natural: a long shifted by up to 300 digits. */
  private val natural: Gen[BigInt] =
    for
      digits <- Gen.long(Range.linear(0L, Long.MaxValue))
      shift <- Gen.int(Range.linear(0, 300))
    yield BigInt(digits) << shift

  /** The static method called on the operands, by its class and name, its
    * result of the JVM convention the method declares read as the value of
    * its family.
    */
  private def calledStatically(method: StaticBlockMethod, operands: Vector[BigInt]): NativeValue =
    val resultClass: Class[?] = method.result match
      case StaticBlockResult.Natural => classOf[BigInteger]
      case StaticBlockResult.Truth   => java.lang.Boolean.TYPE
    val handle = MethodHandles
      .publicLookup()
      .findStatic(
        Class.forName(method.className),
        method.methodName,
        MethodType.methodType(resultClass, java.util.List.of(Vector.fill(operands.size)(classOf[BigInteger])*))
      )
    handle.invokeWithArguments(operands.map(_.bigInteger)*) match
      case result: BigInteger        => BinaryNatural(BigInt(result))
      case result: java.lang.Boolean => NativeValue.Truth(result.booleanValue)
      case other                     => throw IllegalStateException(s"a static block method gave neither a BigInteger nor a boolean: $other")

  test("the standard set has static block methods") {
    assert(staticNatives(NativeBackend.standard).nonEmpty)
  }

  property("aStaticBlockMethodComputesWhatItsNativeComputes") {
    val natives = staticNatives(NativeBackend.standard)
    for
      position <- Gen.int(Range.linear(0, natives.size - 1)).forAll
      (name, places, method) = natives(position)
      drawn <- Gen.list(natural, Range.singleton(places)).forAll
      // Half the time every operand is the first, so that a comparison is
      // checked where its operands are equal too.
      repeated <- Gen.boolean.forAll
      operands = if repeated then drawn.headOption.fold(drawn)(first => drawn.map(_ => first)) else drawn
    yield
      val byVector = NativeBackend.standard
        .natives(name)
        .implementation(operands.toVector.map(operand => NativeArgument.Represented(BinaryNatural(operand))))
      Result.diff(calledStatically(method, operands.toVector), byVector)(_ == _).log(name.toString)
  }
