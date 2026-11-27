package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType
import java.math.BigInteger
import com.yang_bo.gezi.contest.natives.plover.PloverNatives
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalNatives
import com.yang_bo.gezi.jit.Native
import com.yang_bo.gezi.jit.NativeArgument
import com.yang_bo.gezi.jit.NativeName
import com.yang_bo.gezi.jit.NativePlace
import com.yang_bo.gezi.jit.StaticBlockMethod

/** The law of the natives of `PloverNatives` that both the JIT and a narrow
  * block can call: on operands drawn by each place, zero at a canonical place
  * and never at a positive one, the implementation on an argument vector
  * computes what the static method computes. Its purpose is to catch a vector
  * implementation that passes its operands in the wrong order or calls another
  * method, which the laws of the static functions do not reach, and a native
  * that no longer carries its static method, which would leave its blocks
  * silently. The natives are named, so that the law cannot hold of an empty
  * set.
  */
class PloverStaticMethodsLawTest extends GeneratedProperties:

  private val natives = PloverNatives().natives.natives

  private val named = Vector(
    "plover_digit_steps",
    "plover_trailing_zeros",
    "plover_divisor_sums",
    "plover_rectangle_cutting",
    "plover_modular_power",
    "plover_modular_tower"
  )

  // A bound that keeps the rectangle's table, cubic in its sides, small.
  private val greatestOperand = 40

  private def drawn(place: NativePlace): Gen[BigInt] = place match
    case NativePlace.Fixed(BinaryNaturalNatives.canonical) =>
      Gen.int(Range.linear(0, greatestOperand)).map(BigInt(_))
    case NativePlace.Fixed(BinaryNaturalNatives.positive) =>
      Gen.int(Range.linear(1, greatestOperand)).map(BigInt(_))
    case other => throw AssertionError(s"a place of no binary natural: $other")

  private def drawnOperands(places: List[NativePlace]): Gen[List[BigInt]] =
    places.foldRight(Gen.constant(List.empty[BigInt]))((place, rest) =>
      for
        operand <- drawn(place)
        others <- rest
      yield operand :: others
    )

  private def staticMethod(name: String, native: Native): StaticBlockMethod =
    native.implementation match
      case method: StaticBlockMethod => method
      case other => throw AssertionError(s"$name has no static method: $other")

  private def calledStatically(
      method: StaticBlockMethod,
      operands: List[BigInt]
  ) =
    val handle = MethodHandles
      .publicLookup()
      .findStatic(
        Class.forName(method.className),
        method.methodName,
        MethodType.methodType(
          classOf[BigInteger],
          java.util.List.of(Vector.fill(operands.size)(classOf[BigInteger])*)
        )
      )
    handle.invokeWithArguments(operands.map(_.bigInteger)*) match
      case result: BigInteger => BinaryNatural(BigInt(result))
      case other              =>
        throw AssertionError(s"${method.methodName} gave no BigInteger: $other")

  named.foreach { name =>
    property(
      s"$name computes on an argument vector what its static method computes"
    ) {
      val native = natives(NativeName.Function(name))
      val method = staticMethod(name, native)
      for operands <- drawnOperands(native.parameters.toList).forAll
      yield
        val byVector = native.implementation(
          operands.toVector.map(operand =>
            NativeArgument.Represented(BinaryNatural(operand))
          )
        )
        Result
          .diff(calledStatically(method, operands), byVector)(_ == _)
          .log(s"the operands $operands")
    }
  }
