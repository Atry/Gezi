package com.yang_bo.gezi.contest.natives.solo

import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalNatives
import com.yang_bo.gezi.jit.Native
import com.yang_bo.gezi.jit.NativeArgument
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.jit.NativePlace
import com.yang_bo.gezi.jit.NativeValue
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.jit.StaticBlockMethod

import java.math.BigInteger

/** The natives bound by `corpora/compiler/solo_binary_natives`: the product of
  * two canonical binary naturals, the native of `merge_binary_times`.
  */
final class SoloNatives extends NativesProvider:

  def natives: NativeBackend = NativeBackend.functions(
    Map(
      TimesMethod.nativeName -> Native(
        Vector(
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NativePlace.Fixed(BinaryNaturalNatives.canonical)
        ),
        NativePlace.Fixed(BinaryNaturalNatives.canonical),
        TimesMethod
      )
    ),
    Vector.empty
  )

/** The operations of `SoloNatives` as public static methods over
  * `java.math.BigInteger`, what a narrow block calls with `invokestatic`.
  */
object SoloBinaryOperations:

  /** The product. */
  def times(left: BigInteger, right: BigInteger): BigInteger =
    left.multiply(right)

/** `SoloBinaryOperations.times` as the native's implementation on its argument
  * vector and as the static method a narrow block calls.
  */
private object TimesMethod
    extends (Vector[NativeArgument[Any]] => NativeValue[Nothing]),
      StaticBlockMethod:

  val nativeName: String = "solo_binary_times"

  val className: String =
    classOf[SoloBinaryOperations.type].getName.stripSuffix("$")

  val methodName: String = "times"

  def apply(arguments: Vector[NativeArgument[Any]]): NativeValue[Nothing] =
    arguments match
      case Vector(
            NativeArgument.Represented(BinaryNatural(left)),
            NativeArgument.Represented(BinaryNatural(right))
          ) =>
        BinaryNatural(
          BigInt(SoloBinaryOperations.times(left.bigInteger, right.bigInteger))
        )
      case _ => Native.outsidePlaces(nativeName, arguments)
