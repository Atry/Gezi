package com.yang_bo.gezi.ffi

import com.yang_bo.gezi.hotspot.ForeignCall
import com.yang_bo.gezi.hotspot.ForeignValue
import java.lang.invoke.MethodHandle
import java.lang.invoke.MethodHandles
import java.lang.invoke.MethodType
import scala.jdk.CollectionConverters.*

/** A call of a continuation-aware method: a public static method whose last
  * parameter is the `ReplyHandler` and which returns `void`. This is how the
  * JVM service of the first step calls a method. FIXME
  * (https://github.com/Atry/private-overlay/issues/1797): it boxes its
  * arguments and calls through a `MethodHandle`, which whole-block compilation
  * replaces by a direct call.
  */
final case class ContinuationAwareCall(
    method: MethodHandle,
    arguments: Vector[AnyRef]
):

  /** Calls the method. What it throws reaches the caller: the FFI catches
    * nothing, and offers no way to catch.
    */
  def requested(replies: ReplyHandler): Unit =
    val _ = method.invokeWithArguments((arguments :+ replies).asJava)

object ContinuationAwareCall:

  /** The method the call names with its arguments boxed as the descriptor's
    * parameters, or none when the arguments are not values of those parameters.
    * A symbol that names no method throws what the JVM's look-up throws. Throws
    * `UnsupportedOperationException` for a method that is not
    * continuation-aware.
    */
  def of(call: ForeignCall): Option[ContinuationAwareCall] =
    val loader = classOf[ReplyHandler].getClassLoader
    val methodType =
      MethodType.fromMethodDescriptorString(call.descriptor, loader)
    val parameters = methodType.parameterList.asScala.toVector
    if methodType.returnType != java.lang.Void.TYPE || !parameters.lastOption
        .contains(classOf[ReplyHandler])
    then
      throw UnsupportedOperationException(
        s"the method ${call.owner}.${call.name}${call.descriptor}, which is no continuation-aware method, runs in a later step (https://github.com/Atry/private-overlay/issues/1797)"
      )
    val values = parameters.init
    Option
      .when(values.size == call.arguments.size)(values.zip(call.arguments))
      .flatMap(pairs =>
        pairs
          .foldLeft(Option(Vector.empty[AnyRef])) {
            case (read, (parameter, value)) =>
              for sofar <- read; boxed <- boxed(parameter, value)
              yield sofar :+ boxed
          }
          .map(arguments =>
            val found =
              Class.forName(call.owner.replace('/', '.'), true, loader)
            ContinuationAwareCall(
              MethodHandles.publicLookup
                .findStatic(found, call.name, methodType),
              arguments
            )
          )
      )

  /** The boxed value of the primitive type, or none for a value of another
    * width.
    */
  private def boxed(primitive: Class[?], value: ForeignValue): Option[AnyRef] =
    value match
      case ForeignValue.Truth(truth) if primitive == java.lang.Boolean.TYPE =>
        Some(java.lang.Boolean.valueOf(truth))
      case ForeignValue.Bits(8, bits) if primitive == java.lang.Byte.TYPE =>
        Some(java.lang.Byte.valueOf(bits.toByte))
      case ForeignValue.Bits(16, bits) if primitive == java.lang.Short.TYPE =>
        Some(java.lang.Short.valueOf(bits.toShort))
      case ForeignValue.Bits(16, bits)
          if primitive == java.lang.Character.TYPE =>
        Some(java.lang.Character.valueOf(bits.toChar))
      case ForeignValue.Bits(32, bits) if primitive == java.lang.Integer.TYPE =>
        Some(java.lang.Integer.valueOf(bits.toInt))
      case ForeignValue.Bits(32, bits) if primitive == java.lang.Float.TYPE =>
        Some(
          java.lang.Float.valueOf(java.lang.Float.intBitsToFloat(bits.toInt))
        )
      case ForeignValue.Bits(64, bits) if primitive == java.lang.Long.TYPE =>
        Some(java.lang.Long.valueOf(bits))
      case ForeignValue.Bits(64, bits) if primitive == java.lang.Double.TYPE =>
        Some(java.lang.Double.valueOf(java.lang.Double.longBitsToDouble(bits)))
      case _ => None
