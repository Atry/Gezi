package gezi.contest.entries.solo

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result

import gezi.contest.natives.solo.SoloBinaryOperations
import gezi.contest.natives.solo.SoloNatives
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.BinaryNatural
import gezi.jit.NativeArgument
import gezi.jit.NativeName

/** The law that the native `solo_binary_times`, called by the JIT on its
  * argument vector, computes what its static method
  * `SoloBinaryOperations.times`, which a narrow block calls, computes, on
  * generated canonical binary naturals, zero and equal operands included.
  * `StaticBlockMethodLawTest` checks this of the standard set only. Its purpose
  * is to catch an implementation that unpacks or packs its operands or its
  * result wrong, so that a call through the JIT and a call from a block
  * disagree.
  */
class TimesStaticMethodLawTest extends GeneratedProperties:

  private lazy val native =
    SoloNatives().natives.natives(NativeName.Function("solo_binary_times"))

  /** A canonical binary natural: zero, or a long shifted by up to 200 digits.
    */
  private val natural: Gen[BigInt] =
    Gen.choice1(
      Gen.constant(BigInt(0)),
      for
        digits <- Gen.long(Range.linear(0L, Long.MaxValue))
        shift <- Gen.int(Range.linear(0, 200))
      yield BigInt(digits) << shift
    )

  property(
    "the native computes on its argument vector what its static method computes"
  ) {
    for
      left <- natural.forAll
      drawn <- natural.forAll
      equal <- Gen.boolean.forAll
    yield
      val right = if equal then left else drawn
      val byVector = native.implementation(
        Vector(left, right).map(operand =>
          NativeArgument.Represented(BinaryNatural(operand))
        )
      )
      Result.diff(
        byVector,
        BinaryNatural(
          BigInt(SoloBinaryOperations.times(left.bigInteger, right.bigInteger))
        )
      )(_ == _)
  }
