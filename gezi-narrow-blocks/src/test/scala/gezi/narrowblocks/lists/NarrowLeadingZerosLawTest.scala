package gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.saturation.StopSignal

/** The law of a numeral with leading zeros (the trap of
  * `repeated_library_binary_domain_traps`): a block that reads `binary_even`
  * over zero gives no value, alone and as a native's operand, since no
  * canonical natural is that term; the canonical numeral of the same value in
  * its place gives the value and the sum. Its purpose is to catch a block that
  * computes the leading zeros away, `even 0` as 0, which answered that
  * family falsely on 2026-11-21.
  */
class NarrowLeadingZerosLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  /** The canonical numeral of the value with the zero at its end replaced by
    * `even` applied `padding` times to zero.
    */
  private def padded(value: Int, padding: Int): Instruction =
    if value == 0 then (1 to padding).foldLeft(zero)((inner, _) => Instruction.Apply(even, inner))
    else Instruction.Apply(if (value & 1) == 1 then odd else even, padded(value >> 1, padding))

  private def plusOf(left: Instruction, right: Instruction): Instruction = Instruction.Apply(Instruction.Apply(plus, left), right)

  stoppableProperty("a numeral with leading zeros gives no value, alone or added; its canonical numeral gives its value and the sum") {
    stopped =>
      for
        value <- Gen.int(Range.linear(0, 1000)).forAll
        padding <- Gen.int(Range.linear(1, 4)).forAll
        summand <- Gen.int(Range.linear(0, 1000)).forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        def values(program: Instruction): Either[String, Vector[Option[BigInteger]]] =
          compilation.compiled(compilation.blocks(program), DebugAttributes.Omitted, stop).map(_.map(_.run(stop)))
        def answered(program: Instruction): Vector[BigInteger] = values(program).toOption.toVector.flatten.flatten
        Result
          .all(
            List(
              Result.diff(answered(padded(value, padding)), Vector.empty[BigInteger])(_ == _).log("the padded numeral alone"),
              Result
                .diff(answered(plusOf(padded(value, padding), numeral(summand))), Vector.empty[BigInteger])(_ == _)
                .log("the padded numeral added"),
              Result
                .diff(values(plusOf(numeral(value), numeral(summand))), Right(Vector(Some(BigInteger.valueOf(value.toLong + summand)))))(_ == _)
                .log("the canonical numeral added")
            )
          )
          .log(s"the value $value, the padding $padding, the summand $summand")
  }
