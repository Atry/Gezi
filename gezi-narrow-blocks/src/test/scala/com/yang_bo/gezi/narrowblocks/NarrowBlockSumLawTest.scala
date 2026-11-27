package com.yang_bo.gezi.narrowblocks

import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.jit.BinaryNaturalFamily
import com.yang_bo.gezi.jit.NativesProvider
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.CombinatorProperty
import com.yang_bo.gezi.standardlibrary.NativeBound
import com.yang_bo.gezi.standardlibrary.Property
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger

private given narrowBlockSumLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of a left-nested sum of the binary naturals' plus over canonical
  * numerals, zero among them, `plus (… (plus l0 l1) …) ln`: it is the program's
  * one block and computes the sum of its numerals; and the constant the reader
  * folds it into (`NarrowExpression.Folded`) is the value the same sum computes
  * unfolded, written as the body of a closed function, one numeral its
  * parameter, and called on that numeral, a call that no fold reads into. Their
  * purpose is to catch an operand the narrow kinds do not admit, the numeral
  * zero, a native of no operands, which was none, so that a sum with zero was
  * no block and a block holding `plus zero zero` was refused, the inner sum
  * read as a literal that does not decode; and a fold that computes another
  * value than the code it replaces.
  *
  * The names are bound by hand, as in `NarrowBlockDepthLawTest`.
  */
class NarrowBlockSumLawTest extends GeneratedProperties:

  /** λx. x x, bound to zero. */
  private val zero = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Slot(0)),
    Vector(Hole.Bound(0)),
    Vector.empty
  )

  /** λx y. y x, bound to even. */
  private val even =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(1), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y z. z y x, bound to odd. */
  private val odd = NoFacts.thunkOrInstance(
    Code.Apply(Code.Apply(Code.Slot(2), Code.Slot(1)), Code.Slot(0)),
    Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
    Vector.empty
  )

  /** λx y. x (y y), the criterion `binary_set` whose `data_family` lists zero,
    * even and odd, in the codec's order (`BinaryNaturalFamily`).
    */
  private val binarySet = NoFacts.thunkOrInstance(
    Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(1), Code.Slot(1))),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )

  /** λx y. y y x, bound to plus. */
  private val plus = NoFacts.thunkOrInstance(
    Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(1)), Code.Slot(0)),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector.empty
  )

  private val compilation = NarrowBlockCompilation(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector(
        NativeBound(Pure.required(plus), "wren_binary_plus")
      ),
      Vector(
        CombinatorProperty(
          Pure.required(binarySet),
          Property.NativeSpecialization(BinaryNaturalFamily.identity.name)
        ),
        CombinatorProperty(
          Pure.required(binarySet),
          Property.DataFamily(0, Vector(zero, even, odd).map(Pure.required))
        )
      )
    ),
    NativesProvider.loaded,
    com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts
  )

  /** The canonical binary numeral of the value, least significant digit
    * outermost.
    */
  private def numeral(value: Int): Configured[NoFacts.type] =
    if value == 0 then zero
    else
      NoFacts.application(
        if (value & 1) == 1 then odd else even,
        numeral(value >> 1)
      )

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] =
    Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 7)))

  /** The sum's body over its numerals, the one at `parameter` the slot 0 of a
    * function's hole, plus the slot 1 and the other numerals the slots after
    * it, in order: the fillings of `function`.
    */
  private def body(values: Vector[Int], parameter: Int): Code =
    val slots = values.indices.map(position =>
      if position == parameter then Code.Slot(0)
      else
        Code.Slot(2 + values.indices.filter(_ != parameter).indexOf(position))
    )
    slots.tail.foldLeft(slots.head)((sum, slot) =>
      Code.Apply(Code.Apply(Code.Slot(1), sum), slot)
    )

  /** The closed function of the sum's body, its parameter the numeral at
    * `parameter`.
    */
  private def function(
      values: Vector[Int],
      parameter: Int
  ): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      body(values, parameter),
      Vector(Hole.Bound(0)),
      plus +: values.indices
        .filter(_ != parameter)
        .map(position => numeral(values(position)))
        .toVector
    )

  stoppableProperty(
    "a sum of numerals, zero among them, is one block that computes the sum, folded as unfolded"
  ) { stopped =>
    for
      first <- value.forAll
      rest <- Gen.list(value, Range.linear(1, 4)).forAll
      parameter <- Gen.int(Range.constant(0, rest.size)).forAll
    yield
      val values = (first +: rest).toVector
      val sum = rest.foldLeft(numeral(first))((sum, literal) =>
        NoFacts.application(NoFacts.application(plus, sum), numeral(literal))
      )
      val call = NoFacts.application(
        function(values, parameter),
        numeral(values(parameter))
      )
      val stop = StopSignal.completedWith(stopped)
      val expected =
        Right(Vector(Some(BigInteger.valueOf(values.map(_.toLong).sum))))
      def computed(program: Configured[NoFacts.type]) =
        compilation
          .compiled(compilation.blocks(program), DebugAttributes.Omitted, stop)
          .map(_.map(_.run(stop)))
      Result
        .all(
          List(
            Result
              .assert(compilation.blocks(sum) == Vector(sum))
              .log(
                s"the blocks are not the sum: ${compilation.blocks(sum).size} blocks"
              ),
            Result.diff(computed(sum), expected)(_ == _).log("folded"),
            Result
              .assert(compilation.blocks(call) == Vector(call))
              .log(
                s"the blocks are not the call: ${compilation.blocks(call).size} blocks"
              ),
            Result
              .diff(computed(call), expected)(_ == _)
              .log("unfolded, the call")
          )
        )
        .log(
          s"the numerals ${values.mkString(", ")}, the parameter at $parameter"
        )
  }
