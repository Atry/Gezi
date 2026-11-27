package gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BinaryNaturalNatives
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativeName
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.saturation.StopSignal
import gezi.standardlibrary.NativeBound

private given narrowNaturalListPlaceLawTestNoFacts: NoFacts.type = NoFacts

/** The static method of the law's native: the sum of the list's elements and
  * of a natural. Public, since a block's generated class calls it.
  */
object NaturalListSum:
  def summed(elements: Vector[BigInteger], base: BigInteger): BigInteger = elements.foldLeft(base)(_.add(_))

/** The law's native as a block calls it. Its list place is one the JIT never
  * fills, so the implementation on an argument vector is never run.
  */
private object NaturalListSumMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[NaturalListSum.type].getName.stripSuffix("$")
  val methodName: String = "summed"
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("natural_list_sum", arguments)

/** The static method of the law's native with a positive place and no list
  * place. Public, since a block's generated class calls it. It throws on a
  * divisor of 0, which is how a call the place does not license shows.
  */
object PositiveDivisorQuotient:
  def quotient(dividend: BigInteger, divisor: BigInteger): BigInteger = dividend.divide(divisor)

/** The quotient native as a block calls it; the law never runs it on an
  * argument vector.
  */
private object PositiveDivisorQuotientMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[PositiveDivisorQuotient.type].getName.stripSuffix("$")
  val methodName: String = "quotient"
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("positive_divisor_quotient", arguments)

/** The laws of a native's place `NativePlace.NaturalList`. A block with lists
  * passes the elements of a list whose root filter names the place's element
  * representation; an operand with no such filter, a list that may hold 0 at
  * a place of positive naturals or a natural at a list's place among them,
  * compiles no call; and the narrow blocks without lists do not compile a call
  * of such a native. Their purpose is to catch an element lost or reordered on
  * the way to the native, a descriptor that does not match the static method,
  * an operand the native's places do not admit reaching it, and a block
  * without lists that would call the method with the wrong descriptor.
  */
class NarrowNaturalListPlaceLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  /** λx y. x y (y x), a term of no other name of the library, bound to the
    * native. The law reads the calling convention, so its body is not read.
    */
  private val listSum: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(0), Code.Slot(1)), Code.Apply(Code.Slot(1), Code.Slot(0))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y. y x (x y), bound to the native whose places declare the positive naturals. */
  private val positiveListSum: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(0)), Code.Apply(Code.Slot(0), Code.Slot(1))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y. y (x y) x, bound to the native with a positive place and no list place. */
  private val positiveDivisorQuotient: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(1), Code.Apply(Code.Slot(0), Code.Slot(1))), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y. x (y x) y, bound to a native whose result a block cannot hold. */
  private val unheldResultQuotient: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(1), Code.Slot(0))), Code.Slot(1)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y. y x y, bound to a native with a place the block does not license. */
  private val unlicensedPlaceQuotient: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(0)), Code.Slot(1)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  private val index = compilation.index.copy(nativeBound =
    compilation.index.nativeBound ++ Vector(
      NativeBound(Pure.required(listSum), "natural_list_sum"),
      NativeBound(Pure.required(positiveListSum), "positive_list_sum"),
      NativeBound(Pure.required(positiveDivisorQuotient), "positive_divisor_quotient"),
      NativeBound(Pure.required(unheldResultQuotient), "unheld_result_quotient"),
      NativeBound(Pure.required(unlicensedPlaceQuotient), "unlicensed_place_quotient")
    )
  )

  private val natives: NativeBackend = compilation.natives.extended(
    NativeBackend.functions(
      Map(
        "natural_list_sum" -> Native(
          Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical), NativePlace.Fixed(BinaryNaturalNatives.canonical)),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NaturalListSumMethod
        ),
        "positive_list_sum" -> Native(
          Vector(NativePlace.NaturalList(BinaryNaturalNatives.positive), NativePlace.Fixed(BinaryNaturalNatives.positive)),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          NaturalListSumMethod
        ),
        "positive_divisor_quotient" -> Native(
          Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical), NativePlace.Fixed(BinaryNaturalNatives.positive)),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          PositiveDivisorQuotientMethod
        ),
        "unheld_result_quotient" -> Native(
          Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical), NativePlace.Fixed(BinaryNaturalNatives.canonical)),
          NativePlace.Fixed(Representation.BigInteger),
          PositiveDivisorQuotientMethod
        ),
        "unlicensed_place_quotient" -> Native(
          Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical), NativePlace.Item),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          PositiveDivisorQuotientMethod
        )
      ),
      Vector.empty
    )
  )

  private val listBlocks = NarrowBlockCompilation(index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)

  private val value: Gen[Int] = Gen.int(Range.constant(0, 7))

  private val elements: Gen[Vector[Int]] = Gen.list(value, Range.linear(0, 6)).map(_.toVector)

  private def called(operand: Configured[NoFacts.type], base: Int): Configured[NoFacts.type] =
    NoFacts.application(NoFacts.application(listSum, operand), numeral(base))

  private def filteredList(numbers: Vector[Int]): Configured[NoFacts.type] =
    NoFacts.parallel(list(numbers.map((_, false))), listCriterion(true))

  private def ran(compilation: NarrowBlockCompilation, program: Configured[NoFacts.type], stop: StopSignal): Either[String, Vector[Option[BigInt]]] =
    compilation
      .compiled(compilation.blocks(program), DebugAttributes.Omitted, stop)
      .map(_.map(_.run(stop).map(BigInt(_))))

  /** That the compilation refused the call for its operand, and for no other reason. */
  private def refusedAtPlace(result: Either[String, Vector[Option[BigInt]]]): Result =
    Result
      .assert(result.fold(_.contains("is not known to be of the representation its place declares"), _ => false))
      .log(s"the compilation gave $result")

  stoppableProperty("a block passes the elements of a filtered list to the native, in order") { stopped =>
    for
      numbers <- elements.forAll
      base <- value.forAll
    yield Result.diff(
      ran(listBlocks, called(filteredList(numbers), base), StopSignal.completedWith(stopped)),
      Right(Vector(Some(BigInt(numbers.sum + base))))
    )(_ == _)
  }

  stoppableProperty("a natural at the list's place compiles no call") { stopped =>
    for
      number <- value.forAll
      base <- value.forAll
    yield refusedAtPlace(
      ran(listBlocks, called(NoFacts.parallel(numeral(number), criterion(true)), base), StopSignal.completedWith(stopped))
    )
  }

  private def positiveCalled(listAdmitsZero: Boolean, numbers: Vector[Int], baseAdmitsZero: Boolean, base: Int): Configured[NoFacts.type] =
    NoFacts.application(
      NoFacts.application(positiveListSum, NoFacts.parallel(list(numbers.map((_, false))), listCriterion(listAdmitsZero))),
      NoFacts.parallel(numeral(base), criterion(baseAdmitsZero))
    )

  private val positiveValue: Gen[Int] = Gen.int(Range.constant(1, 7))

  private val positiveElements: Gen[Vector[Int]] = Gen.list(positiveValue, Range.linear(1, 6)).map(_.toVector)

  stoppableProperty("a place of positive naturals takes operands whose filters name them") { stopped =>
    for
      numbers <- positiveElements.forAll
      base <- positiveValue.forAll
    yield Result.diff(
      ran(listBlocks, positiveCalled(false, numbers, false, base), StopSignal.completedWith(stopped)),
      Right(Vector(Some(BigInt(numbers.sum + base))))
    )(_ == _)
  }

  stoppableProperty("a list whose filter admits zero compiles no call of a native of positive elements") { stopped =>
    for
      numbers <- elements.forAll
      base <- positiveValue.forAll
    yield refusedAtPlace(ran(listBlocks, positiveCalled(true, numbers, false, base), StopSignal.completedWith(stopped)))
  }

  stoppableProperty("a natural whose filter admits zero compiles no call at a place of positive naturals") { stopped =>
    for
      numbers <- positiveElements.forAll
      base <- value.forAll
    yield refusedAtPlace(ran(listBlocks, positiveCalled(false, numbers, true, base), StopSignal.completedWith(stopped)))
  }

  private def quotientCalled(dividend: Int, divisorAdmitsZero: Boolean, divisor: Int): Configured[NoFacts.type] =
    NoFacts.application(
      NoFacts.application(positiveDivisorQuotient, NoFacts.parallel(numeral(dividend), criterion(true))),
      NoFacts.parallel(numeral(divisor), criterion(divisorAdmitsZero))
    )

  stoppableProperty("a closed call of a native with no list place is computed when its filters name its places") { stopped =>
    for
      dividend <- value.forAll
      divisor <- positiveValue.forAll
    yield Result.diff(
      ran(listBlocks, quotientCalled(dividend, false, divisor), StopSignal.completedWith(stopped)),
      Right(Vector(Some(BigInt(dividend / divisor))))
    )(_ == _)
  }

  stoppableProperty("a closed call whose operand is not known at a positive place is neither folded nor compiled") { stopped =>
    for
      dividend <- value.forAll
      divisor <- value.forAll
    yield refusedAtPlace(ran(listBlocks, quotientCalled(dividend, true, divisor), StopSignal.completedWith(stopped)))
  }

  private def filteredCall(function: Configured[NoFacts.type], first: Int, second: Int): Configured[NoFacts.type] =
    NoFacts.application(
      NoFacts.application(function, NoFacts.parallel(numeral(first), criterion(true))),
      NoFacts.parallel(numeral(second), criterion(true))
    )

  stoppableProperty("a native whose result a block cannot hold compiles no call") { stopped =>
    for
      dividend <- value.forAll
      divisor <- positiveValue.forAll
    yield
      val result = ran(listBlocks, filteredCall(unheldResultQuotient, dividend, divisor), StopSignal.completedWith(stopped))
      Result.assert(result.fold(_.contains("has no static method a block can call"), _ => false)).log(s"the compilation gave $result")
  }

  stoppableProperty("a place the block does not license compiles no call") { stopped =>
    for
      dividend <- value.forAll
      divisor <- positiveValue.forAll
    yield refusedAtPlace(ran(listBlocks, filteredCall(unlicensedPlaceQuotient, dividend, divisor), StopSignal.completedWith(stopped)))
  }

  stoppableProperty("the narrow blocks without lists compile no call of a native with a positive place") { stopped =>
    for
      dividend <- value.forAll
      divisor <- value.forAll
      divisorAdmitsZero <- Gen.boolean.forAll
    yield
      val withoutLists = gezi.narrowblocks.NarrowBlockCompilation(index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)
      val program = quotientCalled(dividend, divisorAdmitsZero, divisor)
      Result.all(
        List(
          Result
            .assert(withoutLists.staticMethod(NativeName.Function("positive_divisor_quotient"), 2).isEmpty)
            .log("a static method is offered"),
          Result
            .assert(withoutLists.compiled(withoutLists.blocks(program), DebugAttributes.Omitted, StopSignal.completedWith(stopped)).fold(_ => true, _.isEmpty))
            .log("a block was compiled")
        )
      )
  }

  stoppableProperty("the narrow blocks without lists compile no call of such a native") { stopped =>
    for
      numbers <- elements.forAll
      base <- value.forAll
    yield
      val withoutLists = gezi.narrowblocks.NarrowBlockCompilation(index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)
      val program = called(filteredList(numbers), base)
      Result.all(
        List(
          Result.assert(withoutLists.staticMethod(NativeName.Function("natural_list_sum"), 2).isEmpty).log("a static method is offered"),
          Result
            .assert(withoutLists.compiled(withoutLists.blocks(program), DebugAttributes.Omitted, StopSignal.completedWith(stopped)).fold(_ => true, _.isEmpty))
            .log("a block was compiled")
        )
      )
  }
