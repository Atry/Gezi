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
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult
import gezi.saturation.StopSignal
import gezi.standardlibrary.NativeBound

private given narrowNoAnswerLawTestNoFacts: NoFacts.type = NoFacts

/** The static methods of the law's natives. Public, since a block's generated
  * class calls them.
  */
object NoAnswerLawMethods:

  /** The natural when the list holds it, and otherwise null, no answer. */
  def found(elements: Vector[BigInteger], wanted: BigInteger): BigInteger =
    if elements.contains(wanted) then wanted else null

  /** The sum of the list's elements and of a natural. */
  def summed(elements: Vector[BigInteger], base: BigInteger): BigInteger = elements.foldLeft(base)(_.add(_))

/** The native that may say it has no answer, as a block calls it. */
private object NoAnswerFoundMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[NoAnswerLawMethods.type].getName.stripSuffix("$")
  val methodName: String = "found"
  override val result: StaticBlockResult = StaticBlockResult.NaturalOrNoAnswer
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("no_answer_found", arguments)

/** An ordinary native whose natural operand may be a call of the other. */
private object NoAnswerSumMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[NoAnswerLawMethods.type].getName.stripSuffix("$")
  val methodName: String = "summed"
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("no_answer_sum", arguments)

/** The laws of a native whose result is `StaticBlockResult.NaturalOrNoAnswer`.
  * At a block's root, its natural is the block's value and its null the
  * outcome `NoAnswer`, told apart from a block that gave no value; anywhere
  * else no block is compiled, and the narrow blocks without lists compile no
  * call of it. Their purpose is to catch a no answer read as a natural by
  * arithmetic, a no answer taken for a block that gave no value, and a block
  * without lists that would call such a method.
  */
class NarrowNoAnswerLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  /** λx y. x y (y x), a term of no other name of the library, bound to the
    * native that may say it has no answer.
    */
  private val foundTerm: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(0), Code.Slot(1)), Code.Apply(Code.Slot(1), Code.Slot(0))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  /** λx y. y x (x y), bound to the ordinary native. */
  private val sumTerm: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(0)), Code.Apply(Code.Slot(0), Code.Slot(1))),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  private val index = compilation.index.copy(nativeBound =
    compilation.index.nativeBound ++ Vector(NativeBound(Pure.required(foundTerm), "no_answer_found"), NativeBound(Pure.required(sumTerm), "no_answer_sum"))
  )

  private val listAndNatural =
    Vector(NativePlace.NaturalList(BinaryNaturalNatives.canonical), NativePlace.Fixed(BinaryNaturalNatives.canonical))

  private val natives: NativeBackend = compilation.natives.extended(
    NativeBackend.functions(
      Map(
        "no_answer_found" -> Native(listAndNatural, NativePlace.Fixed(BinaryNaturalNatives.canonical), NoAnswerFoundMethod),
        "no_answer_sum" -> Native(listAndNatural, NativePlace.Fixed(BinaryNaturalNatives.canonical), NoAnswerSumMethod)
      ),
      Vector.empty
    )
  )

  private val listBlocks = NarrowBlockCompilation(index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)

  private val value: Gen[Int] = Gen.int(Range.constant(0, 7))

  private val elements: Gen[Vector[Int]] = Gen.list(value, Range.linear(0, 6)).map(_.toVector)

  private def filteredList(numbers: Vector[Int]): Configured[NoFacts.type] =
    NoFacts.parallel(list(numbers.map((_, false))), listCriterion(true))

  private def foundCall(numbers: Vector[Int], wanted: Int): Configured[NoFacts.type] =
    NoFacts.application(NoFacts.application(foundTerm, filteredList(numbers)), numeral(wanted))

  stoppableProperty("at a block's root, the native's natural is the value and its null is no answer") { stopped =>
    for
      numbers <- elements.forAll
      wanted <- value.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val outcomes = listBlocks
        .compiled(listBlocks.blocks(foundCall(numbers, wanted)), DebugAttributes.Omitted, stop)
        .map(_.map(_.outcome(stop)))
      val expected =
        if numbers.contains(wanted) then NarrowBlockOutcome.Computed(BigInteger.valueOf(wanted.toLong))
        else NarrowBlockOutcome.NoAnswer
      Result.diff(outcomes, Right(Vector(expected)))(_ == _)
  }

  stoppableProperty("a call of the native under another native compiles no block") { stopped =>
    for
      numbers <- elements.forAll
      wanted <- value.forAll
      others <- elements.forAll
    yield
      val nested = NoFacts.application(
        NoFacts.application(sumTerm, filteredList(others)),
        NoFacts.parallel(foundCall(numbers, wanted), criterion(true))
      )
      val result = listBlocks.compiled(listBlocks.blocks(nested), DebugAttributes.Omitted, StopSignal.completedWith(stopped))
      Result.assert(result.fold(_.contains("has no static method a block can call"), _ => false)).log(s"the compilation gave $result")
  }

  stoppableProperty("the narrow blocks without lists compile no call of the native") { stopped =>
    for
      numbers <- elements.forAll
      wanted <- value.forAll
    yield
      val withoutLists = gezi.narrowblocks.NarrowBlockCompilation(index, natives, gezi.weakhead.ReadingConfiguration.withoutFacts)
      val program = foundCall(numbers, wanted)
      Result.all(
        List(
          Result.assert(withoutLists.staticMethod(NativeName.Function("no_answer_found"), 2).isEmpty).log("a static method is offered"),
          Result
            .assert(withoutLists.compiled(withoutLists.blocks(program), DebugAttributes.Omitted, StopSignal.completedWith(stopped)).isLeft)
            .log("a block was compiled")
        )
      )
  }
