package gezi.frontend

import gezi.ir.Code
import gezi.ir.Configured
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import gezi.ir

/** The port of `gezi/tests/thunk_instructions.plt`: the thunk
  * conversion of the front end:
  * a chain of abstractions is one thunk layer whose binders and maximal
  * closed subterms are slots alike, a closure is the thunk with holes,
  * abstractions of one shape share a code, and the readback is the inverse.
  * A parallel is a layer of two sides, converted, read back and interned
  * like an application. Where the Prolog tests compare hash_consing handles,
  * these compare interned instructions.
  */
class ThunkInstructionsTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  import DeBruijnTerm.*
  import Defunctionalization.instructionTerm

  private def thunkInstruction(term: DeBruijnTermOf[NoFactsTerm]): NoFactsTerm =
    Defunctionalization.thunkInstruction[NoFacts.type](term)

  private def thunkOf(code: Code, holes: Vector[Hole], fillings: Vector[NoFactsTerm]): NoFactsTerm =
    NoFacts.thunk(code, NonEmptyHoles.of(holes).getOrElse(throw IllegalArgumentException("a thunk of no hole")), fillings)

  private def assertSameInstruction(obtained: NoFactsTerm, expected: NoFactsTerm): Unit =
    assert(Configured.same(obtained, expected), s"the instructions differ: $obtained and $expected")

  private val zero: DeBruijnTerm = Lambda(Lambda(Variable(1)))
  private val one: DeBruijnTerm = Lambda(Lambda(Apply(Variable(0), zero)))
  private val two: DeBruijnTerm = Lambda(Lambda(Apply(Variable(0), one)))

  /** Zero's instruction: an instruction standing for a library name; a reference
    * `Constant(instruction)` converts to the bare instruction.
    */
  private val name = thunkInstruction(zero)

  private def slot(index: Int): Code = Code.Slot(index)

  test("aChainIsOneThunkWithAHolePerBinder") {
    assertSameInstruction(
      thunkInstruction(zero),
      thunkOf(slot(0), Vector(Hole.Bound(0), Hole.Ignored), Vector.empty)
    )
    assertSameInstruction(
      thunkInstruction(Lambda(Variable(0))),
      thunkOf(slot(0), Vector(Hole.Bound(0)), Vector.empty)
    )
    assertSameInstruction(
      thunkInstruction(Lambda(Apply(Variable(0), Variable(0)))),
      thunkOf(
        Code.Apply(slot(0), slot(0)),
        Vector(Hole.Bound(0)),
        Vector.empty
      )
    )
  }

  test("aClosedSubtermIsASlotFilledOutsideTheThunk") {
    assertSameInstruction(
      thunkInstruction(one),
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Ignored, Hole.Bound(0)),
        Vector(thunkInstruction(zero))
      )
    )
    assertSameInstruction(
      thunkInstruction(Lambda(Apply(Variable(0), Constant(name)))),
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Bound(0)),
        Vector(name)
      )
    )
  }

  test("numeralsShareTheThunkAndTheHolesOfTheSuccessorShape") {
    (thunkInstruction(one).layer, thunkInstruction(two).layer) match
      case (
            ir.Thunk(code, holes, Vector(zeroInstruction)),
            ir.Thunk(code2, holes2, Vector(oneInstruction))
          ) =>
        assertEquals(code, code2)
        assertEquals(holes, holes2)
        assertSameInstruction(zeroInstruction, thunkInstruction(zero))
        assertSameInstruction(oneInstruction, thunkInstruction(one))
      case other => fail(s"the numerals convert to $other")
  }

  // `\x. f x` with f closed and `\f. f a` with a closed share the code
  // `apply(slot(0), slot(1))` with different holes.
  test("oneThunkTwoHoles") {
    assertSameInstruction(
      thunkInstruction(Lambda(Apply(Constant(name), Variable(0)))),
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Bound(1)),
        Vector(name)
      )
    )
    assertSameInstruction(
      thunkInstruction(Lambda(Apply(Variable(0), Constant(name)))),
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Bound(0)),
        Vector(name)
      )
    )
  }

  test("anInnerChainReadsTheEnclosingSlots") {
    assertSameInstruction(
      thunkInstruction(
        Lambda(Apply(Constant(name), Lambda(Apply(Variable(1), Variable(0)))))
      ),
      thunkOf(
        Code.Apply(
          slot(0),
          Code.Thunk(
            Code.Apply(slot(0), slot(1)),
            Vector(Hole.Bound(1)),
            Vector(slot(1))
          )
        ),
        Vector(Hole.Bound(1)),
        Vector(name)
      )
    )
    assertSameInstruction(
      thunkInstruction(Lambda(Lambda(Apply(Variable(1), zero)))),
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Bound(0), Hole.Ignored),
        Vector(thunkInstruction(zero))
      )
    )
  }

  test("theReadbackInvertsTheConversion") {
    Vector[DeBruijnTerm](
      zero,
      two,
      Lambda(Variable(0)),
      Lambda(Apply(Variable(0), Variable(0))),
      Lambda(Lambda(Apply(Variable(1), zero))),
      Lambda(Apply(zero, Lambda(Apply(Variable(1), Variable(0))))),
      Lambda(
        Lambda(
          Lambda(
            Apply(Apply(Variable(2), Variable(0)), Lambda(Variable(2)))
          )
        )
      ),
      Apply(
        zero,
        Lambda(Apply(Variable(0), Lambda(Apply(Variable(1), Variable(0)))))
      ),
      Choice(zero, two)
    ).foreach(term => assertEquals(instructionTerm(thunkInstruction(term)), term))
  }

  test("anOpenTermIsAnError") {
    val open = Lambda(Variable(1))
    assertEquals(
      intercept[LambdaError](thunkInstruction(open)).reason,
      LambdaErrorReason.NotClosed(open)
    )
  }

  test("aNegativeIndexIsAnError") {
    val negative = Lambda(Variable(-1))
    assertEquals(
      intercept[LambdaError](thunkInstruction(negative)).reason,
      LambdaErrorReason.NotClosed(negative)
    )
  }

  test("theInstructionOfALiteralIsTheInstructionOfItsThunkIr") {
    val instruction = thunkInstruction(zero)
    val instruction2 = thunkInstruction(zero)
    assert(Configured.same(instruction, instruction2), "converting one literal twice gives one object")
  }

  // A term that refers to a name by instruction and the same term with the name's
  // literal in its place are one instruction: the reference is the referenced
  // layer.
  test("aReferenceAndTheLiteralItNamesAreOneInstruction") {
    val instruction = thunkInstruction(Lambda(Apply(Variable(0), Constant(name))))
    val instruction2 = thunkInstruction(Lambda(Apply(Variable(0), zero)))
    assertSameInstruction(instruction, instruction2)
  }

  // `\x. \y. x ∥ y`: the parallel of the two binders' slots in the body.
  test("aParallelOfBindersIsAParallelOverSlots") {
    val term = Lambda(Lambda(Parallel(Variable(1), Variable(0))))
    val instruction = thunkInstruction(term)
    assertSameInstruction(
      instruction,
      thunkOf(
        Code.Parallel(slot(0), slot(1)),
        Vector(Hole.Bound(0), Hole.Bound(1)),
        Vector.empty
      )
    )
    assertEquals(instructionTerm(instruction), term)
  }

  // `\f. f ((\a. a) ∥ (\b. b))`: a closed parallel is a maximal closed
  // subterm, a filling of the chain, converted outside the thunk.
  test("aClosedParallelIsAFilling") {
    val term = Lambda(Apply(Variable(0), Parallel(Lambda(Variable(0)), Lambda(Variable(0)))))
    val instruction = thunkInstruction(term)
    val identity = thunkOf(slot(0), Vector(Hole.Bound(0)), Vector.empty)
    assertSameInstruction(
      instruction,
      thunkOf(
        Code.Apply(slot(0), slot(1)),
        Vector(Hole.Bound(0)),
        Vector(NoFacts.parallel(identity, identity))
      )
    )
    assertEquals(instructionTerm(instruction), term)
  }

  test("aParallelIsInternedOverTheInstructionsOfItsSides") {
    // `(λa. a) ∥ (λb. b)`.
    val closedInstruction = thunkInstruction(Parallel(Lambda(Variable(0)), Lambda(Variable(0))))
    closedInstruction.layer match
      case ir.Parallel(left, right) =>
        assert(Configured.same(left, right), "the two sides are one canonical instruction")
      case other => fail(s"the layer of the closed parallel is $other")
  }
