package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Instruction
import gezi.ir.Reachability

/** The laws of respelling a closed instruction on the IR
  * (`Respelling.respelled`). The inputs are the evaluator's instructions
  * (`HoasGenerators.evaluatorInstruction`), the names a subset of the
  * instructions under them.
  */
class RespellingLawTest extends GeneratedProperties:

  /** A subset of the instructions under the root. */
  private def names(root: Instruction): Gen[Set[Instruction]] =
    val under = Reachability.instructionsUnder(Vector(root)).toVector.sortBy(_.hashCode)
    Gen.boolean.list(Range.singleton(under.size)).map(chosen => under.zip(chosen).collect { case (instruction, true) => instruction }.toSet)

  private def nameSets(root: Instruction): Gen[Set[Instruction]] =
    Gen.frequency1(1 -> Gen.constant(Set.empty[Instruction]), 1 -> names(root))

  /** An instruction the front end spells is its own respelling: catches a
    * respelling that renumbers the slots of a body, shares two closed parts
    * the conversion keeps apart or keeps apart two it shares, or joins or
    * folds a chain the conversion does not.
    */
  property("the front end's instruction is its own respelling") {
    for
      root <- HoasGenerators.instruction.forAll
      kept <- nameSets(root).forAll
    yield Result.diff(Respelling.respelled(root, kept), root)(_ == _)
  }

  /** A respelling is its own respelling: catches a respelling of the
    * evaluator's instructions (a thunk with filled holes, whose code reads
    * closed parts the conversion would hoist) that is not the front end's
    * spelling of its term.
    */
  property("a respelling is its own respelling", _.copy(testLimit = 300)) {
    for
      size <- Gen.int(Range.linear(1, 8)).forAll
      root <- HoasGenerators.evaluatorInstruction(size).forAll
      kept <- nameSets(root).forAll
    yield
      val respelled = Respelling.respelled(root, kept)
      Result.diff(Respelling.respelled(respelled, kept), respelled)(_ == _)
  }
