package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.SeededSnapshots
import gezi.ir.Instruction
import gezi.ir.Reachability
import snapshot4s.generated.snapshotConfig

/** The respellings of generated evaluator instructions
  * (`HoasGenerators.evaluatorInstruction`) with the operations each took
  * (`Respelling.respelledCounted`): each input by its hash and its size as a
  * graph, each output by its hash, its size as a graph and the operations.
  * Recorded on 2026-11-12 from the respelling that agreed with the tree path
  * it replaced (`thunkInstruction` of `namedInstructionTerm`, 300 generated
  * inputs, the law of commit 5754c415d). Its purpose is to catch a change of
  * a respelling, which shows as a changed output hash, and a respelling whose
  * work grows with the term written out rather than with the graph, which
  * shows as operations far above the input's size.
  */
class RespellingSnapshotTest extends gezi.generatedinputs.FailFastSuite with SeededSnapshots:

  private val inputs: Gen[Instruction] =
    Gen.int(Range.linear(1, 8)).flatMap(HoasGenerators.evaluatorInstruction)

  private def described(instruction: Instruction): String =
    s"instruction ${instruction.hashCode.toHexString}, ${Reachability.instructionsUnder(Vector(instruction)).size} instructions"

  test("the respellings of generated evaluator instructions and their operations") {
    assertSeededSnapshot(inputs, 20261112L, 40, "respelling/evaluator_instructions.txt")(
      described,
      identity[String]
    )(instruction =>
      val Counted(respelled, operations) = Respelling.respelledCounted(instruction, Set.empty)
      s"${described(respelled)}, $operations operations"
    )
  }
