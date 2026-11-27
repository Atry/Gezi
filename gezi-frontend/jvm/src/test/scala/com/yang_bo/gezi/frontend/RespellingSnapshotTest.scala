package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.SeededSnapshots
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.Reachability
import snapshot4s.generated.snapshotConfig

/** The respellings of generated evaluator instructions
  * (`HoasGenerators.evaluatorInstruction`) with the operations each took
  * (`Respelling.respelledCounted`): each input by its exchange line and its
  * size as a graph, each output by its exchange line, its size as a graph and
  * the operations (a hash code, an identity, differs from run to run). Recorded
  * on 2026-11-12 from the respelling that agreed with the tree path it replaced
  * (`thunkInstruction` of `namedInstructionTerm`, 300 generated inputs, the law
  * of commit 5754c415d). Its purpose is to catch a change of a respelling,
  * which shows as a changed output line, and a respelling whose work grows with
  * the term written out rather than with the graph, which shows as operations
  * far above the input's size.
  */
class RespellingSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with SeededSnapshots:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private val inputs: Gen[Configured[NoFacts.type]] =
    Gen.int(Range.linear(1, 8)).flatMap(HoasGenerators.evaluatorInstruction)

  private def described(instruction: Configured[NoFacts.type]): String =
    s"instruction ${ExchangeText.line(instruction)}, ${Reachability.instructionsUnder(Vector(instruction)).size} instructions"

  test(
    "the respellings of generated evaluator instructions and their operations"
  ) {
    assertSeededSnapshot(
      inputs,
      20261112L,
      40,
      "respelling/evaluator_instructions.txt"
    )(
      described,
      identity[String]
    )(instruction =>
      val Counted(respelled, operations) =
        Respelling.respelledCounted(instruction, Set.empty)
      s"${described(respelled)}, $operations operations"
    )
  }
