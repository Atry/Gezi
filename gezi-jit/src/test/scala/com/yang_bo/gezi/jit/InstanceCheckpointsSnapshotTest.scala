package com.yang_bo.gezi.jit

import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.jit.JitTesting.*
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.EvaluatorTesting
import com.yang_bo.gezi.weakhead.JitState
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState
import snapshot4s.generated.snapshotConfig

/** The instance table under each checkpoint policy (`InstanceCheckpoints`) over
  * 40 random closed terms with choices and parallels, from the fixed seed
  * 20261103, read one after another with the table kept: for each policy and
  * term, the outcome and steps of its normal-form reading and the table's
  * entries and hits so far. Its purpose is to record what a policy changes, the
  * steps and the entries the table holds, which the law test does not see while
  * the answers stay the same, and to catch a change in either under the
  * default.
  */
class InstanceCheckpointsSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  private val encoding = noFactsEncoding

  private given encoding.type = encoding

  private val terms =
    EvaluatorTesting.draws(40, 20261103L)(random =>
      randomLatticeApplication(16, random)
    )

  private val policies: Vector[(String, InstanceCheckpoints)] = Vector(
    "default" -> ProfitableCheckpoints,
    "every 0 steps" -> EveryStepsCheckpoints(0),
    "every 50 steps" -> EveryStepsCheckpoints(50),
    "every 500 steps" -> EveryStepsCheckpoints(500)
  )

  private def lines(checkpoints: InstanceCheckpoints): Vector[String] =
    val jit = Jit(
      JitConfiguration[encoding.type](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.NoDispatch,
        instanceTable = true,
        instanceCheckpoints = checkpoints,
        storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
      )
    )
    terms.zipWithIndex
      .foldLeft((Vector.empty[String], NoJitState: JitState[encoding.type])) {
        case ((written, state), (term, index)) =>
          val value = valuesOf(Vector(instructionOf(term))) match
            case Vector(only) => only
            case other        => fail(s"one value per term, not ${other.size}")
          val read = NativesTesting.normalFormsSpent(jit, value, 200000, state)
          val outcome = read.outcome match
            case Bounded.Finished(normalForms) =>
              s"finished(${normalForms.size})"
            case other => other.productPrefix
          val (costs, held) = read.jitState match
            case run: JitRunState[?] =>
              (
                run.tableCosts.values.toVector,
                run.instanceTables.complete.size + run.olderInstances.size
              )
            case NoJitState => (Vector.empty, 0)
            case other      => fail(s"the JIT left another state: $other")
          val line = Vector(
            index.toString,
            Lambdalattice.textWithLiterals(term, Map.empty),
            outcome,
            s"steps=${read.steps}",
            s"entries=${costs.map(_.entries).sum}",
            s"hits=${costs.map(_.hits).sum}",
            s"held=$held"
          ).mkString("\t")
          (written :+ line, read.jitState)
      }
      ._1

  test("theTableUnderEachCheckpointPolicyOnRandomTerms") {
    assertFileSnapshot(
      policies
        .flatMap((name, checkpoints) => s"# $name" +: lines(checkpoints))
        .mkString("\n") + "\n",
      "instance-checkpoints/random-lattice-terms.txt"
    )
  }
