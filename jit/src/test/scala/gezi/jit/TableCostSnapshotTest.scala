package gezi.jit

import gezi.frontend.Lambdalattice
import gezi.jit.JitTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.JitState
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import snapshot4s.generated.snapshotConfig

/** The instance table's accounting (`TableCost`, `JitRunState.tableCosts`) over
  * 40 random closed terms with choices and parallels, from the fixed seed
  * 20261102, read one after another under the table with its default trial and
  * with a trial of four entries: for each term, its spelling, the outcome and
  * steps of its normal-form reading, and the table's entries, hits, entry
  * steps, lookup steps and codes cut off so far. Its purpose is to catch a
  * regression in the accounting (a lookup charged other steps, a hit or an
  * entry not counted, a cutoff at another point) and a change in the steps a
  * tabled reading takes, which the law tests do not see while the answers stay
  * the same.
  */
class TableCostSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  private val terms =
    EvaluatorTesting.draws(40, 20261102L)(random =>
      randomLatticeApplication(16, random)
    )

  private def configuration(trial: Long): JitConfiguration[encoding.type] =
    JitConfiguration[encoding.type](
      encoding,
      10000,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceTableTrial = trial,
      storageAccess = gezi.ir.StorageAccess.granted()
    )

  /** One line a term, the table kept from one term to the next. */
  private def lines(trial: Long): Vector[String] =
    val jit = Jit(configuration(trial))
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
          val costs = read.jitState match
            case run: JitRunState[?] => run.tableCosts.values.toVector
            case NoJitState          => Vector.empty
            case other => fail(s"the JIT left another state: $other")
          val line = Vector(
            index.toString,
            Lambdalattice.textWithLiterals(term, Map.empty),
            outcome,
            s"steps=${read.steps}",
            s"entries=${costs.map(_.entries).sum}",
            s"hits=${costs.map(_.hits).sum}",
            s"entrySteps=${costs.map(_.entrySteps).sum}",
            s"lookupSteps=${costs.map(_.lookupSteps).sum}",
            s"cutOff=${costs.count(_.unprofitable(trial))}"
          ).mkString("\t")
          (written :+ line, read.jitState)
      }
      ._1

  test("theTableCostsOfRandomTermsUnderTheDefaultTrialAndAnEarlyCutoff") {
    assertFileSnapshot(
      (Vector(s"# trial ${TableCost.trial}") ++ lines(
        TableCost.trial
      ) ++ Vector("# trial 4") ++ lines(4)).mkString("\n") + "\n",
      "table-costs/random-lattice-terms.txt"
    )
  }
