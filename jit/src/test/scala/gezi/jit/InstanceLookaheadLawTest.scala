package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState

/** The law of the instance table's lookahead (`InstanceLookahead`): on a
  * random closed term with choices and parallels, the JIT with the table
  * pulling a missed instance's rest within a generated number of steps reads
  * the normal forms the lazy table reads, wherever both finish. Its purpose
  * is to catch a lookahead that changes answers rather than steps and
  * memory: a head of the pulled rest dropped or given twice, a state kept
  * from a pull that ran out of its steps (a table left marked as stopped, a
  * partial reading recorded), or the reading's own limit left lowered after
  * the pull. At least 30% of the draws finish under the lookahead with a
  * table entry, so that the law compares readings the lookahead acted on.
  */
class InstanceLookaheadLawTest extends GeneratedProperties:

  private def configuration(lookahead: InstanceLookahead): JitConfiguration =
    JitConfiguration(
      noFacts,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceLookahead = lookahead
    )

  /** The steps of each reading. The draws that finish take 9 to 87 steps
    * (40 draws of size 20, measured 2026-11-22), while a draw that does not
    * finish spends the whole limit in each mode: at 200,000 steps such a
    * draw took 0.3 to 2.3 s a reading under a load of 17, which ran the
    * suite's deadline out.
    */
  private val limit: Long = 20000

  /** A drawn term, a lookahead bound, and the readings of the term under the
    * lazy table and under the lookahead.
    */
  private val readings =
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      size <- Gen.int(Range.linear(4, 24))
      steps <- Gen.long(Range.linear(1L, 64L))
    yield
      val term = EvaluatorTesting.draws(1, seed)(random => randomLatticeApplication(size, random)) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one term drawn, not ${other.size}")
      val value = valuesOf(Vector(instructionOf(term))) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one value per term, not ${other.size}")
      def read(lookahead: InstanceLookahead) =
        NativesTesting.normalFormsSpent(Mode.Jit(Jit(configuration(lookahead))), value, limit, NoJitState)
      (term, steps, read(InstanceLookahead.Lazy), read(InstanceLookahead.WithinSteps(steps)))

  /** Whether the reading finished with an entry in the table. */
  private def finishedWithAnEntry(read: Spent[?]): Boolean =
    (read.outcome, read.jitState) match
      case (Bounded.Finished(_), run: JitRunState) => run.tableCosts.values.exists(_.entries > 0)
      case _                                      => false

  property("the lookahead reads the lazy table's normal forms wherever both finish") {
    for
      drawn <- readings.forAll
        .cover(30, "a reading under the lookahead that finished with a table entry", (_, _, _, ahead) => finishedWithAnEntry(ahead))
    yield
      val (term, steps, lazily, ahead) = drawn
      (lazily.outcome, ahead.outcome) match
        case (Bounded.Finished(expected), Bounded.Finished(found)) =>
          Result.diff(found, expected)(_ == _).log(s"within $steps steps, term $term")
        case _ => Result.success
  }
