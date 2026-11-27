package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.*
import gezi.weakhead.Budget
import gezi.weakhead.Computed
import gezi.weakhead.EvaluatorTesting
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState
import gezi.ir.Value

/** The law of a JIT reading under a ceiling (`Budget.ceiling`, the bound a
  * part of a reading is tried under, `NormalForms`' shares of a parallel
  * set's heads): over a generated closed term with choices and parallels,
  * read for its normal forms with the instance table on, at every ceiling c
  * from 0 to the steps the reading spends with none, the reading ends, done
  * or stopped, having spent at most c. Derived from the budget's contract:
  * every charge checks the bound, `min(limit, ceiling)`, before it spends,
  * and a lookahead is given at most the bound's remainder. The reading runs
  * under the lazy lookahead and under lookaheads within 1, 3 and 10 steps,
  * and the sweep meets every point on its path at which a charge of several
  * steps (a table's lookup by its fillings, a replay by its heads) or a
  * lookahead would cross a ceiling. Its purpose is to catch such a charge or
  * lookahead that reads the limit and not the ceiling, which lets an attempt
  * within a share spend past it. Not reached here: a read verification (a
  * reuse across versions), a decode point's hit (facts with
  * representations), and a group block's entry, whose laws are the group
  * blocks'.
  */
class JitCeilingLawTest extends GeneratedProperties:

  /** The configurations read: the lazy lookahead, and lookaheads within a few steps. */
  private val encoding = noFactsEncoding

  private given encoding.type = encoding

  private val configurations: Vector[JitConfiguration[encoding.type]] =
    (InstanceLookahead.Lazy +: Vector(1L, 3L, 10L).map(InstanceLookahead.WithinSteps(_))).map(lookahead =>
      JitConfiguration[encoding.type](
        encoding,
        JitConfiguration.defaultBudget,
        PredicatePerCode,
        ClosureBackend,
        DispatchMode.NoDispatch,
        instanceTable = true,
        instanceLookahead = lookahead,
        storageAccess = gezi.ir.StorageAccess.granted()
      )
    )

  /** The steps a reading may take: the generated terms are small. */
  private val limit: Long = 2000

  private val values: Gen[Value[encoding.type]] =
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      size <- Gen.int(Range.linear(4, 12))
    yield
      val term = EvaluatorTesting.draws(1, seed)(random => randomLatticeApplication(size, random)) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one term drawn, not ${other.size}")
      valuesOf(Vector(instructionOf(term))) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one value per term, not ${other.size}")

  property("a JIT reading under a ceiling spends at most the ceiling") {
    for value <- values.forAll
    yield Result.all(configurations.toList.map(configuration =>
      def spent(ceiling: Long): Long =
        NormalForms.normalForms(Mode.Jit, value).result(ReadingState.fresh(limit, configuration.readingConfigurationOf(Jit(configuration))).copy(budget = Budget(0, limit, ceiling = ceiling))) match
          case Computed.Done(_, after)  => after.budget.spent
          case Computed.Stopped(after) => after.budget.spent
      val uncapped = spent(Long.MaxValue)
      Result.all((0L to uncapped).toList.map(ceiling =>
        val found = spent(ceiling)
        Result.assert(found <= ceiling).log(s"${configuration.instanceLookahead}, ceiling $ceiling: spent $found")
      ))
    ))
  }
