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

/** The law of the instance table's checkpoint strategies
  * (`InstanceCheckpoints`): on a random closed term with choices and
  * parallels, the JIT with the table under `EveryStepsCheckpoints` at a
  * generated interval reads the normal forms the default policy
  * (`ProfitableCheckpoints`) reads, wherever both finish. Whether a policy
  * finishes within a limit is not part of the law: a lookup-only miss runs
  * the instance again, so a policy may spend many more steps. Its purpose is to catch a policy that changes answers, not only steps and
  * memory: a lookup-only miss that records a partial reading, or a hit taken
  * from an entry recorded under another key.
  */
class InstanceCheckpointsLawTest extends GeneratedProperties:

  private def configuration(checkpoints: InstanceCheckpoints): JitConfiguration =
    JitConfiguration(
      noFacts,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceCheckpoints = checkpoints
    )

  private val limit: Long = 200000

  property("a checkpoint policy reads the default policy's normal forms wherever both finish") {
    for
      seed <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      size <- Gen.int(Range.linear(4, 24)).forAll
      interval <- Gen.long(Range.linear(0L, 400L)).forAll
    yield
      val term = EvaluatorTesting.draws(1, seed)(random => randomLatticeApplication(size, random)) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one term drawn, not ${other.size}")
      val value = valuesOf(Vector(instructionOf(term))) match
        case Vector(only) => only
        case other        => throw IllegalStateException(s"one value per term, not ${other.size}")
      def read(checkpoints: InstanceCheckpoints) =
        NativesTesting.normalFormsSpent(Mode.Jit(Jit(configuration(checkpoints))), value, limit, NoJitState)
      val default = read(ProfitableCheckpoints)
      val policy = read(EveryStepsCheckpoints(interval))
      (default.outcome, policy.outcome) match
        case (Bounded.Finished(expected), Bounded.Finished(found)) =>
          Result.diff(found, expected)(_ == _).log(s"interval $interval, term $term")
        case _ => Result.success
  }
