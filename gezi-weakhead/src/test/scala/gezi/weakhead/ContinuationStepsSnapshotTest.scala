package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import gezi.frontend.Term
import snapshot4s.generated.snapshotConfig

/** The evaluator steps and tables of `tabling(weak_head)` on a diamond of calls
  * in continuation passing style, under each `ContinuationReading`:
  * `d_0 = λk. k (λz. z)`, and `d_i = λk. d_(i-1) (λa. d_(i-1) (λb. k a))`, each
  * `d_(i-1)` a closed term, so that `d_i` calls `d_0` along 2^i paths. Each
  * depth is read from a fresh state, applied to `λx. x`.
  *
  * Under `Substituted` each call of `d_(i-1)` takes a continuation of its own,
  * a new key, so the work before the continuation is done once per path; under
  * `Packed` the calls share the table of `d_(i-1)` applied to the pack.
  *
  * Its purpose: the snapshot's diff shows any change of what the two readings
  * share, as the counts move between the paths and the depths. The depths are
  * the input, a count of calls, as `jmh-pipeline`'s counts take their copies.
  */
class ContinuationStepsSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  given NoFacts.type = NoFacts

  /** The steps a read may take: far above what the deepest read takes. */
  private val limit: Long = 2000000

  /** The deepest diamond. */
  private val deepest: Int = 10

  /** `d_0` to `d_deepest`, each a closed instruction. */
  private val diamonds: Vector[Configured[NoFacts.type]] =
    (1 to deepest).foldLeft(
      Vector(
        EvaluatorTesting.instructionOf(
          Term.λ(continuation => continuation(Term.λ(z => z)))
        )
      )
    ) { (made, _) =>
      val below = Term.closed(made.last)
      made :+ EvaluatorTesting.instructionOf(
        Term.λ(continuation =>
          below(Term.λ(first => below(Term.λ(_ => continuation(first)))))
        )
      )
    }

  /** The steps and tables of reading the diamond applied to `λx. x`. */
  private def counts(
      diamond: Configured[NoFacts.type],
      continuations: ContinuationReading
  ): (Long, Int, Int) =
    val term =
      EvaluatorTesting.instructionOf(Term.closed(diamond)(Term.λ(x => x)))
    val start = ReadingState
      .knowingTop(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)
      .copy(continuations = continuations)
    WeakHead
      .heads(Mode.TablingWeakHead, gezi.ir.Value.of(term))
      .collected
      .result(start) match
      case Computed.Done(found, after) =>
        (
          after.budget.spent,
          after.tables.complete.size + after.tables.open.size,
          found.size
        )
      case Computed.Stopped(after) =>
        throw AssertionError(
          s"the read of a diamond stopped: ${after.exhausted}"
        )

  test("steps and tables of a diamond of calls, by continuation reading") {
    val rows = diamonds.zipWithIndex.flatMap((diamond, depth) =>
      ContinuationReading.values.toVector.map(reading =>
        val (steps, tables, sets) = counts(diamond, reading)
        s"$depth\t$reading\t$steps\t$tables\t$sets"
      )
    )
    assertFileSnapshot(
      rows
        .mkString("depth\treading\tsteps\ttables\tparallel sets\n", "\n", "\n"),
      "continuation_reading/diamond_counts.tsv"
    )
  }
