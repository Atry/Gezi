package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.jit.JitTesting.*
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.EvaluatorTesting
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState

/** The law of the instance table's lookahead (`InstanceLookahead`): on a random
  * closed term with choices and parallels, the JIT with the table pulling a
  * missed instance's rest within a generated number of steps reads the normal
  * forms the lazy table reads, wherever both finish. Its purpose is to catch a
  * lookahead that changes answers rather than steps and memory: a head of the
  * pulled rest dropped or given twice, a state kept from a pull that ran out of
  * its steps (a table left marked as stopped, a partial reading recorded), or
  * the reading's own limit left lowered after the pull. Every iteration checks
  * the law also on `(λx. x x) (λy. y)`, whose β step reads the body `x x` as an
  * instance of its code under the filling `λy. y`, missed by the empty table
  * and pulled by the lookahead, whose heads end at `λy. y` with the table
  * complete; that the lookahead's reading finished with a table entry is
  * asserted, so that the law always compares a reading the lookahead acted on.
  */
class InstanceLookaheadLawTest extends GeneratedProperties:

  private val encoding = noFactsEncoding

  private given encoding.type = encoding

  private def configuration(
      lookahead: InstanceLookahead
  ): JitConfiguration[encoding.type] =
    JitConfiguration[encoding.type](
      encoding,
      JitConfiguration.defaultBudget,
      PredicatePerCode,
      ClosureBackend,
      DispatchMode.NoDispatch,
      instanceTable = true,
      instanceLookahead = lookahead,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )

  /** The steps of each reading. The draws that finish take 9 to 87 steps (40
    * draws of size 20, measured 2026-11-22), while a draw that does not finish
    * spends the whole limit in each mode: at 200,000 steps such a draw took 0.3
    * to 2.3 s a reading under a load of 17, which ran the suite's deadline out.
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
      val term = EvaluatorTesting.draws(1, seed)(random =>
        randomLatticeApplication(size, random)
      ) match
        case Vector(only) => only
        case other        =>
          throw IllegalStateException(s"one term drawn, not ${other.size}")
      (
        term,
        steps,
        read(term, InstanceLookahead.Lazy),
        read(term, InstanceLookahead.WithinSteps(steps))
      )

  /** The term's reading under the table with the lookahead. */
  private def read(
      term: DeBruijnTerm,
      lookahead: InstanceLookahead
  ): Spent[encoding.type, Vector[Configured[encoding.type]]] =
    val value = valuesOf(Vector(instructionOf(term))) match
      case Vector(only) => only
      case other        =>
        throw IllegalStateException(s"one value per term, not ${other.size}")
    NativesTesting.normalFormsSpent(
      Jit(configuration(lookahead)),
      value,
      limit,
      NoJitState
    )

  /** `(λx. x x) (λy. y)`: the instance of `x x` under `λy. y` is missed. */
  private val selfApplied: DeBruijnTerm =
    DeBruijnTerm.Apply(
      DeBruijnTerm.Lambda(
        DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(0))
      ),
      DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))
    )

  /** The law on the two readings of one term. */
  private def agreed(
      term: DeBruijnTerm,
      steps: Long,
      lazily: Spent[encoding.type, Vector[Configured[encoding.type]]],
      ahead: Spent[encoding.type, Vector[Configured[encoding.type]]]
  ): Result =
    (lazily.outcome, ahead.outcome) match
      case (Bounded.Finished(expected), Bounded.Finished(found)) =>
        Result
          .assert(sameTerms(found, expected))
          .log(s"within $steps steps, term $term")
      case _ => Result.success

  /** Whether the reading finished with an entry in the table. */
  private def finishedWithAnEntry(read: Spent[encoding.type, ?]): Boolean =
    (read.outcome, read.jitState) match
      case (Bounded.Finished(_), run: JitRunState[?]) =>
        run.tableCosts.values.exists(_.entries > 0)
      case _ => false

  property(
    "the lookahead reads the lazy table's normal forms wherever both finish"
  ) {
    for (term, steps, lazily, ahead) <- readings.forAll
    yield
      val selfAhead = read(selfApplied, InstanceLookahead.WithinSteps(steps))
      agreed(term, steps, lazily, ahead)
        .and(
          agreed(
            selfApplied,
            steps,
            read(selfApplied, InstanceLookahead.Lazy),
            selfAhead
          )
        )
        .and(
          Result
            .assert(finishedWithAnEntry(selfAhead))
            .log(
              s"(λx. x x) (λy. y) within $steps steps did not finish with a table entry: ${selfAhead.outcome}"
            )
        )
  }
