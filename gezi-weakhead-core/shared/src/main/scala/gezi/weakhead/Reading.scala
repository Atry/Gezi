package gezi.weakhead

import gezi.ir.{NativeSpecializer, Value}

/** How a reading ended (reading.pl's outcomes). */
enum ReadingOutcome[C <: NativeSpecializer & Singleton]:

  /** The evaluation finished: its distinct parallel sets, their heads plain
    * values, in the order first found, reduced by `WeakHead.bottomAbsorbed`;
    * none when it has none (under tabling(weak_head), a decision that the
    * term has no head; under weak_head, a finite failure).
    */
  case Heads(heads: Vector[ParallelSet[C]])

  /** The evaluation did not finish within its budget of steps (the Prolog
    * reading's `inference_limit`).
    */
  case StepLimit()

  /** A resource ran out first (the Prolog reading's `exhausted(Resource)`).
    */
  case Exhausted(resource: Resource)

/** How the witness reading of one root ended. */
enum WitnessOutcome:

  /** Some head of the root reads out as the witness. */
  case Found

  /** The evaluation finished and no head reads out as the witness. */
  case NotFound

  /** The reading did not finish within its budget of steps. */
  case StepLimit

  /** A resource ran out first. */
  case Exhausted(resource: Resource)

/** The witness reading of one root of a suite: how it ended and the steps it
  * took.
  */
final case class WitnessReading(outcome: WitnessOutcome, spent: Long)

/** Readings: one evaluation of a closed root, bounded by a budget of
  * evaluator steps. The port of `gezi/prolog/gezi/reading.pl`, the reading
  * harness.
  *
  * A READING runs the evaluator (`WeakHead`, or the JIT under `Mode.Jit`) on
  * a closed root, a value that may hold neutral values, within a budget of
  * steps (`Budget`, the steps as `WeakHead` defines them), never within a
  * time: the count is the same on every run, so a reading repeats exactly.
  * The Prolog reading was bounded by SWI-Prolog's inference count, which
  * Scala does not have. Its outcome
  * `exhausted(Resource)`, a stack or the table space run out first, has one
  * counterpart: the tabled mode's number of tables, bounded by the
  * reading's table limit (`ReadingState.tableLimit`, the counterpart of the
  * table space); the untabled machine bounds no resource but steps, its
  * goals living on the heap.
  *
  * `termReading` takes every parallel set, so its outcome never depends on
  * the order they come in: it depends on the term, the mode and the budget.
  * Each reading of `termReading` starts from no table.
  *
  * The judge's question "does some parallel set read out as the witness" is
  * answered by `witnessReadings`. A parallel set reads out as the witness
  * when every head of it is the witness: L ⊑ w and R ⊑ w give L ∥ R ⊑ w by
  * the λ-lattice laws, so the set of the witness alone does, and so does the
  * empty parallel set, the least term, which is below the witness as it is
  * below every term. Under every mode the first one found that reads out
  * settles it (for tabling(weak_head) too, since its parallel sets come as
  * they are found), the parallel sets coming in the term's own
  * order, so a witness ahead of a branch that does not end is found, behind
  * it the budget runs out.
  *
  * THE SUITE. `witnessReadings` reads the roots of one suite one after
  * another with one set of tables, kept from one root to the next, so
  * that a later reading reuses what an earlier one tabled: a cache kept
  * across test points is closer to a real program, and lets the JIT cache
  * what it compiled.
  * A reading the budget stops leaves its incomplete tables with their
  * answers found and their producers (`Tables.stopped`), where SWI-Prolog
  * discards the incomplete tables of the evaluation its inference limit
  * interrupts: no answer found is ever dropped, and a later reading goes on from there. Unlike the
  * Prolog reading, the first reading of a run spends no steps more than a
  * later one: the count is the evaluator's own.
  */
object Reading:

  /** The reading of the root from no table, within the limit of steps,
    * knowing top (`ReadingState.knowingTop`).
    */
  def termReading[C <: NativeSpecializer & Singleton](
      mode: Mode,
      root: Value[C],
      limit: Long,
      configuration: ReadingConfiguration[C]
  )(using C): ReadingOutcome[C] =
    WeakHead.heads(mode, root).collected.result(ReadingState.knowingTop(limit, configuration)) match
      case Computed.Done(heads, _) =>
        ReadingOutcome.Heads(WeakHead.bottomAbsorbed(heads.distinct))
      case Computed.Stopped(after) =>
        after.exhausted match
          case Some(resource) => ReadingOutcome.Exhausted(resource)
          case None           => ReadingOutcome.StepLimit()

  /** The readings of a suite (the object's comment), for each root in order,
    * each within the limit of steps; the witness is a neutral value with no
    * argument, a value a closed program cannot name. Throws `EvaluationError`
    * with `NotAWitness` for another witness, before any root is read.
    */
  def witnessReadings[C <: NativeSpecializer & Singleton](
      mode: Mode,
      roots: Vector[Value[C]],
      witness: Value[C],
      limit: Long,
      configuration: ReadingConfiguration[C]
  )(using C): Vector[WitnessReading] =
    witnessReadingsFrom(mode, roots, witness, limit, NoJitState, configuration)._1

  /** `witnessReadings` with the suite starting from the JIT state given
    * rather than none, and the JIT state the suite left: the JIT's compiled
    * codes, which a caller reading several suites keeps
    * from one suite to the next, as the Prolog JIT kept its compiled
    * predicates in the process.
    */
  def witnessReadingsFrom[C <: NativeSpecializer & Singleton](
      mode: Mode,
      roots: Vector[Value[C]],
      witness: Value[C],
      limit: Long,
      jitState: JitState[C],
      configuration: ReadingConfiguration[C]
  )(using C): (Vector[WitnessReading], JitState[C]) =
    val witnessHead = witness match
      case NeutralValue(variable, arguments) if arguments.isEmpty => Head.Neutral(variable, arguments)
      case _ => throw EvaluationError(EvaluationErrorReason.NotAWitness(witness.representation))
    val (readings, last) = roots
      .foldLeft((Vector.empty[WitnessReading], ReadingState.knowingTop(limit, configuration).copy(jitState = jitState))) {
        case ((readings, state), root) =>
          val reading = state.nextReading(limit)
          readsOut(mode, root, witnessHead).result(reading) match
            case Computed.Done(found, after) =>
              val outcome = if found then WitnessOutcome.Found else WitnessOutcome.NotFound
              (readings :+ WitnessReading(outcome, after.budget.spent), after)
            case Computed.Stopped(after) =>
              val outcome = after.exhausted match
                case Some(resource) => WitnessOutcome.Exhausted(resource)
                case None           => WitnessOutcome.StepLimit
              (readings :+ WitnessReading(outcome, after.budget.spent), after)
      }
    (readings, last.jitState)

  /** Some parallel set of the term reads out as the witness: the first one
    * found that does settles it, under every mode.
    */
  private def readsOut[C <: NativeSpecializer & Singleton](mode: Mode, term: Value[C], witness: Head[C])(using
      C
  ): Computation[ReadingState[C], Boolean] =
    WeakHead.heads(mode, term).exists(set => Computation.pure(setReadsOut(set, witness)))

  /** Whether every head of the parallel set is the witness. */
  private def setReadsOut[C <: NativeSpecializer & Singleton](set: ParallelSet[C], witness: Head[C]): Boolean =
    set.heads.forall(_ == witness)

  /** The budget of steps that stands for a budget stated in seconds: the
    * problems state their limits in seconds (`limits(Seconds,
    * StackMegabytes, TableMegabytes)`, written when the readings were timed
    * on a clock). A budget of Seconds is Seconds times `stepsPerSecond`.
    * Throws `EvaluationError` with `NotABudget` for a budget that is not
    * positive.
    */
  def budgetSteps(seconds: Double): Long =
    if seconds > 0 then java.lang.Math.round(seconds * stepsPerSecond)
    else throw EvaluationError(EvaluationErrorReason.NotABudget(seconds))

  /** The steps a stated second stands for, rounded down from the rate this
    * evaluator ran at on the machine of the migration, MEASURED 2026-10-31
    * in a forked test JVM (-Xmx256m, JDK 25, the third of three rounds, load
    * average 3.6 from other work): the normal forms of the program of
    * reduction_fibonacci_N at N = 12 read under weak_head, 34,016 steps in 14 ms
    * of thread CPU time, 2.4 million steps a second. Under weak_head Omega
    * runs 21 million steps a second (10,000,000 in 475 ms), a loop with no
    * work in it; under tabling(weak_head) a step costs more, the program of
    * reduction_fibonacci_twenty reading its normal form in 3,319 steps and
    * 1,632 tables (the Prolog reading's number of tables) in 27 to 61 ms, 55
    * to 120 thousand steps a second. The Prolog rate, 30 million inferences
    * a second, was measured the same way on the Prolog weak_head readings of
    * the contest corpus; their port, the module `contest-corpora`, reads them
    * at the rate stated here, which was not measured on them; a
    * reading at the edge of a stated budget is investigated, never passed by
    * raising the rate.
    */
  val stepsPerSecond: Long = 2000000
