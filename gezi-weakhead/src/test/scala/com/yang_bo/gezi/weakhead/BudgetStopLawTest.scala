package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Value
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.hotspot.baselines.BaselineCaches
import com.yang_bo.gezi.standardlibrary.SplitMix

/** The laws of a reading's budget under a fork's stop signal (`Budget.stop`): a
  * reading under the never-stopped signal reads and spends exactly what a
  * reading under a budget of steps alone does, and a reading whose stop is
  * already requested stops within `Budget.stopCheckSteps` steps. Its purpose is
  * to catch a budget that loses its signal (a copy that drops it, so that a
  * losing task of `Forks.joinedFirstSuccess` runs to its limit) and a signal
  * that changes a reading outside any fork; the next reading of a suite
  * (`ReadingState.nextReading`), which rebuilds a budget, keeps its signal; and
  * an executor's call (`ReadingExecutor`) stops under the signal of its own
  * `com.yang_bo.gezi.hotspot.Budget`, a resumption included, while a call cancelled so
  * resumes under a new call's budget to what an uncancelled call reads, so that
  * a cancel neither leaves a reading running nor loses an answer. The inputs
  * are random closed applications of `EvaluatorTesting.randomApplication`, of
  * sizes 2 to 30, under both weak-head modes.
  */
class BudgetStopLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val limit: Long = 20000

  /** A stop requested before the reading starts. */
  private object AlreadyStopped extends StopSignal:
    def stopRequested: Boolean = true

  private val terms =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield EvaluatorTesting.randomApplication(size, SplitMix(seed))._1

  private val modes: Vector[(String, Mode)] = Vector(
    ("weak_head", Mode.WeakHead),
    ("tabling(weak_head)", Mode.TablingWeakHead)
  )

  private def sameRead(
      left: (Option[Vector[Configured[NoFacts.type]]], Long),
      right: (Option[Vector[Configured[NoFacts.type]]], Long)
  ): Boolean =
    left._2 == right._2 && ((left._1, right._1) match
      case (Some(leftForms), Some(rightForms)) =>
        EvaluatorTesting.sameInstructions(leftForms, rightForms)
      case (None, None) => true
      case _            => false)

  /** The reading's normal forms, if it finished, and the steps it spent. */
  private def read(
      mode: Mode,
      value: Value[NoFacts.type],
      budget: Budget
  ): (Option[Vector[Configured[NoFacts.type]]], Long) =
    NormalForms
      .normalForms(mode, value)
      .result(
        ReadingState
          .fresh(limit, com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts)
          .copy(budget = budget)
      ) match
      case Computed.Done(normalForms, after) =>
        (Some(normalForms), after.budget.spent)
      case Computed.Stopped(after) => (None, after.budget.spent)

  modes.foreach((name, mode) =>
    property(
      s"a reading under the never-stopped signal is the reading of its steps alone, under $name"
    ) {
      for term <- terms.forAll
      yield
        val value =
          Value.of(Defunctionalization.thunkInstruction[NoFacts.type](term))
        Result.diff(
          read(mode, value, Budget.stoppedBy(limit, StopSignal.NeverStopped)),
          read(mode, value, Budget.of(limit))
        )(sameRead)
    }

    property(
      s"a reading whose stop is already requested stops within the check interval, under $name"
    ) {
      for term <- terms.forAll
      yield
        val value =
          Value.of(Defunctionalization.thunkInstruction[NoFacts.type](term))
        val (_, wholeSpent) = read(mode, value, Budget.of(limit))
        val (stopped, stoppedSpent) =
          read(mode, value, Budget.stoppedBy(limit, AlreadyStopped))
        Result.all(
          List(
            Result
              .assert(stoppedSpent <= Budget.stopCheckSteps)
              .log(s"stopped at $stoppedSpent"),
            Result
              .assert(stopped.isEmpty || wholeSpent <= stoppedSpent)
              .log(s"finished in $stoppedSpent of $wholeSpent")
          )
        )
    }

    property(
      s"the next reading of a suite keeps a requested stop, under $name"
    ) {
      for term <- terms.forAll
      yield
        val value =
          Value.of(Defunctionalization.thunkInstruction[NoFacts.type](term))
        val next = ReadingState
          .fresh(limit, com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts)
          .copy(budget = Budget.stoppedBy(limit, AlreadyStopped))
          .nextReading(limit)
        val stoppedSpent =
          NormalForms.normalForms(mode, value).result(next) match
            case Computed.Done(_, after) => after.budget.spent
            case Computed.Stopped(after) => after.budget.spent
        Result
          .assert(stoppedSpent <= Budget.stopCheckSteps)
          .log(s"stopped at $stoppedSpent")
    }

    property(
      s"an execution cancelled by its budget's stop resumes to what an uncancelled one reads, under $name"
    ) {
      for term <- terms.forAll
      yield
        val dependencies = ExecutionDependencies(
          BaselineCaches.provider(),
          ExpansionSource.fresh()
        )
        val executor = ReadingExecutor(
          mode,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        )
        val instruction =
          Defunctionalization.thunkInstruction[NoFacts.type](term)
        val (_, _, whole) = executor.executed(
          instruction,
          dependencies,
          hotspot.Budget(limit, countedUnits = false, StopSignal.NeverStopped)
        )
        val (afterCancel, _, cancelled) = executor.executed(
          instruction,
          dependencies,
          hotspot.Budget(limit, countedUnits = false, AlreadyStopped)
        )
        (whole.suspension, cancelled.suspension) match
          case (None, Some(suspension)) =>
            val (_, _, resumed) =
              afterCancel.resumed(
                suspension,
                dependencies,
                hotspot.Budget(
                  limit,
                  countedUnits = false,
                  StopSignal.NeverStopped
                )
              )
            Result.all(
              List(
                Result
                  .assert(cancelled.spent.steps <= Budget.stopCheckSteps)
                  .log(s"cancelled after ${cancelled.spent.steps}"),
                Result.diff(cancelled.found ++ resumed.found, whole.found)(
                  EvaluatorTesting.sameInstructions
                )
              )
            )
          case (None, None) =>
            Result.diff(cancelled.found, whole.found)(
              EvaluatorTesting.sameInstructions
            )
          case _ => Result.success
    }

    property(
      s"an executor's resumption stops under its own budget's stop, under $name"
    ) {
      for term <- terms.forAll
      yield
        val dependencies = ExecutionDependencies(
          BaselineCaches.provider(),
          ExpansionSource.fresh()
        )
        val executor = ReadingExecutor(
          mode,
          com.yang_bo.gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        )
        val (_, _, first) = executor.executed(
          Defunctionalization.thunkInstruction[NoFacts.type](term),
          dependencies,
          hotspot.Budget(1, countedUnits = false, StopSignal.NeverStopped)
        )
        first.suspension match
          case None             => Result.success
          case Some(suspension) =>
            val (_, _, resumed) = executor.resumed(
              suspension,
              dependencies,
              hotspot.Budget(limit, countedUnits = false, AlreadyStopped)
            )
            Result
              .assert(resumed.spent.steps <= Budget.stopCheckSteps)
              .log(s"resumed for ${resumed.spent.steps}")
    }
  )
