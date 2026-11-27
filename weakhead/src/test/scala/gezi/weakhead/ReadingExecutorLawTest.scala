package gezi.weakhead

import gezi.ir.NoFacts

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties
import gezi.standardlibrary.SplitMix

/** The resume law and honest costs (`ExecutorLaws`) of the weak-head reference
  * as an executor (`ReadingExecutor`) under `weak_head` and
  * `tabling(weak_head)`. Its purpose is to catch a suspension that loses or
  * repeats a normal form when it is resumed, or an execution that reports other
  * steps than its budget charged. The inputs are choices of one to three random
  * closed applications of `EvaluatorTesting.randomApplication`, of sizes 2 to
  * 30, each drawn from a generated seed; a choice of several has several normal
  * forms, so that a resumption falls between two of them. The laws of the
  * counts of applications (`ExecutorLaws.countingUnobservableLaw`,
  * `honestCountsLaw`, `exactCountLaw`) catch a count that changes a reading, a
  * count of a code the reading never entered or entered once and counted twice,
  * and a missed entry, on the same terms and on Church numerals of 0 to 100.
  */
class ReadingExecutorLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val application: Gen[DeBruijnTerm] =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield EvaluatorTesting.randomApplication(size, SplitMix(seed))._1

  private val terms: Gen[DeBruijnTerm] =
    application.list(Range.linear(1, 3)).map {
      case List(single) => single
      case members      => DeBruijnTerm.nestedChoice(members.toVector)
    }

  private val modes: Vector[(String, Mode)] = Vector(
    ("weak_head", Mode.WeakHead),
    ("tabling(weak_head)", Mode.TablingWeakHead)
  )

  modes.foreach((name, mode) =>
    stoppableProperty(
      s"a resumed reading finds what an uninterrupted one finds, under $name"
    ) { stopped =>
      for term <- terms.forAll
      yield ExecutorLaws.resumeLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        ),
        mode,
        term,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"a suspension's residual reads with what was found to what the term reads, under $name"
    ) { stopped =>
      for term <- terms.forAll
      yield ExecutorLaws.residualLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        ),
        term,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"an execution spends the least budget it finishes in, under $name"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.honestCostsLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        ),
        term,
        steps,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"counting the applications of codes changes nothing else, under $name"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.countingUnobservableLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState,
          tableRetention = TableRetention.KeptAll
        ),
        term,
        steps,
        StopSignal.completedWith(stopped),
        ExecutorLaws.readingTablesAlike
      )
    }

    stoppableProperty(
      s"the applications counted are positive, of codes the term reaches, at most the steps and deterministic, under $name"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.honestCountsLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        ),
        term,
        steps,
        StopSignal.completedWith(stopped),
        withinSteps = true,
        readerCodes = Set.empty
      )
    }

    stoppableProperty(
      s"a numeral of n applies its step function exactly n times, under $name"
    ) { stopped =>
      for n <- Gen.int(Range.linear(0, 100)).forAll
      yield ExecutorLaws.exactCountLaw(
        ReadingExecutor(
          mode,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState
        ),
        n,
        StopSignal.completedWith(stopped)
      )
    }
  )

  /** Under `ContinuationReading.Packed`, counting is unobservable and the
    * counts honest on the consumers of a program in continuation passing style
    * (`ContinuationPrograms.consumers`), whose readings walk the pack, take the
    * fallback and walk the continuations the step functions fill, the entries
    * `WeakHead` counts under `Packed` (APPLICATIONS COUNTED).
    */
  stoppableProperty(
    "counting the applications of codes changes nothing else and counts honestly, under Packed"
  ) { stopped =>
    for
      consumers <- ContinuationPrograms.consumers.forAll
      steps <- Gen.long(Range.linear(0L, 2000L)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val executor = ReadingExecutor(
        Mode.TablingWeakHead,
        gezi.weakhead.ReadingConfiguration.withoutFacts,
        NoJitState,
        tableRetention = TableRetention.KeptAll,
        continuations = ContinuationReading.Packed
      )
      val term = EvaluatorTesting.lambdaTerm(consumers.last)
      hedgehog.Result.all(
        List(
          ExecutorLaws.countingUnobservableLaw(
            executor,
            term,
            steps,
            stop,
            ExecutorLaws.readingTablesAlike
          ),
          ExecutorLaws.honestCountsLaw(
            executor,
            term,
            steps,
            stop,
            withinSteps = true,
            readerCodes = ExecutorLaws.packCodes
          )
        )
      )
  }

  /** The other terms and the last term the retention law reads under a
    * continuation reading. Under `Packed`, the others hold consumers of one
    * program in continuation passing style (`ContinuationPrograms.consumers`)
    * and the last is another of them, so that the last meets, through a key of
    * its own, the table of the program applied to the pack that an earlier call
    * completed, with the marks its walk made.
    */
  private def retentionInputs(
      continuations: ContinuationReading
  ): Gen[(List[DeBruijnTerm], DeBruijnTerm)] =
    continuations match
      case ContinuationReading.Substituted =>
        for
          others <- terms.list(Range.linear(0, 4))
          last <- terms
        yield (others, last)
      case ContinuationReading.Packed =>
        for
          others <- terms.list(Range.linear(0, 2))
          consumers <- ContinuationPrograms.consumers
        yield (
          others ++ consumers.init.map(EvaluatorTesting.lambdaTerm),
          EvaluatorTesting.lambdaTerm(consumers.last)
        )

  /** Under each table retention and each continuation reading, a term read by
    * the executor that read other terms before it, itself among them at a drawn
    * place, finds what a new executor finds, whenever both finish. Its purpose
    * is to catch tables an executor carries from one call to the next that
    * change an answer: a stopped call's tables carried with a producer a later
    * call misreads, tables of one call read under another's state, or, under
    * `Packed`, a table kept without the mark that asks its consumers for the
    * fallback (the review of
    * https://github.com/Atry/private-overlay/pull/1798).
    */
  for
    retention <- Vector(
      TableRetention.KeptAll,
      TableRetention.NoneKept,
      TableRetention.DroppedAtPercent(50)
    )
    continuations <- ContinuationReading.values.toVector
  do
    stoppableProperty(
      s"a term read after others finds what a new executor finds, under $retention and $continuations"
    ) { stopped =>
      for
        (others, last) <- retentionInputs(continuations).forAll
        position <- Gen.int(Range.constant(0, others.size)).forAll
        steps <- Gen.long(Range.linear(1L, ExecutorLaws.largeSteps)).forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        val budget = gezi.hotspot.Budget(steps, countedUnits = false, stop)
        val executor = ReadingExecutor(
          Mode.TablingWeakHead,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState,
          tableRetention = retention,
          continuations = continuations
        )
        val earlier = others.take(position) ++ (last :: others.drop(position))
        val filled = earlier.foldLeft(
          executor: gezi.hotspot.Executor[NoFacts.type, ReadingSuspension[
            NoFacts.type
          ]]
        ) { (current, term) =>
          val (instruction, context) = ExecutorLaws.interned(term)
          current.executed(instruction, context, budget)._1
        }
        val (instruction, context) = ExecutorLaws.interned(last)
        val (_, _, afterOthers) = filled.executed(
          instruction,
          context,
          gezi.hotspot
            .Budget(ExecutorLaws.largeSteps, countedUnits = false, stop)
        )
        val (_, _, alone) = executor.executed(
          instruction,
          context,
          gezi.hotspot
            .Budget(ExecutorLaws.largeSteps, countedUnits = false, stop)
        )
        (afterOthers.suspension, alone.suspension) match
          case (None, None) =>
            hedgehog.Result.diff(afterOthers.found.toSet, alone.found.toSet)(
              _ == _
            )
          case _ => hedgehog.Result.success
    }

  /** Under each continuation reading, a term read by an executor that keeps its
    * complete tables in a cache service, after the same executor read other
    * terms in the same context, itself among them at a drawn place, finds what
    * it finds in a context of a new cache service, whenever both finish. Each
    * call starts from no table of its own (`NoneKept`), so that the tables it
    * meets are the service's alone. Its purpose is to catch a table shared
    * without what it depends on: under `Packed`, a table of a head applied to
    * the pack kept or found without the mark of its head, whose consumers then
    * skip the fallback.
    */
  ContinuationReading.values.toVector.foreach(continuations =>
    stoppableProperty(
      s"a term read after others in a shared cache finds what it finds alone, under $continuations"
    ) { stopped =>
      for
        (others, last) <- retentionInputs(continuations).forAll
        position <- Gen.int(Range.constant(0, others.size)).forAll
        steps <- Gen.long(Range.linear(1L, ExecutorLaws.largeSteps)).forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        val budget = gezi.hotspot.Budget(steps, countedUnits = false, stop)
        val large = gezi.hotspot
          .Budget(ExecutorLaws.largeSteps, countedUnits = false, stop)
        val executor = ReadingExecutor(
          Mode.TablingWeakHead,
          gezi.weakhead.ReadingConfiguration.withoutFacts,
          NoJitState,
          sharedRetention = Some(gezi.hotspot.Retention.Strong),
          continuations = continuations
        )
        val (_, shared) = ExecutorLaws.interned(last)
        val earlier = others.take(position) ++ (last :: others.drop(position))
        earlier.foreach(term =>
          val (instruction, _) = ExecutorLaws.interned(term)
          val _ = executor.executed(instruction, shared, budget)
        )
        val (instruction, fresh) = ExecutorLaws.interned(last)
        val (_, _, afterOthers) = executor.executed(instruction, shared, large)
        val (_, _, alone) = executor.executed(instruction, fresh, large)
        (afterOthers.suspension, alone.suspension) match
          case (None, None) =>
            hedgehog.Result.diff(afterOthers.found.toSet, alone.found.toSet)(
              _ == _
            )
          case _ => hedgehog.Result.success
    }
  )
