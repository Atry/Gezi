package gezi.weakhead

import gezi.ir.NoFacts
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.standardlibrary.SplitMix

/** The law of the retentions of a reading's tables for the next reading of
  * the same owner (`ReadingState.next`, `TableRetention`):
  * a sequence of
  * generated closed terms read one after another, each round from the state
  * the last one left under a retention, reads the same heads as rounds that
  * keep every table under no limit, and after each round the tables held are
  * none under `NoneKept` and fewer than the retention's share of a small
  * table limit under `DroppedAtPercent`. Its purpose is to catch a dropped
  * table that changes an answer, a dropped table whose state a later round
  * still reads (a producer, a status), and a retention that keeps more than
  * it promises. The shares checked are 1, 50 (half the limit, the share a
  * long run of FFI calls was measured with)
  * and 100 percent.
  */
class TableRetentionLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val stepLimit: Long = 20000

  /** A table limit small enough that the rounds drop their tables often. */
  private val tableLimit: Int = 24

  private val rounds =
    Gen.list(
      for
        size <- Gen.int(Range.linear(2, 20))
        seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      yield EvaluatorTesting.randomApplication(size, SplitMix(seed))._1,
      Range.linear(1, 12)
    )

  /** The heads of each round, if it finished, and the tables held after each
    * round's next state.
    */
  private def read(
      terms: List[gezi.frontend.DeBruijnTerm],
      start: ReadingState[NoFacts.type],
      next: ReadingState[NoFacts.type] => ReadingState[NoFacts.type]
  ): (Vector[Option[Vector[ParallelSet[NoFacts.type]]]], Vector[Int]) =
    val (_, heads, held) = terms.foldLeft((start, Vector.empty[Option[Vector[ParallelSet[NoFacts.type]]]], Vector.empty[Int])) {
      case ((state, found, tables), term) =>
        val value = gezi.ir.Value.of(Defunctionalization.thunkInstruction[NoFacts.type](term))
        WeakHead.heads(Mode.TablingWeakHead, value).collected.result(state) match
          case Computed.Done(sets, after) =>
            val following = next(after)
            (following, found :+ Some(sets), tables :+ following.tables.held)
          case Computed.Stopped(after) =>
            val following = next(after)
            (following, found :+ None, tables :+ following.tables.held)
    }
    (heads, held)

  private val retentions: Vector[(TableRetention, Int => Boolean)] =
    Vector(
      (TableRetention.KeptAll, _ => true),
      (TableRetention.NoneKept, _ == 0),
      (TableRetention.DroppedAtPercent(1), held => held * 100 < tableLimit * 1),
      (TableRetention.DroppedAtPercent(50), held => held * 100 < tableLimit * 50),
      (TableRetention.DroppedAtPercent(100), held => held * 100 < tableLimit * 100)
    )

  retentions.foreach((retention, heldWithin) =>
    property(s"rounds under $retention read the heads that rounds keeping every table read") {
      for terms <- rounds.forAll
      yield
        val (kept, _) = read(terms, ReadingState.fresh(stepLimit, gezi.weakhead.ReadingConfiguration.withoutFacts).copy(tableLimit = Int.MaxValue), _.nextReading(stepLimit))
        val (retained, held) = read(terms, ReadingState.fresh(stepLimit, gezi.weakhead.ReadingConfiguration.withoutFacts).copy(tableLimit = tableLimit), _.next(retention, stepLimit))
        val compared = kept.zip(retained).collect { case (Some(keptHeads), Some(retainedHeads)) => (keptHeads, retainedHeads) }
        Result.all(
          List(
            Result.diff(compared.map(_._2), compared.map(_._1))(_ == _),
            Result.assert(retention == TableRetention.KeptAll || held.forall(heldWithin)).log(s"tables held after each round: $held")
          )
        ).log(s"rounds finished under both: ${compared.size} of ${terms.size}")
    }
  )
