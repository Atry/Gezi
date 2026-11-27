package com.yang_bo.gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.weakhead.Trampoline.done

/** The laws of the tabling's streams (`Tabling`), on generated equation systems
  * whose bodies give their answers as they find them: the answers of key k are
  * its own label `100 * k` and, for each key r it reads, every answer of r that
  * passes r's filter at k, shifted by one while it is less than five above its
  * label, so that a body reading its own key grows its set over several
  * iterations. A body reads its keys lazily, one answer at a time
  * (`Answers.flatMap`), and calls its next key for every answer of the one
  * before (`chained`), so a frame is suspended after each new answer while its
  * caller reads other keys, among them, through cycles, the suspended frame's
  * own. Their purpose is to catch an answer lost or a table completed early
  * when frames are suspended: a dependency recorded on the wrong frame, a
  * growth not counted, a lowlink not restored.
  *
  *   1. Every key's answers are those of the least fixed point computed by
  *      naive iteration from the empty sets (`leastFixedPoint`), read alone and
  *      read with another key's stream pulled between its answers, the tables
  *      shared.
  *   2. A key whose answers include one found before a part of its body that
  *      never ends gives that answer before the budget stops it: key 0 reads
  *      key 1, whose own label 100 key 0 gives as 101, and key 1 then reads key
  *      2, which reads key 3, and so on without end.
  */
class TablingStreamLawTest extends GeneratedProperties:

  private final case class State(
      tables: Tables[State, Int, Int],
      budget: Budget
  )

  /** An equation system over the keys 0 to `size - 1`: the keys each reads, in
    * order, and whether the answer passes from the read key to the reader.
    */
  private final case class Equations(
      size: Int,
      reads: Map[Int, Vector[Int]],
      passes: (Int, Int, Int) => Boolean
  )

  private val stepTaken: Computation[State, Unit] =
    Computation(state =>
      done(state.budget.charged match
        case Some(charged) => Computed.Done((), state.copy(budget = charged))
        case None          => Computed.Stopped(state))
    )

  private def answerOf(
      reader: Int,
      read: Int,
      answer: Int,
      equations: Equations
  ): Vector[Int] =
    if !equations.passes(reader, read, answer) then Vector.empty
    else if answer % 100 < 5 then Vector(answer + 1)
    else Vector(answer)

  private def tabling(equations: Equations): Tabling[State, Int, Int] =
    Tabling(
      _.tables,
      (state, tables) => state.copy(tables = tables),
      _ => CompletedTables.unshared,
      (key, call) =>
        Answers(
          stepTaken.map(_ => Some((100 * key, Answers.empty[State, Int])))
        ).appended(
          chained(
            key,
            equations.reads.getOrElse(key, Vector.empty),
            call,
            equations
          )
        )
    )

  /** The answers of the reads, each later read called again for every answer of
    * the one before it, while that one's frame is suspended, as the weak head
    * calls an application's argument for every parallel set of its function.
    * Every key's own label is among its answers, so in the least fixed point
    * every read has an answer and the later reads are read.
    */
  private def chained(
      key: Int,
      reads: Vector[Int],
      call: Int => Answers[State, Int],
      equations: Equations
  ): Answers[State, Int] =
    reads match
      case read +: later =>
        call(read).flatMap(answer =>
          Answers
            .of[State, Int](answerOf(key, read, answer, equations))
            .appended(chained(key, later, call, equations))
        )
      case _ => Answers.empty

  private def leastFixedPoint(equations: Equations): Map[Int, Set[Int]] =
    val keys = 0 until equations.size
    @scala.annotation.tailrec
    def iterated(current: Map[Int, Set[Int]]): Map[Int, Set[Int]] =
      val next = keys
        .map(key =>
          key -> (Set(100 * key) ++ equations.reads
            .getOrElse(key, Vector.empty)
            .flatMap(read =>
              current(read).toVector.flatMap(answerOf(key, read, _, equations))
            ))
        )
        .toMap
      if next == current then current else iterated(next)
    iterated(keys.map(_ -> Set.empty[Int]).toMap)

  private val systems: Gen[Equations] =
    for
      size <- Gen.int(Range.linear(1, 8))
      reads <- Gen.list(
        Gen.list(Gen.int(Range.constant(0, size - 1)), Range.linear(0, 3)),
        Range.singleton(size)
      )
      modulus <- Gen.int(Range.constant(2, 5))
      residue <- Gen.int(Range.constant(0, 4))
    yield Equations(
      size,
      reads.zipWithIndex.map((keys, key) => key -> keys.toVector).toMap,
      (reader, read, answer) =>
        (answer + reader + read) % modulus != residue % modulus || answer % 100 == 0
    )

  private val limit: Long = 1000000

  /** The first answer of the stream, the answers of the other key read whole,
    * then the rest of the first stream: both read with one set of tables.
    */
  private def interleaved(
      tabled: Tabling[State, Int, Int],
      first: Int,
      other: Int
  ): Option[(Vector[Int], Vector[Int])] =
    tabled
      .answers(first)
      .pull
      .result(State(Tables.empty, Budget.of(limit))) match
      case Computed.Done(None, after) =>
        tabled.answers(other).collected.result(after) match
          case Computed.Done(otherAnswers, _) =>
            Some((Vector.empty, otherAnswers))
          case Computed.Stopped(_) => None
      case Computed.Done(Some((answer, more)), after) =>
        tabled.answers(other).collected.result(after) match
          case Computed.Done(otherAnswers, afterOther) =>
            more.collected.result(afterOther) match
              case Computed.Done(rest, _) =>
                Some((answer +: rest, otherAnswers))
              case Computed.Stopped(_) => None
          case Computed.Stopped(_) => None
      case Computed.Stopped(_) => None

  property(
    "every key's streamed answers are the least fixed point's, read alone or interleaved with another key's"
  ) {
    for
      equations <- systems.forAll
      first <- Gen.int(Range.constant(0, equations.size - 1)).forAll
      other <- Gen.int(Range.constant(0, equations.size - 1)).forAll
    yield
      val expected = leastFixedPoint(equations)
      val tabled = tabling(equations)
      val alone = (0 until equations.size).toList.map(key =>
        tabled
          .answers(key)
          .collected
          .result(State(Tables.empty, Budget.of(limit))) match
          case Computed.Done(answers, after) =>
            Result
              .all(
                List(
                  Result
                    .diff(answers.toSet, expected(key))(_ == _)
                    .log(s"key $key alone"),
                  Result
                    .assert(answers.distinct == answers)
                    .log(s"key $key gave an answer twice"),
                  Result
                    .assert(!after.tables.inProgress)
                    .log(s"key $key left an evaluation in progress"),
                  Result.all(
                    after.tables.complete.toList.map((completed, answers) =>
                      Result
                        .diff(answers.members, expected(completed))(_ == _)
                        .log(s"the complete table of $completed after key $key")
                    )
                  )
                )
              )
          case Computed.Stopped(_) => Result.failure.log(s"key $key stopped")
      )
      val together = interleaved(tabled, first, other) match
        case Some((firstAnswers, otherAnswers)) =>
          Result.all(
            List(
              Result
                .diff(firstAnswers.toSet, expected(first))(_ == _)
                .log(s"key $first interleaved"),
              Result
                .diff(otherAnswers.toSet, expected(other))(_ == _)
                .log(s"key $other read between"),
              Result
                .assert(firstAnswers.distinct == firstAnswers)
                .log(s"key $first gave an answer twice")
            )
          )
        case None => Result.failure.log("an interleaved reading stopped")
      Result.all(together :: alone).log(s"reads ${equations.reads}")
  }

  property(
    "an answer found before a part that never ends is given before the stop"
  ) {
    for budget <- Gen.long(Range.linear(10L, 1000L)).forAll
    yield
      val endless = Equations(Int.MaxValue, Map.empty, (_, _, _) => true)
      val tabled = Tabling[State, Int, Int](
        _.tables,
        (state, tables) => state.copy(tables = tables),
        _ => CompletedTables.unshared,
        (key, call) =>
          val read = call(key + 1).flatMap(answer =>
            Answers.of(answerOf(key, key + 1, answer, endless))
          )
          if key == 0 then Answers(stepTaken.flatMap(_ => read.pull))
          else
            Answers(
              stepTaken.map(_ => Some((100 * key, Answers.empty[State, Int])))
            ).appended(read)
      )
      tabled
        .answers(0)
        .pull
        .result(State(Tables.empty, Budget.of(budget))) match
        case Computed.Done(Some((answer, _)), _) =>
          Result.diff(answer, 101)(_ == _)
        case other => Result.failure.log(s"no answer before the stop: $other")
  }
