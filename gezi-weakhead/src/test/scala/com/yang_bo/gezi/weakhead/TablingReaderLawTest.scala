package com.yang_bo.gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.weakhead.Trampoline.done

/** The law of a reader of several keys that stops early, on generated equation
  * systems (`Tabling`): a reader that, for each answer a of a key k, asks
  * whether another key j has an answer b with b ≡ a modulo m, and stops reading
  * j at the first that has (`Answers.exists`), gives exactly the answers a of
  * the least fixed point's k for which the least fixed point's j has such a b,
  * each once; every table it leaves complete holds the least fixed point's
  * answers, every approximation it leaves holds only answers of its key, and
  * every key read whole afterwards, from the tables it leaves, gives the least
  * fixed point's answers, which drives every producer given up to its end. j
  * may be k, or a key k's evaluation is still reading, and some bodies stop
  * early too (`Equations`), so producers are given up part way, and driven
  * again out of their depth-first order or after a producer they read has
  * ended. Its purpose is to catch such a producer completing a table from
  * answers it read before that table grew, and a reader that drops answers
  * found, which no reader may do. It does not reach a producer driven again
  * after one it read has run its body again (`Tables.holds`'s iteration): its
  * bodies stop early on a condition fixed in advance, so the reruns of a
  * component drive no producer further than its first run did.
  */
class TablingReaderLawTest extends GeneratedProperties:

  private final case class State(
      tables: Tables[State, Int, Int],
      budget: Budget
  )

  /** An equation system over the keys 0 to `size - 1`: the keys each reads, in
    * order, each read whole or until a first odd answer; the answers of k are
    * its label 100 k, the answers of the keys it reads whole, shifted by one
    * while less than five above their label, and 100 k + 50 when a key it reads
    * until a first odd answer has one. A label is even, so an odd answer comes
    * from a key read whole: a body that reads a key until a first odd answer
    * gives up that key's producer after it has read other keys, so that a
    * producer which read the giving one may be driven again after the giving
    * one has run its body again or ended.
    */
  private final case class Equations(
      size: Int,
      reads: Map[Int, Vector[(Int, Boolean)]]
  )

  private val stepTaken: Computation[State, Unit] =
    Computation(state =>
      done(state.budget.charged match
        case Some(charged) => Computed.Done((), state.copy(budget = charged))
        case None          => Computed.Stopped(state))
    )

  private def shifted(answer: Int): Int =
    if answer % 100 < 5 then answer + 1 else answer

  private def tabling(equations: Equations): Tabling[State, Int, Int] =
    Tabling(
      _.tables,
      (state, tables) => state.copy(tables = tables),
      _ => CompletedTables.unshared,
      (key, call) =>
        Answers(
          stepTaken.map(_ => Some((100 * key, Answers.empty[State, Int])))
        ).appended(
          equations.reads
            .getOrElse(key, Vector.empty)
            .foldRight(Answers.empty[State, Int])((read, later) =>
              read match
                case (whole, false) =>
                  call(whole)
                    .flatMap(answer =>
                      Answers.single[State, Int](shifted(answer))
                    )
                    .appended(later)
                case (first, true) =>
                  Answers(
                    call(first)
                      .exists(answer => Computation.pure(answer % 2 == 1))
                      .flatMap(found =>
                        if found then
                          Computation.pure(Some((100 * key + 50, later)))
                        else later.pull
                      )
                  )
            )
        )
    )

  private def leastFixedPoint(equations: Equations): Map[Int, Set[Int]] =
    val keys = 0 until equations.size
    @scala.annotation.tailrec
    def iterated(current: Map[Int, Set[Int]]): Map[Int, Set[Int]] =
      val next = keys
        .map(key =>
          key -> (Set(100 * key) ++ equations.reads
            .getOrElse(key, Vector.empty)
            .flatMap {
              case (whole, false) => current(whole).map(shifted)
              case (first, true)  =>
                if current(first).exists(_ % 2 == 1) then Set(100 * key + 50)
                else Set.empty
            })
        )
        .toMap
      if next == current then current else iterated(next)
    iterated(keys.map(_ -> Set.empty[Int]).toMap)

  private val systems: Gen[Equations] =
    for
      size <- Gen.int(Range.linear(1, 7))
      reads <- Gen.list(
        Gen.list(
          Gen
            .int(Range.constant(0, size - 1))
            .flatMap(read => Gen.boolean.map(read -> _)),
          Range.linear(0, 3)
        ),
        Range.singleton(size)
      )
    yield Equations(
      size,
      reads.zipWithIndex.map((keys, key) => key -> keys.toVector).toMap
    )

  private val limit: Long = 1000000

  property(
    "a reader that stops early gives the least fixed point's results and leaves no table short"
  ) {
    for
      equations <- systems.forAll
      first <- Gen.int(Range.constant(0, equations.size - 1)).forAll
      second <- Gen.int(Range.constant(0, equations.size - 1)).forAll
      modulus <- Gen.int(Range.constant(2, 4)).forAll
    yield
      val expected = leastFixedPoint(equations)
      val tabled = tabling(equations)
      val reader = tabled
        .answers(first)
        .flatMap(answer =>
          Answers(
            tabled
              .answers(second)
              .exists(other =>
                Computation.pure(other % modulus == answer % modulus)
              )
              .map(found =>
                if found then Some((answer, Answers.empty[State, Int]))
                else None
              )
          )
        )
      val wanted = expected(first).filter(answer =>
        expected(second).exists(_ % modulus == answer % modulus)
      )
      reader.collected.result(State(Tables.empty, Budget.of(limit))) match
        case Computed.Done(results, after) =>
          Result
            .all(
              List(
                Result
                  .diff(results.toSet, wanted)(_ == _)
                  .log("the reader's results"),
                Result
                  .assert(results.distinct == results)
                  .log("a result given twice"),
                Result
                  .assert(!after.tables.inProgress)
                  .log("an evaluation left in progress"),
                Result.all(
                  after.tables.complete.toList.map((key, answers) =>
                    Result
                      .diff(answers.members, expected(key))(_ == _)
                      .log(s"the complete table of $key")
                  )
                ),
                Result.all(
                  after.tables.open.toList.map((key, table) =>
                    Result
                      .assert(table.answers.members.subsetOf(expected(key)))
                      .log(s"the approximation of $key")
                  )
                ),
                Result.all(
                  (0 until equations.size).toList.map(key =>
                    tabled.answers(key).collected.result(after) match
                      case Computed.Done(answers, _) =>
                        Result
                          .diff(answers.toSet, expected(key))(_ == _)
                          .log(s"key $key read whole afterwards")
                      case Computed.Stopped(_) =>
                        Result.failure.log(s"key $key stopped afterwards")
                  )
                )
              )
            )
            .log(
              s"reads ${equations.reads}, first $first, second $second, modulus $modulus"
            )
        case Computed.Stopped(_) => Result.failure.log("the reader stopped")
  }
