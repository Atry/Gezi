package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.weakhead.Trampoline.done
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result

/** The law that the tabling computes each key's answers once, as tablambda's
  * tabling does (its paper's Algorithms 1 to 3, which also set the time
  * complexity): a key whose body gives n answers, each after c steps, asked for
  * M times by consumers that each stop at the first answer they look for
  * (`Answers.exists`), the answers looked for drawn, takes (1 + j) c steps in
  * all, j the furthest answer looked for: a consumer reads the answers found so
  * far for no step and drives the key's producer from where the last consumer
  * left it. Its purpose is to catch a producer given up by a consumer and
  * evaluated again from its body by the next one: MEASURED 2026-11-19 on
  * e45454515, which did that, n = 100, c = 50 and every consumer looking for
  * the last answer took M times 5,000 steps.
  */
class TablingReuseLawTest extends GeneratedProperties:

  private final case class State(
      tables: Tables[State, Int, Int],
      budget: Budget
  )

  private val stepTaken: Computation[State, Unit] =
    Computation(state =>
      done(state.budget.charged match
        case Some(charged) => Computed.Done((), state.copy(budget = charged))
        case None          => Computed.Stopped(state))
    )

  /** The key 0, whose answers are 0 to n - 1, each after c steps. */
  private def tabling(answers: Int, cost: Int): Tabling[State, Int, Int] =
    Tabling(
      _.tables,
      (state, tables) => state.copy(tables = tables),
      _ => CompletedTables.unshared,
      (_, _) =>
        (0 until answers).foldRight(Answers.empty[State, Int])(
          (answer, later) =>
            Answers(
              (0 until cost)
                .foldLeft(Computation.pure[State, Unit](()))((steps, _) =>
                  steps.flatMap(_ => stepTaken)
                )
                .map(_ => Some((answer, later)))
            )
        )
    )

  property(
    "a key asked for many times by consumers that stop early is computed once"
  ) {
    for
      answers <- Gen.int(Range.linear(1, 60)).forAll
      cost <- Gen.int(Range.linear(1, 20)).forAll
      sought <- Gen
        .list(Gen.int(Range.constant(0, answers - 1)), Range.linear(1, 30))
        .forAll
    yield
      val tabled = tabling(answers, cost)
      sought.foldLeft[Either[String, State]](
        Right(State(Tables.empty, Budget.of(Long.MaxValue / 2)))
      )((reached, answer) =>
        reached.flatMap(state =>
          tabled
            .answers(0)
            .exists(found => Computation.pure(found == answer))
            .result(state) match
            case Computed.Done(true, after) => Right(after)
            case other => Left(s"answer $answer not found: $other")
        )
      ) match
        case Right(after) =>
          Result
            .diff(after.budget.spent, (1L + sought.max) * cost)(_ == _)
            .log(s"sought $sought")
        case Left(why) => Result.failure.log(why)
  }
