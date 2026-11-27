package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.NoFacts
import gezi.weakhead.Answers
import gezi.weakhead.Computation
import gezi.weakhead.Computed
import gezi.weakhead.ReadingState
import gezi.weakhead.Trampoline.done

/** The law of the lookahead over a stream (`InstanceLookahead.lookedAhead`):
  * on a generated stream whose answers each cost a drawn number of steps, and
  * whose end costs some more, collected under a drawn limit, the stream
  * looked ahead within a drawn number of steps gives, wherever its
  * collection finishes, the answers the stream gives in their order, and the
  * stream's own collection finishes too. Its purpose is to catch a lookahead
  * that changes answers: a pulled head dropped or given twice, the rest
  * pulled again after a pull that gave its head, or a state kept from a pull
  * that ran out of its steps. A second law checks that case by
  * construction, every iteration: a stream of two answers or more, collected
  * under a limit that pays every answer and its end, gives exactly its
  * answers in their order, looked ahead or not, so that a pulled second head
  * is always checked.
  */
class InstanceLookaheadStreamLawTest extends GeneratedProperties:

  /** The answers, each after its cost in steps, then the end after its cost:
    * a cost the budget cannot pay stops the stream.
    */
  private def costly(answers: List[(Int, Long)], endCost: Long): Answers[ReadingState[NoFacts.type], Int] =
    Answers(Computation(state =>
      val (outcome, cost) = answers match
        case Nil                    => (None, endCost)
        case (answer, steps) :: rest => (Some((answer, costly(rest, endCost))), steps)
      done(state.budget.chargedTimes(cost) match
        case Some(budget) => Computed.Done(outcome, state.copy(budget = budget))
        case None         => Computed.Stopped(state)
      )
    ))

  private def collected(stream: Answers[ReadingState[NoFacts.type], Int], limit: Long): Option[Vector[Int]] =
    stream.collected.result(ReadingState.fresh(limit, gezi.weakhead.ReadingConfiguration.withoutFacts)) match
      case Computed.Done(answers, _) => Some(answers)
      case Computed.Stopped(_)       => None

  private val draws =
    for
      answers <- Gen.list(Gen.int(Range.linear(0, 9)).flatMap(answer => Gen.long(Range.linear(0L, 20L)).map(cost => (answer, cost))), Range.linear(0, 6))
      endCost <- Gen.long(Range.linear(0L, 20L))
      limit <- Gen.long(Range.linear(0L, 200L))
      steps <- Gen.long(Range.linear(1L, 40L))
    yield (answers, endCost, limit, steps)

  property("the lookahead gives the stream's answers wherever its collection finishes") {
    for drawn <- draws.forAll
    yield
      val (answers, endCost, limit, steps) = drawn
      collected(InstanceLookahead.lookedAhead(costly(answers, endCost), steps), limit) match
        case Some(found) =>
          Result.diff(collected(costly(answers, endCost), limit), Some(found))(_ == _).log(s"within $steps steps, limit $limit")
        case None => Result.success
  }

  /** Two answers or more by construction, and a limit that pays them all:
    * the costs of the answers and of the end. The lookahead charges no more
    * on this stream: a pull it goes back from keeps the steps it spent, but
    * `costly` charges an answer all at once or not at all (a refused charge
    * leaves the state as it was), so a pull that runs out spent nothing.
    */
  private val multipleAnswers =
    for
      answers <- Gen.list(Gen.int(Range.linear(0, 9)).flatMap(answer => Gen.long(Range.linear(0L, 20L)).map(cost => (answer, cost))), Range.linear(2, 6))
      endCost <- Gen.long(Range.linear(0L, 20L))
      steps <- Gen.long(Range.linear(1L, 40L))
    yield (answers, endCost, answers.map(_._2).sum + endCost, steps)

  property("a stream of two answers or more, its costs paid, gives exactly its answers, looked ahead or not") {
    for (answers, endCost, limit, steps) <- multipleAnswers.forAll
    yield
      val expected = Some(answers.map(_._1).toVector)
      Result.diff(collected(costly(answers, endCost), limit), expected)(_ == _).log("the stream")
        .and(Result.diff(collected(InstanceLookahead.lookedAhead(costly(answers, endCost), steps), limit), expected)(_ == _).log(s"looked ahead within $steps steps, limit $limit"))
  }
