package gezi.jit

import gezi.weakhead.Answers
import gezi.weakhead.Computation
import gezi.weakhead.Computed
import gezi.weakhead.ReadingState
import gezi.weakhead.Trampoline.tailcall

/** How far the instance table pulls a missed instance's reading on its own,
  * beyond the heads its consumers ask for (`JitConfiguration.instanceLookahead`).
  *
  * A missed instance's heads are a lazy stream (`Tabling`): a consumer that
  * takes the first head and goes on leaves the instance's producer suspended,
  * and its table is complete only once its stream is pulled to the end. A
  * one-answer instance whose consumer never asks for a second head therefore
  * stays open, with the producer's frames, until the reading ends, and so do
  * the instances its reading met: on a reading of a graph's values, every
  * table of the reading stays open, and the open tables fill the heap before
  * any completes.
  *
  * Pulling the rest of the stream right after its first head, within a bound
  * of steps, is the speculation: where the stream ends within the bound, the
  * table is complete in place, its producer's frames dropped, and the next
  * instance of the key a hit; where it gives another head, that head is the
  * stream's next; where the bound runs out first, the reading goes on from
  * the state before the lookahead, the bound's steps spent. It costs at most
  * the bound's steps per missed instance and never an answer: the heads and
  * their order are the stream's. Only an instance that leads its component
  * completes this way: one that depends on a producer further down the stack
  * is handed to that producer however far it is pulled.
  */
enum InstanceLookahead:

  /** Each head pulled only when a consumer asks for it, the table as it was
    * before lookaheads.
    */
  case Lazy

  /** The rest of a missed instance's stream pulled within `steps` steps
    * after its first head.
    */
  case WithinSteps(steps: Long)

/** The lookahead itself, over any stream of a reading's answers. */
object InstanceLookahead:

  /** The stream with its rest pulled within `steps` steps right after its
    * first head (`WithinSteps`): the limit of the pull is the lesser of the
    * steps after the head and the reading's own limit. A rest that ends or
    * gives its next head within it is the stream's rest as pulled, with the
    * state after the pull (where an instance's stream ends, the JIT has
    * recorded its complete table); a pull that stops under that limit, below
    * the reading's own, with no stop requested (its steps ran out, or work it
    * could not pay for was refused) goes back to the state after the first
    * head, the steps it spent still spent, and leaves the rest as it was;
    * one under the reading's own limit, or one a requested stop ended, stops
    * the stream there, as an unlimited pull would have.
    *
    * Going back drops what the pull changed in the reading's state, but not
    * a component it completed in the cache service when the reading shares
    * its complete tables (`JitRules.sharedInstances`): such a table is a
    * complete least fixed point, which another reading may take as any
    * other.
    */
  def lookedAhead[Answer](stream: Answers[ReadingState, Answer], steps: Long): Answers[ReadingState, Answer] =
    Answers(stream.pull.flatMap {
      case None => Computation.pure(None)
      case Some((head, rest)) =>
        Computation(after =>
          val limit = math.min(after.budget.spent + steps, after.budget.limit)
          tailcall(rest.pull.run(after.copy(budget = after.budget.copy(limit = limit)))).map {
            case Computed.Done(next, pulled) =>
              Computed.Done(Some((head, Answers(Computation.pure(next)))), pulled.copy(budget = pulled.budget.copy(limit = after.budget.limit)))
            case Computed.Stopped(stopped) if limit < after.budget.limit && !stopped.budget.stop.stopRequested =>
              Computed.Done(Some((head, rest)), after.copy(budget = after.budget.copy(spent = stopped.budget.spent)))
            case Computed.Stopped(stopped) =>
              Computed.Stopped(stopped.copy(budget = stopped.budget.copy(limit = after.budget.limit)))
          }
        )
    })
