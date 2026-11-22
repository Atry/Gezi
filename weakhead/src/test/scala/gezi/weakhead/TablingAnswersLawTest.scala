package gezi.weakhead

import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.weakhead.EvaluatorTesting.valueOf
import hedgehog.Gen
import hedgehog.Result

/** The law that tabling never gives fewer answers than no tabling, whatever
  * the caching policy: every parallel set the weak head gives
  * within `limit` steps, before it ends or stops, tabling(weak_head) gives
  * within `tabledLimit` steps. The terms are a generated closed term T alone,
  * and T in a choice with a member whose reading never ends, Ω, which re-enters
  * itself, or F F I with F = λx. λn. x x (n n), which reads a new term at
  * every unfolding, so that no table of it completes. Its purpose is to catch
  * a tabling that gives a term's answers only once its table completes (as
  * tabling(weak_head) did before 2026-11-18: on I + F F I within 20,000 steps
  * the weak head gave I, tabling none), or that loses answers by any cache
  * policy. The tabled reading is given ten times the steps: the two count
  * different work, and a tabled reading that finds the answers at all finds
  * them within a constant factor of the untabled one's steps.
  */
class TablingAnswersLawTest extends GeneratedProperties:

  private val limit: Long = 2000

  private val tabledLimit: Long = 10 * limit

  private def omega: Term = λ(x => x(x))(λ(x => x(x)))

  private def growing: Term =
    val unfolding = λ(x => λ(n => x(x)(n(n))))
    unfolding(unfolding)(λ(i => i))

  /** The parallel sets the mode gives, one at a time, until it ends or the
    * limit stops it.
    */
  @scala.annotation.tailrec
  private def pulled(
      heads: Answers[ReadingState, ParallelSet],
      state: ReadingState,
      found: Vector[ParallelSet]
  ): Vector[ParallelSet] =
    heads.pull.result(state) match
      case Computed.Done(Some((set, more)), after) => pulled(more, after, found :+ set)
      case Computed.Done(None, _)                  => found
      case Computed.Stopped(_)                     => found

  private def answersOf(mode: Mode, term: Term, steps: Long): Set[ParallelSet] =
    pulled(WeakHead.heads(mode, valueOf(term)), ReadingState.fresh(steps), Vector.empty).toSet

  property("tabling(weak_head) gives every parallel set the weak head gives") {
    for
      term <- HoasGenerators.closedTerm.forAll
      shape <- Gen.element1[Term => Term](identity, t => t + omega, t => t + growing, t => growing + t).forAll
    yield
      val read = shape(term)
      val untabled = answersOf(Mode.WeakHead, read, limit)
      val tabled = answersOf(Mode.TablingWeakHead, read, tabledLimit)
      Result.assert(untabled.subsetOf(tabled)).log(s"missing ${untabled -- tabled}; untabled ${untabled.size}, tabled ${tabled.size}")
  }
