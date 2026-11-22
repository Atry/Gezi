package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.instructionOf
import gezi.jit.JitTesting.noFacts
import gezi.jit.JitTesting.randomLatticeApplication
import gezi.standardlibrary.SplitMix
import gezi.weakhead.Answers
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ParallelSet
import gezi.weakhead.ReadingState
import gezi.weakhead.Value
import gezi.weakhead.Values
import gezi.weakhead.WeakHead

/** The laws that the instance table never costs an answer and decides what
  * the untabled reading cannot: an instance whose body is a choice of a term
  * T and of Ω, `(λx. T + Ω) (λy. y)`, gives under the table every head of T
  * that the untabled JIT gives before its budget stops it, and its reading
  * under the table ends: Ω has no head, and its untabled reading never ends,
  * while the table answers Ω met again within its own reading by its
  * approximation, none, and so decides it (`Jit.tabledInstance`, `Tabling`).
  * Their purpose is to catch a table that hands an instance's heads on only
  * once its reading has ended (before 2026-11-18 a miss read the instance to
  * its end before applying the first head, and such an instance gave no head
  * at all under the table), and a table that runs an instance's re-entry
  * untabled (before re-entries took the approximation and iterated,
  * Omega read to the budget under the table too). T is a random closed application
  * with choices and parallels (`JitTesting.randomLatticeApplication`), of
  * size 2 to 30, kept only when the untabled JIT reads it to its end within
  * the limit.
  */
class InstanceTableAnswersLawTest extends GeneratedProperties:

  private val limit: Long = 20000

  private def configuration(tabled: Boolean) =
    JitConfiguration(noFacts, 10000, PredicatePerCode, ClosureBackend, DispatchMode.NoDispatch, instanceTable = tabled)

  private val omega: DeBruijnTerm =
    val selfApplication = DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(0)))
    DeBruijnTerm.Apply(selfApplication, selfApplication)

  /** The heads the stream gives before it ends or is stopped, and whether it
    * ended.
    */
  @scala.annotation.tailrec
  private def pulled(
      heads: Answers[ReadingState, ParallelSet],
      state: ReadingState,
      found: Vector[ParallelSet]
  ): (Vector[ParallelSet], Boolean) =
    heads.pull.result(state) match
      case Computed.Done(Some((head, more)), after) => pulled(more, after, found :+ head)
      case Computed.Done(None, _)                   => (found, true)
      case Computed.Stopped(_)                      => (found, false)

  private def headsBeforeTheStop(tabled: Boolean, value: Value, budget: Long): (Vector[ParallelSet], Boolean) =
    val mode = Mode.Jit(Jit(configuration(tabled)))
    val (heads, ended) = pulled(WeakHead.heads(mode, value), ReadingState.fresh(budget), Vector.empty)
    (WeakHead.headsExpanded(mode, heads), ended)

  private val readTerms =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield randomLatticeApplication(size, SplitMix(seed))._1

  property("an instance with a member that has no head gives under the table every head it gives untabled, and ends") {
    for term <- readTerms.forAll
    yield
      val (alone, ended) = headsBeforeTheStop(tabled = false, Values.ofInstruction(instructionOf(term), Set.empty), limit)
      if !ended then Result.success
      else
        val instance = DeBruijnTerm.Apply(
          DeBruijnTerm.Lambda(DeBruijnTerm.Choice(term, omega)),
          DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))
        )
        val value = Values.ofInstruction(instructionOf(instance), Set.empty)
        val (untabled, _) = headsBeforeTheStop(tabled = false, value, limit)
        val (tabled, tabledEnded) = headsBeforeTheStop(tabled = true, value, limit)
        Result
          .all(
            List(
              Result.diff(untabled.toSet, alone.toSet)(_ == _).log("the untabled JIT's heads before the stop are T's"),
              Result.diff(tabled.toSet, untabled.toSet)(_ == _).log("the table's heads before the stop are the untabled JIT's"),
              Result.assert(tabledEnded).log("the reading under the table did not decide Ω"),
              Result.diff(tabled.toSet, alone.toSet)(_ == _).log("the table's heads are T's")
            )
          )
          .log(s"term $term")
  }
