package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.instructionOf
import gezi.jit.JitTesting.noFacts
import gezi.jit.NativesTesting.normalFormsSpent
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.weakhead.Value
import gezi.weakhead.Values

/** The sharing law of the instance table: what the table read before does
  * not take call-by-need sharing away from a later reading. A function that
  * reads its argument twice (`\x. x zero (\p. x)` over Scott naturals),
  * iterated k times by a recursive `iterate`, is read after a hot loop of
  * the same codes that shares nothing: `iterate` over successor, a function
  * that reads its argument once, and the function that reads its argument
  * twice applied to distinct numerals, each read once; and it reads what it
  * reads from an empty table, within twice the steps (plus 1,000). Its
  * purpose is to catch a table cost verdict (`TableCost.unprofitable`) that, reached on `iterate`'s codes in
  * the hot loop, stops tabling the values the later loop reads twice, so
  * that the later reading takes steps exponential in k (the defect of
  * 2026-11-02: 382,000 native calls and no answer in 90 s against 641 calls
  * in 1.4 s without the verdict). The cutoff is reached after four entries
  * (`instanceTableTrial` = 4) and the hot calls, 8 to 64, exceed it; k is 4
  * to 20.
  */
class TableSharingLawTest extends GeneratedProperties:

  private val limit: Long = 2000000

  private val configuration = JitConfiguration(
    noFacts,
    10000,
    PredicatePerCode,
    ClosureBackend,
    DispatchMode.NoDispatch,
    instanceTable = true,
    instanceTableTrial = 4
  )

  private val zero: Term = λ(z => λ(_ => z))

  private val successor: Term = λ(n => λ(_ => λ(s => s(n))))

  private def numeral(size: Int): Term = (1 to size).foldLeft(zero)((value, _) => successor(value))

  private val fixpoint: Term =
    val turing = λ(x => λ(f => f(x(x)(f))))
    turing(turing)

  private val iterate: Term =
    fixpoint(λ(self => λ(f => λ(n => λ(x => n(x)(λ(m => f(self(f)(m)(x)))))))))

  private val readTwice: Term = λ(x => x(zero)(λ(_ => x)))

  private def value(term: Term): Value = Values.ofInstruction(instructionOf(term.deBruijnTerm(Map.empty)), Set.empty)

  property("a value read twice stays shared after a hot loop of the same code") {
    for
      hot <- Gen.int(Range.linear(8, 64)).forAll
      iterations <- Gen.int(Range.linear(4, 20)).forAll
    yield
      val jit = Jit(configuration)
      val hotLoop = value(choice((iterate(successor)(numeral(hot))(zero) +: (1 to hot).map(index => readTwice(numeral(index))))*))
      val shared = value(iterate(readTwice)(numeral(iterations))(numeral(1)))
      val afterHot = normalFormsSpent(Mode.Jit(jit), hotLoop, limit).jitState
      val fresh = normalFormsSpent(Mode.Jit(jit), shared, limit)
      val later = normalFormsSpent(Mode.Jit(jit), shared, limit, afterHot)
      (fresh.outcome, later.outcome) match
        case (Bounded.Finished(fromEmpty), Bounded.Finished(fromHot)) =>
          Result
            .diff(fromHot, fromEmpty)(_ == _)
            .and(Result.diff(later.steps, 2 * fresh.steps + 1000)(_ <= _))
        case _ => Result.failure.log(s"a reading stopped: from empty ${fresh.steps} steps, after the hot loop ${later.steps}")
  }
