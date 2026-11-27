package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Term
import gezi.frontend.Term.*
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.JitTesting.instructionOf
import gezi.jit.JitTesting.noFactsEncoding
import gezi.jit.JitTesting.referenceConfiguration
import gezi.jit.JitTesting.sameTerms
import gezi.jit.NativesTesting.normalFormsSpent
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.ir.Value
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
  * to 20. The reading from an empty table is checked against a reference that
  * shares nothing with it: `readTwice` is the identity on numerals by the β
  * rule (`readTwice zero` is `zero`, `readTwice (successor m)` is
  * `(λp. successor m) m`), so `iterate readTwice k (numeral 1)` has the normal
  * forms of `numeral 1`, read by the tabled weak head; comparing the two JIT
  * readings with each other alone would let a defect both share pass.
  */
class TableSharingLawTest extends GeneratedProperties:

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  private val limit: Long = 2000000

  private val configuration = JitConfiguration[encoding.type](
    encoding,
    10000,
    PredicatePerCode,
    ClosureBackend,
    DispatchMode.NoDispatch,
    instanceTable = true,
    instanceTableTrial = 4,
    storageAccess = gezi.ir.StorageAccess.granted()
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

  private def value(term: Term): Value[encoding.type] = Values.ofInstruction(instructionOf(term.deBruijnTerm(Map.empty)), Set.empty)

  property("a value read twice stays shared after a hot loop of the same code") {
    for
      hot <- Gen.int(Range.linear(8, 64)).forAll
      iterations <- Gen.int(Range.linear(4, 20)).forAll
    yield
      val jit = Jit(configuration)
      val hotLoop = value(choice((iterate(successor)(numeral(hot))(zero) +: (1 to hot).map(index => readTwice(numeral(index))))*))
      val shared = value(iterate(readTwice)(numeral(iterations))(numeral(1)))
      val afterHot = normalFormsSpent(jit, hotLoop, limit).jitState
      val fresh = normalFormsSpent(jit, shared, limit)
      val later = normalFormsSpent(jit, shared, limit, afterHot)
      val reference = normalFormsSpent(Mode.TablingWeakHead, referenceConfiguration(jit), value(numeral(1)), limit)
      (fresh.outcome, later.outcome, reference.outcome) match
        case (Bounded.Finished(fromEmpty), Bounded.Finished(fromHot), Bounded.Finished(expected)) =>
          Result
            .assert(sameTerms(fromEmpty, expected))
            .and(Result.assert(sameTerms(fromHot, fromEmpty)))
            .and(Result.diff(later.steps, 2 * fresh.steps + 1000)(_ <= _))
        case _ => Result.failure.log(s"a reading stopped: from empty ${fresh.steps} steps, after the hot loop ${later.steps}")
  }
