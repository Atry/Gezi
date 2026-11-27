package gezi.jit

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.GeneratedProperties
import gezi.standardlibrary.SplitMix
import gezi.weakhead.ExecutorLaws
import gezi.weakhead.Mode

/** The resume law and honest costs (`gezi.weakhead.ExecutorLaws`) of the JIT as
  * an executor (`JitExecutor`), with no library and the compilation budgets of
  * `JitTest`: 10,000 codes, and 0 (every instance interpreted). Its purpose is
  * to catch a suspension of a JIT reading that loses or repeats a normal form
  * when it is resumed, or that resumes from a JIT state the stop left
  * half-made, and an execution that reports other steps than its budget
  * charged. The inputs are the random closed applications with choices and
  * parallels of `JitTesting.randomLatticeApplication`, of sizes 2 to 30, drawn
  * from a generated seed. The laws of the counts of applications catch a count
  * that changes a JIT reading's normal forms or steps, a count of a code the
  * reading never entered, and a missed or doubled entry on Church numerals; the
  * counts are not held to the steps, since a compiled clause that starts with
  * an instance enters it within the step of its own code (`Jit`, APPLICATIONS
  * COUNTED), and the executors are not compared, since compiled closures
  * compare by identity.
  */
class JitExecutorLawTest extends GeneratedProperties:

  private val terms: Gen[DeBruijnTerm] =
    for
      size <- Gen.int(Range.linear(2, 30))
      seed <- Gen.long(Range.linear(0L, Long.MaxValue))
    yield JitTesting.randomLatticeApplication(size, SplitMix(seed))._1

  private val budgets: Vector[Int] = Vector(10000, 0)

  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  budgets.foreach(budget =>
    val jit = Jit(JitTesting.configured(encoding, budget))

    stoppableProperty(
      s"a resumed JIT reading finds what an uninterrupted one finds, compilation budget $budget"
    ) { stopped =>
      for term <- terms.forAll
      yield ExecutorLaws.resumeLaw(
        JitExecutor.of(jit),
        Mode.Jit,
        term,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"a suspension's residual reads with what was found to what the term reads, compilation budget $budget"
    ) { stopped =>
      for term <- terms.forAll
      yield ExecutorLaws.residualLaw(
        JitExecutor.of(jit),
        term,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"a JIT execution spends the least budget it finishes in, compilation budget $budget"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.honestCostsLaw(
        JitExecutor.of(jit),
        term,
        steps,
        StopSignal.completedWith(stopped)
      )
    }

    stoppableProperty(
      s"counting the JIT's applications of codes changes nothing else, compilation budget $budget"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.countingUnobservableLaw(
        JitExecutor.of(jit),
        term,
        steps,
        StopSignal.completedWith(stopped),
        (_, _) => hedgehog.Result.success
      )
    }

    stoppableProperty(
      s"the JIT's applications counted are positive, of codes the term reaches and deterministic, compilation budget $budget"
    ) { stopped =>
      for
        term <- terms.forAll
        steps <- Gen.long(Range.linear(0L, 2000L)).forAll
      yield ExecutorLaws.honestCountsLaw(
        JitExecutor.of(jit),
        term,
        steps,
        StopSignal.completedWith(stopped),
        withinSteps = false,
        readerCodes = Set.empty
      )
    }

    stoppableProperty(
      s"a numeral of n applies its step function exactly n times under the JIT, compilation budget $budget"
    ) { stopped =>
      for n <- Gen.int(Range.linear(0, 100)).forAll
      yield ExecutorLaws.exactCountLaw(
        JitExecutor.of(jit),
        n,
        StopSignal.completedWith(stopped)
      )
    }
  )
