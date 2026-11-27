package com.yang_bo.gezi.contest.corpora.common

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.PropertyConfig
import hedgehog.core.ShrinkLimit
import hedgehog.runner.SeedSource
import com.yang_bo.gezi.jit.Jit
import com.yang_bo.gezi.jit.JitConfiguration
import com.yang_bo.gezi.jit.JitTesting
import com.yang_bo.gezi.jit.Read
import com.yang_bo.gezi.jit.Verdict
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Computed
import com.yang_bo.gezi.weakhead.EvaluatorTesting
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.Head
import com.yang_bo.gezi.weakhead.JitState
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.weakhead.NoJitState
import com.yang_bo.gezi.weakhead.ParallelSet
import com.yang_bo.gezi.weakhead.Reading
import com.yang_bo.gezi.weakhead.ReadingState
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.NeutralValue
import com.yang_bo.gezi.weakhead.ReadingConfiguration
import com.yang_bo.gezi.weakhead.WeakHead
import com.yang_bo.gezi.weakhead.WitnessOutcome
import com.yang_bo.gezi.weakhead.oldcorpora.ConstructorTree
import com.yang_bo.gezi.weakhead.oldcorpora.ScottDecoding
import com.yang_bo.gezi.contest.corpora.claims.ContestClaims
import com.yang_bo.gezi.contest.corpora.claims.Ending
import com.yang_bo.gezi.contest.corpora.claims.OpenTest
import com.yang_bo.gezi.contest.corpora.reductions.CsesFamilies
import com.yang_bo.gezi.contest.corpora.reductions.Encodings
import com.yang_bo.gezi.contest.corpora.reductions.ReductionGroup
import com.yang_bo.gezi.contest.corpora.reductions.ReductionProblems
import com.yang_bo.gezi.contest.corpora.reductions.RepeatedVariant
import com.yang_bo.gezi.contest.corpora.reductions.RepeatedVariants
import com.yang_bo.gezi.contest.corpora.reductions.Scott
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.ReadableText
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.SeededSamples
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.jit.StorageEncoding

/** The law of the JIT (`com.yang_bo.gezi.jit.Jit`) against the reference evaluator,
  * tabling(weak_head), on generated programs: what the JIT reads of a program
  * equals what tabling(weak_head) reads, by the comparison protocol of
  * `gezi/tests/jit.plt` (`JitTesting.comparison`: when both finish within the
  * limit, or one finishes within it and the other within four times the limit
  * plus 100,000, their answers are equal), under the three budgets of jit.plt:
  * large (10,000, the cache kept from one reading to the next), none (0, every
  * instance interpreted) and small (3, the cache dropped before each reading).
  * The JIT reads with no library fact (`JitTesting.noFacts`). Its purpose is to
  * catch a compiled code that answers otherwise than the interpreter on the
  * same instance, including a code compiled while reading one program and
  * reused wrongly on another: the programs of one input are read in turn with
  * the JIT state kept, as the fixed corpora of jit.plt were.
  *
  * Four readings, each a property of its own: the heads of the programs of the
  * contest's repeated families; the normal forms of generated lattice terms
  * that hold top, where tabling(weak_head) finishing and the JIT not is a
  * failure too; the constructor trees a binary program of the arithmetic
  * reduction families decodes to by Scott case analysis; the judge's ending of
  * a claim, judged by witness, that a term is a Scott unary numeral. A fifth
  * test checks that the JIT writes no file. These replace the tests of jit.plt
  * on the fixed legacy corpora (the contest corpus, the 203 reduction problems
  * and the hard claims).
  *
  * SAMPLES: each property checks 30 inputs unless the environment variable
  * `LAMBDAJIT_JIT_LAW_SAMPLES` holds another count; a failure is shrunk at most
  * 8 times, since a shrink reads every program of the input again. The seed is
  * Hedgehog's (`GeneratedProperties`): `HEDGEHOG_SEED` replays a failure.
  *
  * COVERAGE: each property requires a share of its inputs on which the law is
  * not vacuous. The heads law's share (tabling(weak_head) reads every program
  * of the input within the limit, none left out) is 63% by the measurement at
  * `JitReadingLaw.readableFamilies`, whose families `repeatedPrograms` draws
  * half the time, drawn uniformly from every variant it is 28%; measured
  * directly over 100 inputs at seed 20261114 (2026-11-18), 67%. Measured
  * 2026-11-18 over 100 inputs at seed 20261118: the decoding law 100%, the
  * claims law 38% (some claim true) and 91% (some claim false). The thresholds
  * are 10%, 50%, 10% and 20%: at 30 inputs a run below them has a probability
  * of about 2e-10, 0, 1e-4 and 7e-22 (the binomial tails at the measured
  * shares), so a failure is a sign that the generators or the evaluator
  * changed. With far fewer samples than 30 the check can fail by chance (5
  * samples, a run of 2026-11-01: no true claim). The normal-form law over
  * lattice terms with top: 100% (tabling(weak_head) reads every term of the
  * input within the limit, measured 2026-11-18 over 100 inputs at seed
  * 20261118), threshold 50%.
  */
class JitReadingLawTest extends GeneratedProperties with HardCorpusSuite:

  /** The encoding of no facts, whose singleton type is the configuration the
    * law reads under: the reference reading and the JIT's both read terms of
    * it.
    */
  private val encoding: StorageEncoding = JitTesting.noFactsEncoding

  private type C = encoding.type

  private given encoding.type = encoding

  private given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  /** The reading configuration of the reference reading, the JIT's own
    * (`Jit.readingConfiguration`) being the other.
    */
  private val referenceConfiguration: ReadingConfiguration[C] =
    ReadingConfiguration[C](encoding, com.yang_bo.gezi.ir.StorageAccess.granted())

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of JitReadingLawTest, "the JIT writes no file", takes 39.449 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(60, "s")

  private def configured(config: PropertyConfig): PropertyConfig =
    config.copy(testLimit = JitReadingLaw.samples, shrinkLimit = ShrinkLimit(8))

  /** The three budgets and whether the cache is dropped before each reading
    * (jit.plt's `configuration_budget/2` and `term_prepared/1`).
    */
  private val budgets: Vector[(String, Int, Boolean)] =
    Vector(("large", 10000, false), ("none", 0, false), ("small", 3, true))

  /** A reading of a root under a mode within a limit, from a JIT state. */
  private type Reader[Answer] = (
      Mode,
      ReadingConfiguration[C],
      Value[C],
      Long,
      JitState[C]
  ) => Read[C, Answer]

  /** The roots of one input whose tabling(weak_head) answer the protocol can
    * compare, tabling(weak_head)'s reading of each within the limit, and the
    * count of the roots left out.
    */
  private final case class Prepared[Answer](
      roots: Vector[Value[C]],
      references: Vector[Bounded[Answer]],
      leftOut: Int
  ):
    def allFinished: Boolean = leftOut == 0 && references.forall(_.finished)

  /** The input's roots read under tabling(weak_head), those whose finished
    * answer is not `comparable` left out.
    */
  private def prepared[Answer](
      roots: Vector[Value[C]],
      reader: Reader[Answer],
      limit: Long,
      comparable: Answer => Boolean = (_: Answer) => true
  ): Prepared[Answer] =
    val read = roots.map(root =>
      root -> reader(
        Mode.TablingWeakHead,
        referenceConfiguration,
        root,
        limit,
        NoJitState
      ).outcome
    )
    val kept = read.filter {
      case (_, Bounded.Finished(answer)) => comparable(answer)
      case _                             => true
    }
    Prepared(kept.map(_._1), kept.map(_._2), roots.size - kept.size)

  /** The law on one input: under each budget, every root compared in turn with
    * the JIT state kept from one to the next unless the budget drops it,
    * tabling(weak_head)'s reading within the limit already read. Holds when no
    * comparison disagrees and, when `referenceOnlyFails`, no comparison is
    * `Verdict.ReferenceOnly` (tabling(weak_head) finished within the limit and
    * the JIT not within four times it plus 100,000); each budget's verdicts are
    * logged.
    */
  /** The JIT under the law: the test's configuration with the instance table
    * on, so that the JIT tables as its reference does (weak head without
    * tabling is a rejected design). Untabled, the JIT does not end on Ω,
    * `(λx. x x) (λx. x x)`, which tabling(weak_head) reads to no head by its
    * cycle.
    */
  private def tabledConfiguration(budget: Int): JitConfiguration[C] =
    val plain = JitTesting.configured(encoding, budget)
    JitConfiguration[C](
      plain.specializer,
      plain.budget,
      plain.strategy,
      plain.backend,
      plain.dispatch,
      instanceTable = true,
      storageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
    )

  private def agreed[Answer](
      input: Prepared[Answer],
      reader: Reader[Answer],
      limit: Long,
      referenceOnlyFails: Boolean
  ): Result =
    val results = budgets.map((name, budget, dropped) =>
      val evaluator = Jit(tabledConfiguration(budget))
      val questions = input.roots
        .zip(input.references)
        .map((root, alreadyRead) =>
          new JitTesting.Question[C, Answer]:
            def reference(asked: Long) =
              if asked == limit then alreadyRead
              else
                reader(
                  Mode.TablingWeakHead,
                  referenceConfiguration,
                  root,
                  asked,
                  NoJitState
                ).outcome
            def jit(asked: Long, jitState: JitState[C]) = reader(
              Mode.Jit,
              evaluator.readingConfiguration,
              root,
              asked,
              jitState
            )
        )
      val (comparisons, _) = questions.foldLeft(
        (
          Vector.empty[JitTesting.Comparison[C, Answer]],
          NoJitState: JitState[C]
        )
      ) { case ((found, jitState), question) =>
        val comparison =
          JitTesting.comparison(question, limit, jitState, dropped)
        (found :+ comparison, comparison.jitState)
      }
      val disagreements = comparisons.zipWithIndex.collect {
        case (
              JitTesting.Comparison(_, Some((answers, expected)), _),
              position
            ) =>
          Result.failure.log(
            s"budget $name, root $position: the JIT read $answers where tabling(weak_head) read $expected"
          )
      }
      val unfinished =
        if !referenceOnlyFails then Vector.empty
        else
          comparisons.zipWithIndex.collect {
            case (
                  JitTesting.Comparison(Verdict.ReferenceOnly, _, _),
                  position
                ) =>
              Result.failure.log(
                s"budget $name, root $position: tabling(weak_head) finished within $limit steps and the JIT not within ${4 * limit + 100000}"
              )
          }
      Result
        .all(Result.success :: (disagreements ++ unfinished).toList)
        .log(s"budget $name: ${comparisons.map(_.verdict).mkString(", ")}")
    )
    Result.all(results.toList)

  // ---- the heads of the contest's repeated families ----

  /** Every parallel set of the root, distinct and sorted, each by the texts of
    * its heads in order, so that two readings that find one set's heads in
    * different orders sort it alike; or, when the heads written out as trees
    * have more than `JitReadingLaw.comparedNodes` nodes, that bound (`Left`),
    * since the protocol compares and sorts answers as trees.
    */
  private val headsReader: Reader[Either[Long, Vector[ParallelSet[C]]]] =
    (mode, configuration, root, limit, jitState) =>
      JitTesting.headsRead(mode, configuration, root, limit, jitState) match
        case Read(Bounded.Finished(sets), after) =>
          val answer =
            if JitReadingLaw.treeNodesWithin(
                sets.flatMap(_.heads),
                JitReadingLaw.comparedNodes
              )
            then
              Right(
                sets.distinct.sortWith((first, second) =>
                  com.yang_bo.gezi.ir.ContentComparison.compare(
                    first.heads.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering),
                    second.heads.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering)
                  ) < 0
                )
              )
            else Left(JitReadingLaw.comparedNodes)
          Read(Bounded.Finished(answer), after)
        case Read(Bounded.Exceeded, after) => Read(Bounded.Exceeded, after)
        case Read(Bounded.Exhausted(resource), after) =>
          Read(Bounded.Exhausted(resource), after)

  // Replaces theJitReadsTheContestCorpusAsTheReference, whose points were
  // the legacy contest corpus's: the contest's points are now the repeated
  // families' programs drawn from a seed (the judge's
  // `CorpusSources.seededSources`), each family's single programs and its
  // repeated program here, at one or two repetitions.
  //
  // FIXME: a program whose heads under tabling(weak_head) have more than https://github.com/Atry/private-overlay/issues/1993
  // `JitReadingLaw.comparedNodes` nodes written out as trees is left out
  // (`Prepared.leftOut`), a downgrade of the law's domain: the comparison's
  // text and the sort by text in `headsReader` walk a shared subvalue once
  // per occurrence, so on such a program they cost the heads' size as trees
  // (equality and hash codes no longer do: every value is interned). On
  // program 0 of `ReductionMeaningsRepeated` at seed 568201625 and two
  // repetitions, the untabled weak head's head had 156 distinct nodes, the JIT's 162, and
  // 1.93e10 as a tree (measured 2026-11-01). The program returns to the law when the
  // comparison needs no text (the heads compared as interned terms), or the
  // text of a graph names its shared nodes.
  //
  // Each input also holds terms whose heads tabling(weak_head) reads within the limit by construction
  // (`JitReadingLaw.normalFormsBesideTop`, `x + top`, x a closed β normal form), so that the law compares finished
  // readings in every input; whether a repeated family's program finishes is not derived.
  property(
    "the JIT reads the heads of the repeated families' programs as tabling(weak_head) does",
    configured
  ) {
    for
      input <- JitReadingLaw.repeatedPrograms
        .forAllWithLog(_.described)
        .map(drawn =>
          prepared(
            JitReadingLaw.internedAll(drawn.programs),
            headsReader,
            JitReadingLaw.headsLimit,
            _.isRight
          )
        )
      constructed <- JitReadingLaw.normalFormsBesideTop.forAll
        .map(terms =>
          prepared(
            JitReadingLaw.internedAll(terms),
            headsReader,
            JitReadingLaw.headsLimit,
            _.isRight
          )
        )
    yield Result.all(
      List(
        agreed(
          input,
          headsReader,
          JitReadingLaw.headsLimit,
          referenceOnlyFails = false
        ),
        Result
          .assert(constructed.allFinished)
          .log(
            "tabling(weak_head) did not read a constructed term's heads within the limit"
          ),
        agreed(
          constructed,
          headsReader,
          JitReadingLaw.headsLimit,
          referenceOnlyFails = false
        )
      )
    )
  }

  // ---- the normal forms of lattice terms that read top ----

  /** The distinct normal forms of the root, sorted by their text. */
  private val normalFormsReader: Reader[Vector[Configured[C]]] =
    (mode, configuration, root, limit, jitState) =>
      JitTesting.normalFormsRead(mode, configuration, root, limit, jitState)

  // Its purpose: to catch the JIT's reading of normal forms departing from
  // tabling(weak_head)'s on a term in which top (`Term.top`, the miss of every curried
  // partial function) is read. top's body under its opened binder is the
  // parallel set {λy. top ∥ y, y}, which the reader reads as ∅ only when it
  // sees the head λy. top ∥ y as closed; a JIT that carries top in that head's
  // filling as a leaf the reader cannot see into made the reading descend
  // one binder at a time without end (`I + top` read {I} in 33 steps under
  // the untabled weak head and did not finish in 180,000 under the JIT, measured
  // 2026-11-13). The heads law cannot catch it: the two heads agree. Here
  // tabling(weak_head) finishing and the JIT not (`Verdict.ReferenceOnly`) fails as
  // a disagreement does, the JIT's contract being the reference's answers (the
  // framework owner's ruling, 2026-11-13); the other properties keep
  // jit.plt's protocol.
  //
  // Each input also holds terms tabling(weak_head) reads within the limit by
  // construction (`JitReadingLaw.normalFormsBesideTop`): `x + top`, x a
  // closed β normal form, whose reading reads x's normal form and drops top.
  property(
    "the JIT reads the normal forms of lattice terms with top as tabling(weak_head) does",
    configured
  ) {
    def text(terms: Vector[Term]): String =
      terms
        .map(term =>
          ReadableText
            .printedNameless(
              Defunctionalization
                .thunkInstruction[C](term.deBruijnTerm(Map.empty))
            )
            .text
        )
        .mkString(", ")
    for
      input <- JitReadingLaw.latticeTermsWithTop
        .forAllWithLog(text)
        .map(terms =>
          prepared(
            JitReadingLaw.internedAll(terms),
            normalFormsReader,
            JitReadingLaw.normalFormsLimit
          )
        )
      constructed <- JitReadingLaw.normalFormsBesideTop
        .forAllWithLog(text)
        .map(terms =>
          prepared(
            JitReadingLaw.internedAll(terms),
            normalFormsReader,
            JitReadingLaw.normalFormsLimit
          )
        )
    yield Result.all(
      List(
        agreed(
          input,
          normalFormsReader,
          JitReadingLaw.normalFormsLimit,
          referenceOnlyFails = true
        ),
        Result
          .assert(constructed.allFinished)
          .log(
            "tabling(weak_head) did not read a constructed term within the limit"
          ),
        agreed(
          constructed,
          normalFormsReader,
          JitReadingLaw.normalFormsLimit,
          referenceOnlyFails = true
        )
      )
    )
  }

  // ---- the arithmetic reduction problems, decoded ----

  /** The constructor trees the root decodes to as a Scott binary natural,
    * distinct and sorted.
    */
  private val binaryTreesReader: Reader[Vector[ConstructorTree]] =
    (mode, configuration, root, limit, jitState) =>
      ScottDecoding
        .decoded(mode, root, Scott.dataType("binary"))
        .collected
        .result(
          ReadingState.fresh(limit, configuration).copy(jitState = jitState)
        ) match
        case Computed.Done(trees, after) =>
          Read(
            Bounded.Finished(
              trees.distinct.sorted(com.yang_bo.gezi.ir.ContentComparison.ordering)
            ),
            after.jitState
          )
        case Computed.Stopped(after) =>
          Read(EvaluatorTesting.stopped(after), after.jitState)

  // Replaces theJitDecodesTheReductionProblemsAsTheReference, which decoded
  // the 203 fixed reduction problems of the corpus files jit.plt loads: here
  // one to three programs of the four arithmetic families
  // (`ReductionProblems`: Fibonacci, products, grid paths, sums in both
  // orders), the binary families whose single programs the contest's
  // repeated points draw, at small arguments.
  //
  // FIXME: a downgrade of the old test's domain. The 203 fixed problems also https://github.com/Atry/private-overlay/issues/1993
  // held boolean-valued and unary-valued reduction families, decoded by
  // their own Scott case analyses; this law decodes binary-valued programs
  // only, so a JIT defect on a boolean or unary decoding is no longer caught
  // here. Fix: generate programs of those families too, each decoded by its
  // own case analysis, beside the binary ones.
  property(
    "the JIT decodes the arithmetic reduction problems as tabling(weak_head) does",
    configured
  ) {
    for input <- JitReadingLaw.arithmeticPrograms
        .forAllWithLog(_.map(_.described).mkString(", "))
        .map(drawn =>
          prepared(
            JitReadingLaw.internedAll(drawn.map(_.program)),
            binaryTreesReader,
            JitReadingLaw.decodingLimit
          )
        )
    yield agreed(
      input,
      binaryTreesReader,
      JitReadingLaw.decodingLimit,
      referenceOnlyFails = false
    )
  }

  /** The same law on each family's program at argument 0, which
    * tabling(weak_head) decodes within the limit by construction: each family's
    * recursion takes its base case at once (fib 0 = 0, 0 · 0 = 0, the grid of
    * side 0 has one path, 0 + 0 = 0), so the reading decodes a constant
    * numeral. Its purpose is that the decoding law compares at least these
    * programs whatever the draws.
    */
  test(
    "the JIT decodes each arithmetic family's base case as tabling(weak_head) does"
  ) {
    val baseCases = Vector(
      ReductionProblems.fibonacciProgram(JitReadingLaw.group, 0),
      ReductionProblems
        .productProgram(JitReadingLaw.group, BigInt(0), BigInt(0)),
      ReductionProblems.gridProgram(JitReadingLaw.group, 0),
      ReductionProblems.sumBothOrdersProgram(
        JitReadingLaw.group,
        BigInt(0),
        BigInt(0)
      )
    )
    val input = prepared(
      JitReadingLaw.internedAll(baseCases),
      binaryTreesReader,
      JitReadingLaw.decodingLimit
    )
    assert(
      input.allFinished,
      "tabling(weak_head) did not decode a base case within the limit"
    )
    val verdict = agreed(
      input,
      binaryTreesReader,
      JitReadingLaw.decodingLimit,
      referenceOnlyFails = false
    )
    assert(verdict.success, verdict.logs.mkString("; "))
  }

  // ---- claims judged by witness ----

  /** The judge's ending of the claim test rooted at the root
    * (`ContestClaims.witness`); a reading the limit stops reads as not
    * finished.
    */
  private val endingReader: Reader[Ending] =
    (mode, configuration, root, limit, jitState) =>
      val witness = NeutralValue[C](ContestClaims.ClaimWitness, Vector.empty)
      val (readings, after) = Reading.witnessReadingsFrom(
        mode,
        Vector(root),
        witness,
        limit,
        jitState,
        configuration
      )
      readings match
        case Vector(reading) =>
          reading.outcome match
            case WitnessOutcome.Found =>
              Read(Bounded.Finished(Ending.Succeeded), after)
            case WitnessOutcome.NotFound =>
              Read(Bounded.Finished(Ending.Failed), after)
            case WitnessOutcome.StepLimit => Read(Bounded.Exceeded, after)
            case WitnessOutcome.Exhausted(resource) =>
              Read(Bounded.Exhausted(resource), after)
        case other =>
          throw IllegalStateException(s"one test gave ${other.size} readings")

  // Replaces theJitJudgesTheHardClaimsAsTheReference, which judged the
  // fixed hard claims: here one to three claims, each that a term is the
  // Scott unary numeral of a count (the hard corpus's natural template,
  // `HardClaims.numeralTest`), the term a numeral, a numeral in a choice
  // with a generated closed term, or a generated closed term, after two
  // claims of a numeral, one true and one false by construction
  // (`JitReadingLaw.decidedClaims`), which tabling(weak_head) is asserted to
  // judge so, so that the law compares judgments of both endings.
  property(
    "the JIT judges claims by witness as tabling(weak_head) does",
    configured
  ) {
    for
      decided <- JitReadingLaw.decidedClaims.forAllWithLog(
        _.map(_.described).mkString(", ")
      )
      input <- JitReadingLaw.numeralClaims
        .forAllWithLog(_.map(_.described).mkString(", "))
        .map(drawn =>
          prepared(
            JitReadingLaw.claimRoots[C](decided ++ drawn),
            endingReader,
            JitReadingLaw.claimLimit
          )
        )
    yield agreed(
      input,
      endingReader,
      JitReadingLaw.claimLimit,
      referenceOnlyFails = false
    ).and(
      Result
        .diff(
          input.references.take(2),
          Vector(
            Bounded.Finished(Ending.Succeeded),
            Bounded.Finished(Ending.Failed)
          )
        )(_ == _)
        .log("tabling(weak_head)'s judgments of the two decided claims")
    )
  }

  // ---- no file ----

  // The JIT writes no file (jit.plt's the_jit_writes_no_file): run in a
  // fresh working directory, reading the heads of generated programs of the
  // repeated families under the JIT, budget large, leaves that directory
  // empty and the tree of Gezi as it was, and compiles at least one
  // code. The readings run in a child JVM whose working directory is the
  // fresh one (`JitTesting.readInAFreshDirectory`), drawing its programs
  // from the seed this test passes, Hedgehog's (`HEDGEHOG_SEED` replays it).
  // The Prolog test also checked that every compiled predicate was dynamic
  // with no source file; a compiled code here is a closure in the reading's
  // state, with no counterpart of a predicate's properties.
  test("the JIT writes no file") {
    val seedSource = SeedSource.fromEnvOrTime()
    val count = JitReadingLaw.noFileInputs
    val run = JitTesting.readInAFreshDirectory(
      "com.yang_bo.gezi.contest.corpora.common.repeatedProgramsRead",
      Vector(seedSource.seed.toString, count.toString)
    )
    println(s"${seedSource.renderLog}; the child JVM: ${run.output.trim}")
    val expectedPrograms = SeededSamples
      .samples(JitReadingLaw.repeatedPrograms, seedSource.seed, count)
      .map(_.programs.size)
      .sum
    val compiledCount = run.output.trim match
      case s"programs read: $programs, codes compiled: $codes" =>
        assertEquals(programs.toInt, expectedPrograms)
        codes.toInt
      case other => fail(s"the child JVM printed $other")
    assert(compiledCount > 0)
    assertEquals(run.written, Vector.empty)
    assertEquals(run.after, run.before)
  }

/** The generated inputs of `JitReadingLawTest` and their limits. */
object JitReadingLaw:

  /** The inputs each property checks: `LAMBDAJIT_JIT_LAW_SAMPLES`, or 30. */
  val samples: Int =
    sys.env.get("LAMBDAJIT_JIT_LAW_SAMPLES").map(_.toInt).getOrElse(30)

  /** The inputs the child JVM of the no-file test reads: 2. The test needs a
    * compiled code, and one input already gives some: over the single inputs of
    * seeds 1 to 60 (2026-11-14) the JIT compiled 7 codes at the fewest.
    */
  val noFileInputs: Int = 2

  /** What the generators read, from the build's root. */
  lazy val group: ReductionGroup = ReductionGroup(
    HardCorpusFixture.corpus.claimsGroup.corpora.lambdaJit,
    Expansions.none,
    com.yang_bo.gezi.hotspot.baselines.BaselineCaches.provider()
  )

  /** The steps of a heads reading: 150,000. Over 100 inputs drawn at seed
    * 20261114 (2026-11-18), tabling(weak_head) read 202 of their 250 programs
    * within 200,000 steps (the small budget within which the judge's laws read
    * references, `MemberJudgmentsLawTest`), the most of them in 98,846 steps;
    * one more finished with heads too large to compare, and the other 47
    * stopped at the limit. A program that does not finish costs the limit under
    * tabling(weak_head) and under each of the JIT's three budgets, so the limit
    * sets the law's time; 150,000 keeps every program that finished within
    * 200,000, where 50,000 would have lost three.
    */
  val headsLimit: Long = 150000

  /** The nodes, written out as trees, of the largest heads the heads law
    * compares: a million. The answer whose comparison the FIXME at the heads
    * law describes had 1.93e10.
    */
  val comparedNodes: Long = 1000000

  /** The steps of a normal-form reading of a lattice term: 20,000, more than a
    * hundred times what tabling(weak_head) took on the largest of the
    * hand-written terms with top (`(λf. f I + f K) (λy. top ∥ y)`, 34 steps
    * knowing no extreme, measured 2026-11-18).
    */
  val normalFormsLimit: Long = 20000

  /** One to three closed lattice terms (`HoasGenerators.closedTermOver`) with
    * top (`Term.top`) among their leaves, at function and argument positions,
    * of at most 12 nodes besides top's own.
    */
  val latticeTermsWithTop: Gen[Vector[Term]] =
    HoasGenerators
      .closedTermOver(Vector(Term.top))
      .resize(hedgehog.Size(24))
      .list(Range.constant(1, 3))
      .map(_.toVector)

  /** One to three terms `x + top`, x a closed β normal form: an abstraction of
    * one or two binders whose body is a bound variable applied to zero to two
    * such forms, at most three levels deep, the shapes drawn before any binder
    * is opened.
    */
  val normalFormsBesideTop: Gen[Vector[Term]] =
    normalShape(3)
      .map(shape =>
        Term.choice(
          normalForm(shape.copy(binders = shape.binders max 1), Vector.empty),
          Term.top
        )
      )
      .list(Range.constant(1, 3))
      .map(_.toVector)

  /** The shape of a β normal form: its binders, the position of its head
    * variable among those in scope (taken modulo their count), and its
    * arguments' shapes.
    */
  final case class NormalShape(
      binders: Int,
      head: Int,
      arguments: Vector[NormalShape]
  )

  private def normalShape(depth: Int): Gen[NormalShape] =
    for
      binders <- Gen.int(Range.constant(0, 2))
      head <- Gen.int(Range.constant(0, 5))
      count <- Gen.int(Range.constant(0, if depth <= 0 then 0 else 2))
      arguments <-
        if count == 0 then Gen.constant(List.empty[NormalShape])
        else normalShape(depth - 1).list(Range.singleton(count))
    yield NormalShape(binders, head, arguments.toVector)

  /** The β normal form of the shape under the variables in scope; the scope is
    * never empty, the outermost shape having a binder.
    */
  private def normalForm(shape: NormalShape, scope: Vector[Term]): Term =
    def under(remaining: Int, inScope: Vector[Term]): Term =
      if remaining == 0 then
        shape.arguments.foldLeft(inScope(shape.head % inScope.size))(
          (applied, argument) => applied(normalForm(argument, inScope))
        )
      else Term.λ(bound => under(remaining - 1, inScope :+ bound))
    under(shape.binders, scope)

  /** Whether the heads, written out as trees (a subvalue counted once per
    * occurrence), have at most `bound` nodes; walks at most `bound + 1` of
    * them.
    */
  def treeNodesWithin[C <: NativeSpecializer & Singleton](
      heads: Vector[Head[C]],
      bound: Long
  )(using C): Boolean =
    def subvalues(node: Head[C] | Value[C]): Vector[Value[C]] = node match
      case Head.Lambda(_, _, fillings)     => fillings
      case Head.Neutral(_, arguments)      => arguments
      case Value.Apply(function, argument) => Vector(function, argument)
      case Value.Parallel(left, right)     => Vector(left, right)
      case Value.Choice(left, right)       => Vector(left, right)
      case Value.Thunk(_, _, fillings)     => fillings
      case NeutralValue(_, arguments)      => arguments
      case _                               => Vector.empty
    @scala.annotation.tailrec
    def counted(pending: List[Head[C] | Value[C]], count: Long): Boolean =
      if count > bound then false
      else
        pending match
          case Nil          => true
          case node :: rest =>
            counted(subvalues(node).toList ++ rest, count + 1)
    counted(heads.toList, 0)

  /** The steps of a decoding. */
  val decodingLimit: Long = 1000000

  /** The steps of a claim's judgment. */
  val claimLimit: Long = 100000

  /** The programs drawn for one input. */
  final case class Drawn(described: String, programs: Vector[Term])

  /** The families of `RepeatedVariants.families`, by name, whose programs
    * tabling(weak_head) reads within `headsLimit` on at least half the draws,
    * so that the heads law is not vacuous on them.
    *
    * MEASURED (2026-11-18, branch tabled-reference from main 6abea9081, a
    * scratch probe: every variant of `RepeatedVariants.all`, seeds 11, 22 and
    * 33, each repetition the generator draws; a draw counts when
    * tabling(weak_head) reads every program within 150,000 steps, its heads
    * within `comparedNodes`): 100% for the families reduction_interpreter,
    * set_free_premises, set_free_list_laws, reduction_problems_fibonacci,
    * reduction_problems_products, reduction_problems_sums, set_free_arithmetic,
    * identical_subterms, closures, library_compositions, general_compositions,
    * nested_compositions, library_doubling_parities, library_binary_parities
    * and library_binary_domain_traps; 67% for set_free_scope and
    * reduction_problems_grids. Below half: reduction_meanings 17%, the
    * library_hotspots variants calls_10000_cold 17% and calls_1000000_cold 8%,
    * and 0% for reduction_mixin_binary and every other library family (the
    * other library_hotspots variants, billboards, edit_distances,
    * longest_common_subsequences, smallest_teams, the unshared ones and
    * word_powers). Over all 89 variants the share is 28%, over the 25 variants
    * of these families 97%.
    *
    * FIXME: re-probe when variants are added; a family here that stops
    * https://github.com/Atry/private-overlay/issues/1993 finishing lowers the
    * cover.
    */
  val readableFamilies: Vector[String] = Vector(
    "repeated_reduction_interpreter",
    "repeated_set_free_premises",
    "repeated_set_free_scope",
    "repeated_reduction_problems_products",
    "repeated_reduction_problems_sums",
    "repeated_set_free_arithmetic",
    "repeated_identical_subterms",
    "repeated_closures",
    "repeated_library_compositions",
    "repeated_general_compositions",
    "repeated_nested_compositions",
    "repeated_library_binary_domain_traps",
    "repeated_set_free_list_laws",
    "repeated_reduction_problems_fibonacci",
    "repeated_reduction_problems_grids",
    "repeated_library_doubling_parities",
    "repeated_library_binary_parities"
  )

  /** The variants of `readableFamilies`. Throws `IllegalStateException` when
    * one of the names is no family of `RepeatedVariants.families`.
    */
  lazy val readableVariants: Vector[RepeatedVariant] =
    val byName = RepeatedVariants.families.toMap
    readableFamilies.flatMap(name =>
      byName.getOrElse(
        name,
        throw IllegalStateException(
          s"$name is no family of RepeatedVariants.families"
        )
      )
    )

  /** A variant of the contest's repeated families, a seed and one or two
    * repetitions: the variant's single programs and its repeated program. The
    * variant is drawn with probability one half from `readableVariants` and
    * otherwise from every variant, so that every family can be drawn and the
    * heads law's cover stays above its threshold: the share expected from the
    * measurement at `readableFamilies` is 0.5 × 0.97 + 0.5 × 0.28 = 0.63, below
    * 10% in 30 inputs with a probability of about 2e-10. Every variant but the
    * CSES families' top rungs (`CsesFamilies.atConstraints`), whose sites are
    * CSES inputs: one site of counting_rooms' top rung took 14.6 s to build and
    * convert and one of message_route's 23 s (2026-11-21, a scratch probe,
    * `CsesEncodings`), and a draw builds each site twice, in its single program
    * and in the repeated one, against this law's 60 s.
    */
  val repeatedPrograms: Gen[Drawn] =
    for
      variant <- Gen.frequency1(
        1 -> Gen.elementUnsafe(readableVariants.toList),
        1 -> Gen.elementUnsafe(
          RepeatedVariants.all
            .filterNot(CsesFamilies.atConstraints.contains)
            .toList
        )
      )
      seed <- Gen.long(Range.constant(0L, (1L << 31) - 1))
      repetitions <- Gen.int(
        Range.constant(1, math.min(2, variant.nominal.repetitions.end))
      )
    yield Drawn(
      s"${variant.stem}, seed $seed, $repetitions repetitions",
      variant.singlePrograms(group, seed, repetitions) :+ variant.program(
        group,
        seed,
        repetitions
      )
    )

  /** A program and what it computes. */
  final case class Described(described: String, program: Term)

  /** A program of one of the four arithmetic reduction families, every one a
    * Scott binary natural: fib(n) for n up to 12, a product of two numbers up
    * to 63, the grid paths of a side up to 4, and the sums of two numbers up to
    * 255 in both orders. Every range is drawn uniformly whatever Hedgehog's
    * size (`Range.constant`), since 30 inputs reach only the first 30 of its
    * sizes; a failure shrinks towards zero.
    */
  val arithmeticProgram: Gen[Described] =
    Gen.choice1(
      Gen
        .int(Range.constant(0, 12))
        .map(number =>
          Described(
            s"fibonacci $number",
            ReductionProblems.fibonacciProgram(group, number)
          )
        ),
      for
        left <- Gen.int(Range.constant(0, 63))
        right <- Gen.int(Range.constant(0, 63))
      yield Described(
        s"product $left $right",
        ReductionProblems.productProgram(group, BigInt(left), BigInt(right))
      ),
      Gen
        .int(Range.constant(0, 4))
        .map(side =>
          Described(s"grid $side", ReductionProblems.gridProgram(group, side))
        ),
      for
        left <- Gen.int(Range.constant(0, 255))
        right <- Gen.int(Range.constant(0, 255))
      yield Described(
        s"sums $left $right",
        ReductionProblems.sumBothOrdersProgram(
          group,
          BigInt(left),
          BigInt(right)
        )
      )
    )

  /** One to three arithmetic programs. */
  val arithmeticPrograms: Gen[Vector[Described]] =
    arithmeticProgram.list(Range.constant(1, 3)).map(_.toVector)

  /** A claim that the term is the Scott unary numeral of the count. */
  final case class NumeralClaim(described: String, term: Term, count: Int)

  /** A claim whose term is the numeral of n up to 5, the same numeral in a
    * choice with a generated closed term (`HoasGenerators.closedTerm` over no
    * library name), or a generated closed term; the count is n or its
    * neighbours for a numeral (the hard corpus's wrong values,
    * `HardClaims.wrongTemplates`), and up to 3 for a generated term.
    */
  val numeralClaim: Gen[NumeralClaim] =
    val closed = HoasGenerators.closedTerm.resize(hedgehog.Size(12))
    def neighbour(number: Int): Gen[Int] =
      Gen.int(Range.constant(math.max(0, number - 1), number + 1))
    Gen.choice1(
      for
        number <- Gen.int(Range.constant(0, 5))
        count <- neighbour(number)
      yield NumeralClaim(
        s"numeral $number is $count",
        Encodings.unary(number),
        count
      ),
      for
        number <- Gen.int(Range.constant(0, 5))
        other <- closed
        count <- neighbour(number)
      yield NumeralClaim(
        s"numeral $number + $other is $count",
        Term.choice(Encodings.unary(number), other),
        count
      ),
      for
        other <- closed
        count <- Gen.int(Range.constant(0, 3))
      yield NumeralClaim(s"$other is $count", other, count)
    )

  /** One to three claims. */
  val numeralClaims: Gen[Vector[NumeralClaim]] =
    numeralClaim.list(Range.constant(1, 3)).map(_.toVector)

  /** Two claims of the numeral of n up to 5, the first true by construction
    * (its count n), the second false (its count n + 1).
    */
  val decidedClaims: Gen[Vector[NumeralClaim]] =
    for number <- Gen.int(Range.constant(0, 5))
    yield Vector(
      NumeralClaim(
        s"numeral $number is $number",
        Encodings.unary(number),
        number
      ),
      NumeralClaim(
        s"numeral $number is ${number + 1}",
        Encodings.unary(number),
        number + 1
      )
    )

  /** The claims' tests rooted (`ContestClaims.testRoot`), each the natural
    * template's body over the term (`HardClaims.claimTest`).
    */
  def claimRoots[C <: NativeSpecializer & Singleton](
      claims: Vector[NumeralClaim]
  )(using specializer: C): Vector[Value[C]] =
    val hardClaims = HardCorpusFixture.corpus.claimsGroup.claims
    claims.map { claim =>
      val test = OpenTest(
        1,
        free =>
          Term.λ(argument =>
            hardClaims.numeralTest(claim.count, claim.term, argument, free(0))
          )
      )
      ContestClaims.testRootIn(specializer)(test)
    }

  /** The closed programs interned whole, as the corpora intern their programs
    * (`interned_root/2`, `program_root/2`).
    */
  def internedAll[C <: NativeSpecializer & Singleton](
      programs: Vector[Term]
  )(using C): Vector[Value[C]] =
    programs.map(program =>
      Value.of(
        Defunctionalization.thunkInstruction[C](program.deBruijnTerm(Map.empty))
      )
    )

  /** The count of the codes the JIT compiled while reading the heads of the
    * programs of `count` inputs drawn from the seed, every program interned
    * first, under the budget large with the cache kept from one program to the
    * next, each within `headsLimit`; and the count of the programs read. The
    * heads are left as the JIT read them, not encoded back into plain values:
    * the readback writes no file, so the test does not need it.
    */
  def compiledCount(seed: Long, count: Int): (Int, Int) =
    val programs =
      SeededSamples.samples(repeatedPrograms, seed, count).flatMap(_.programs)
    val encoding = JitTesting.noFactsEncoding
    given encoding.type = encoding
    val evaluator = Jit(JitTesting.configured(encoding, 10000))
    val roots = internedAll[encoding.type](programs)
    val after =
      roots.foldLeft(NoJitState: JitState[encoding.type])((jitState, root) =>
        WeakHead
          .heads(Mode.Jit, root)
          .collected
          .result(
            ReadingState
              .fresh(headsLimit, evaluator.readingConfiguration)
              .copy(jitState = jitState)
          ) match
          case Computed.Done(_, read) => read.jitState
          case Computed.Stopped(read) => read.jitState
      )
    (programs.size, JitTesting.compiledCodes(after).size)

/** The main class of the child JVM of `JitReadingLawTest`'s no-file test, given
  * the seed and the count of inputs: it prints the count of the programs read
  * and of the codes compiled.
  */
@main def repeatedProgramsRead(seed: Long, count: Int): Unit =
  val (programs, codes) = JitReadingLaw.compiledCount(seed, count)
  println(s"programs read: $programs, codes compiled: $codes")
