package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.proofs.ArticleDerivation
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteRound
import gezi.proofs.RewriteTrace
import gezi.proofs.StrategyProof
import gezi.rewritetrace.Given
import gezi.rewritetrace.Positions
import gezi.rewritetrace.ProvedReason
import gezi.rewritetrace.ReplayedStep
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceCommand
import gezi.rewritetrace.TracePageText
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText
import gezi.saturation.StopSignal
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex
import snapshot4s.generated.snapshotConfig

/** The laws of the rewrite trace on generated rounds: a generated closed
  * program saturated by the baseline's strategy under four lemmas sound by
  * the formal definition (the choice's commutativity, associativity and
  * idempotence, and two steps of the β rule on K = λx. λy. x) and the
  * built-in rules, its proof wanted; the steps the flattening of the proof
  * the article writer builds for that round (`OpentheoryArticle.derivation`),
  * and the trace of commands that keeps of them what a replay cannot
  * compute (`RewriteTrace.trace`). A second round, of the higher-order
  * saturator under a higher-order lemma, has β conversions with no proof,
  * which the trace keeps as `Convert` commands whose replacements the
  * replay computes.
  *
  * The suite is in `strategies` because it runs the strategy.
  */
class RewriteTraceLawTest extends GeneratedProperties with SeededSnapshots:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private given NoFacts.type = NoFacts
  import RewriteTraceLawTest.*

  private val lemmas: Vector[LemmaSides[NoFacts.type]] = Vector(
    equation(0, "λa. λb. (a + b)", "λa. λb. (b + a)"),
    equation(1, "λa. λb. λc. ((a + b) + c)", "λa. λb. λc. (a + (b + c))"),
    equation(2, "λa. (a + a)", "λa. a"),
    equation(3, "λa. λb. (λx. λy. x) a b", "λa. λb. a")
  )

  private val index: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(NoFacts, Vector.empty, lemmas, Vector.empty, Vector.empty)

  /** The instances a round may add: twice the most a round of the generated
    * programs added, measured on 2026-11-13 (main 3939b8fca) on 100 programs
    * drawn by `SeededSamples` from the seed 20261113, at sizes 1 to the
    * maximum: every round reached its fixed point, after at most 12
    * instances.
    */
  private val budget: Int = 24

  private val strategy: FixpointEgraph[NoFacts.type] = FixpointEgraph(
    index,
    StandardSaturator(
      SaturationOptions(lemmas.map(_.lemma), BuiltInRule.beforeOptIn, budget, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer.of[gezi.ir.NoFacts.type], StandardOrientationCompiler, MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts))
    ),
    CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table[gezi.ir.NoFacts.type])
  )

  /** A program the lemmas rewrite: a choice of two to four closed terms, or
    * a closed term in choice with K applied to two.
    */
  private val programs: Gen[String] =
    Gen.choice1(
      closedText.list(Range.linear(2, 4)).map(_.map(member => s"($member)").mkString(" + ")),
      for
        context <- closedText
        first <- closedText
        second <- closedText
      yield s"($context) + (λk. λl. k) ($first) ($second)"
    )

  /** The derivation of the round of the strategy on the program. */
  private def derivation(program: String, stop: StopSignal): ArticleDerivation[NoFacts.type] =
    val input = closed(program)
    val outcome = strategy.ran(Vector(input), true, stop).getOrElse(fail("the strategy gave no answer"))
    val Vector(output) = outcome.outputs: @unchecked
    val proof = outcome.proof.getOrElse(fail("the strategy gave no proof"))
    OpentheoryArticle.derivation(index, input, output, proof)

  /** Purpose: catch an article writer whose article of a round the
    * opentheory tool does not accept, or whose proof does not need its
    * symmetries: the article of a first-order round is accepted, and, when
    * it has a `sym`, refused with its first or its last `sym` deleted.
    */
  stoppableProperty(
    "a first-order round's article is accepted by the opentheory tool and refused without a sym",
    // Each article costs one to three runs of the tool, 0.1 s to 0.4 s each: 20 rounds took 3.2 s, over the default
    // deadline (measured 2026-11-22, two cores, load 1.3), so the law checks 10.
    _.copy(testLimit = hedgehog.core.SuccessCount(10))
  ) { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val input = closed(program)
      val outcome = strategy.ran(Vector(input), true, StopSignal.completedWith(stopped)).getOrElse(fail("the strategy gave no answer"))
      val Vector(output) = outcome.outputs: @unchecked
      val proof = outcome.proof.getOrElse(fail("the strategy gave no proof"))
      val article = OpentheoryArticle.text(index, input, output, proof)
      val refusals =
        if article.split("\n", -1).contains("sym") then
          Vector(false, true).map(last => gezi.proofs.ProofTestFiles.checkedWithoutSym(article, last))
        else Vector.empty
      Result.all(
        Result.diff(gezi.proofs.ProofTestFiles.textChecked(article), (0, ""))(_ == _) ::
          refusals.toList.map((status, errors) => Result.assert(status == 1 && errors.contains("terms not alpha-equivalent")).log(errors))
      )
    )
  }

  /** Purpose: catch a flattening that loses, duplicates, misplaces or
    * misorders a step, so that the steps no longer make the round's output
    * of its input.
    */
  stoppableProperty("replaying the steps of a round from its input gives its output") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val round = RewriteTrace.round(derivation(program, StopSignal.completedWith(stopped)))
      Result.assert(replayed(round).last eq round.output).log(s"${round.steps.size} steps")
    )
  }

  /** Purpose: catch a command that keeps too little to replay its step (a
    * binding left out, a thunk not written backward, a lemma stated
    * otherwise than the strategy's encoding) or replays it otherwise than the
    * proof: the replay of the trace's commands must give each step's
    * position, replacement and provenance, and the round's output. The
    * steps are the proof's with each two side by side that are an identity
    * together left out, as the trace leaves them out (`RewriteTrace`'s
    * `detoursDropped`): a lemma of the choice turned forward and straight
    * back. The rounds here are first-order, whose terms are their own replay
    * spelling, so the identity is read on the terms as they are.
    */
  stoppableProperty("replaying a trace's commands gives the steps of the proof") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val run = derivation(program, StopSignal.completedWith(stopped))
      val proofSteps = RewriteTrace.of(run)
      val replacedSubterms = proofSteps
        .zip(proofSteps.scanLeft(run.left)(RewriteTrace.applied[NoFacts.type]))
        .map((step, before) => Positions.subterm(before, step.position))
      val steps = proofSteps
        .zip(replacedSubterms)
        .foldLeft(List.empty[(gezi.proofs.RewriteStep[NoFacts.type], Configured[NoFacts.type])]) { case (kept, (step, replaced)) =>
          kept match
            case (last, lastReplaced) :: earlier
                if last.position == step.position && (lastReplaced eq step.replacement) && (last.replacement eq replaced) =>
              earlier
            case _ => (step, replaced) :: kept
        }
        .reverse
        .map(_._1)
        .toVector
      val trace = RewriteTrace.trace(run)
      val Vector(replayedSteps) = trace.replayed(run.left): @unchecked
      val problems = steps.zip(replayedSteps).zipWithIndex.flatMap { case ((step, replayedStep), place) =>
        Option.when(
          step.position != replayedStep.command.at ||
            !(step.replacement eq replayedStep.replacement) ||
            step.provenance != replayedStep.provenance
        )(s"step $place: $step replays as $replayedStep")
      }
      Result
        .all(
          List(
            Result.assert(steps.size == replayedSteps.size).log(s"${steps.size} steps, ${replayedSteps.size} replayed"),
            Result.assert(problems.isEmpty).log(problems.mkString("\n")),
            Result.assert(trace.output(run.left) eq run.right).log("the replay's output is not the round's")
          )
        )
        .log(s"${steps.size} steps")
    )
  }

  /** Purpose: catch a term of the IR written in a trace where the proof
    * gives its origin: a first-order round opens no body, so every term a
    * command gives is the term of a node the round's input holds or a union
    * made, named by its value.
    */
  stoppableProperty("a first-order round's trace writes no term a command gives") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val trace = RewriteTrace.trace(derivation(program, StopSignal.completedWith(stopped)))
      val written = (trace.rounds.flatten ++ trace.values.flatMap(_.commands)).flatMap(writtenTerms)
      Result.assert(written.isEmpty).log(s"${written.size} terms written: ${written.mkString(", ")}")
    )
  }

  /** K applied to two distinct closed terms, in choice with the first: the
    * proof joins the choice to its member through the instance of K, and
    * crosses it from the member back to K's application (the showcase of
    * 2026-11-17, `(λk. λl. k) (λa. a) (λb. b b) + (λa. a)`), a step backward
    * whose second argument only the value of a node gives.
    */
  private val choicesOfK: Gen[String] =
    for
      first <- closedText
      second <- closedText.filter(_ != first)
    yield s"(λk. λl. k) ($first) ($second) + ($first)"

  /** Purpose: catch the law above holding vacuously, a trace whose steps
    * backward give no term, or one that gives the terms of its values by
    * writing them.
    */
  stoppableProperty("a trace of K's application in choice with its first argument names a value") { stopped =>
    choicesOfK.forAllWithLog(identity).map(program =>
      val trace = RewriteTrace.trace(derivation(program, StopSignal.completedWith(stopped)))
      Result.assert(trace.values.nonEmpty).log(TraceText.written(trace))
    )
  }

  /** Purpose: catch a provenance mapping whose positions do not take a
    * variable's subtree from the replaced subterm to the same subtree of the
    * replacement.
    */
  stoppableProperty("the provenance of a step maps each subtree to an equal subtree") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val run = derivation(program, StopSignal.completedWith(stopped))
      val Vector(steps) = RewriteTrace.trace(run).replayed(run.left): @unchecked
      val problems = provenanceProblems(steps)
      Result.assert(problems.isEmpty).log(problems.mkString("\n"))
    )
  }

  /** The steps whose provenance takes a variable's subtree to another
    * subtree, or reads two different subtrees for one variable.
    */
  private def provenanceProblems(steps: Vector[ReplayedStep[NoFacts.type]]): Vector[String] =
    steps.zipWithIndex.flatMap((step, place) =>
      step.provenance.flatMap(found =>
        val sources = found.before.map(Positions.subterm(step.replaced, _)).distinct
        val targets = found.after.map(Positions.subterm(step.replacement, _)).distinct
        Option.when(sources.size > 1 || targets.size > 1 || (sources.nonEmpty && targets.nonEmpty && !(sources == targets)))(
          s"step $place: ${found.variable} takes $sources to $targets"
        )
      )
    )

  /** Purpose: catch a writer and a reader of the trace's text that disagree:
    * a constructor, a field or an integer written otherwise than it is read,
    * or a term the front end reads back as another instruction.
    */
  stoppableProperty("reading the text of a trace gives the trace") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val trace = RewriteTrace.trace(derivation(program, StopSignal.completedWith(stopped)))
      val text = TraceText.written(trace)
      Result.assert(TraceText.read(text, readingLimit(text)) == trace).log(text)
    )
  }

  /** The round of the strategy with the lemmas of the places given. */
  private def roundOf(places: Vector[Int]): Round[NoFacts.type] =
    Round(
      FixpointEgraph(
        index,
        StandardSaturator(
          SaturationOptions(places.map(lemmas(_).lemma), BuiltInRule.beforeOptIn, budget, BaselineLemmaEncoding, ClosureCompilation, StandardIndexer.of[gezi.ir.NoFacts.type], StandardOrientationCompiler, MemoRetention.Kept, gezi.ir.TermConstruction(gezi.ir.NoFacts))
        ),
        CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table[gezi.ir.NoFacts.type])
      ),
      None
    )

  /** Purpose: catch a schedule's trace file that does not replay its rounds:
    * a round
    * left out or put twice, a lemma place of a later round not renumbered
    * into the joined lemmas, or a file the reader reads otherwise. Two
    * articled rounds, K's β step alone and then the choice's laws alone, so
    * that the second round's lemmas start at another place than in the
    * joined trace; the start file beside it (`TraceFiles.startFile`) reads
    * back as the input, and the trace read back replays from it to the
    * schedule's output, one round of commands each. It also catches a
    * player's page beside the file that does not embed the
    * start's text and the trace's text, each in its own script element.
    */
  stoppableProperty("a schedule's trace file replays its rounds from the input to the output") { stopped =>
    programs.forAllWithLog(identity).map(program =>
      val input = closed(program)
      val directory = java.nio.file.Files.createTempDirectory("schedule_trace")
      val rounds = Schedule.articled(Vector(roundOf(Vector(3)), roundOf(Vector(0, 1, 2))), directory, 1)
      val scheduled = Schedule.run(index, Vector(input), rounds, StopSignal.completedWith(stopped))
      val file = Schedule.traceFile(rounds).getOrElse(fail("articled rounds have no trace file"))
      val text = java.nio.file.Files.readString(file)
      val startText = java.nio.file.Files.readString(TraceFiles.startFile(file))
      val trace = TraceText.read(text, readingLimit(text))
      val start = TraceStart.readLocated(startText, java.net.URI("trace:start")).start
      val page = java.nio.file.Files.readString(TraceFiles.pageFile(file))
      (rounds.flatMap(_.article) :+ file :+ TraceFiles.startFile(file) :+ TraceFiles.pageFile(file) :+ directory)
        .foreach(java.nio.file.Files.delete)
      val Vector(output) = scheduled.outputs: @unchecked
      Result
        .all(
          List(
            Result.assert(start eq input).log("the start file does not read back as the input"),
            Result.assert(trace.rounds.size == 2).log(s"${trace.rounds.size} rounds"),
            Result.assert(trace.output(start) eq output).log("the replay's output is not the schedule's"),
            Result
              .assert(
                page.contains(
                  s"""<script type="${TracePageText.traceType}" data-role="${TracePageText.startRole}">$startText</script>"""
                )
              )
              .log("the page does not embed the start's text"),
            Result
              .assert(
                page.contains(
                  s"""<script type="${TracePageText.traceType}" data-role="${TracePageText.traceRole}">$text</script>"""
                )
              )
              .log("the page does not embed the trace's text")
          )
        )
        .log(text)
    )
  }

  /** K applied to a choice of a closed term with itself and to another
    * closed term: the first round, K's β step alone (`roundOf(Vector(3))`),
    * makes the choice, and the second, the choice's laws alone, rewrites it,
    * so that each round makes a step.
    */
  private val choicesOfThemselvesUnderK: Gen[String] =
    for
      member <- closedText
      other <- closedText
    yield s"(λk. λl. k) (($member) + ($member)) ($other)"

  /** The trace of a round of the strategy with the lemmas of the places on
    * the input, and the round's output.
    */
  private def tracedRound(places: Vector[Int], input: Configured[NoFacts.type], stop: StopSignal): (Trace[NoFacts.type], Configured[NoFacts.type]) =
    val outcome = roundOf(places).strategy.ran(Vector(input), true, stop).getOrElse(fail("the strategy gave no answer"))
    val Vector(output) = outcome.outputs: @unchecked
    val proof = outcome.proof.getOrElse(fail("the strategy gave no proof"))
    (RewriteTrace.trace(OpentheoryArticle.derivation(index, input, output, proof)), output)

  /** Purpose: catch a join (`Trace.joined`) that accepts two rounds' traces
    * in the wrong order, and a replay that gives a term for a trace replayed
    * from a term other than its start, now that a trace holds no start
    * and the start
    * each trace is given is all that tells the rounds' order. The joined trace
    * in the right order replays from the first start to the second round's
    * output, so that the order alone makes the join throw.
    */
  stoppableProperty("joining two rounds' traces in the wrong order or replaying a trace from another start throws") { stopped =>
    choicesOfThemselvesUnderK.forAllWithLog(identity).map(program =>
      val stop = StopSignal.completedWith(stopped)
      val firstStart = closed(program)
      val (firstTrace, secondStart) = tracedRound(Vector(3), firstStart, stop)
      val (secondTrace, secondOutput) = tracedRound(Vector(0, 1, 2), secondStart, stop)
      if (secondStart eq firstStart) || secondTrace.rounds.flatten.isEmpty then
        Result.failure.log(
          s"the first round made no step, or the second round no command: the generator drifted (${secondTrace.rounds.flatten.size} commands)"
        )
      else
        intercept[IllegalArgumentException](Trace.joined(Vector((secondStart, secondTrace), (firstStart, firstTrace))))
        intercept[IllegalArgumentException](secondTrace.replayed(firstStart))
        Result
          .assert(Trace.joined(Vector((firstStart, firstTrace), (secondStart, secondTrace))).output(firstStart) eq secondOutput)
          .log("the traces joined in order do not replay to the second round's output")
    )
  }

  /** Purpose: catch a β conversion (`Justification.BetaConversion`) that the
    * flattening loses, misplaces or turns the wrong way, a `Convert` command
    * whose replay computes another term than the proof's, a text of it read
    * back otherwise, a conversion's provenance that takes a variable's
    * subtree elsewhere, or a conversion the article writer refuses: the
    * replay of the trace of a higher-order round must give the round's
    * output, its text must read back as the trace, its provenance must map
    * subtrees to equal ones, the trace must hold a `Convert` command, without
    * which the law checks none, and the writer must write the round's
    * article, each conversion an import (`gezi.proofs.Axiom.Conversion`).
    */
  stoppableProperty("the trace of a higher-order round with β conversions replays and reads back, and its article is written") { stopped =>

    higherOrderPrograms.forAllWithLog(identity).map(program => higherOrderTraced(program, stopped))
  }

  /** Purpose: keep the input that found a solution of the higher-order
    * matching whose binding normal form is not the term it matched, which the
    * matching now drops (`HigherOrderMatching.admitted`): HEDGEHOG_SEED
    * 73277739101918 drew it, the class of `λw. I I` holding the redex
    * `(λx. λz. I x) I` by an instance of the first lemma. A fixed input beside
    * the generated ones (2026-11-16).
    */
  stoppableTest("the trace of a higher-order round whose filling's class holds a redex of it replays and reads back") {
    stopped =>
      higherOrderTraced("(λx. λz. x (λx_0. (λx_1. x_1) (λx_1. x_1))) (λx_0. x_0)", stopped) match
        case Result.Success       => ()
        case Result.Failure(logs) => fail(logs.mkString("\n"))
  }

  /** The law of a higher-order round's trace on the program (the property
    * above).
    */
  private def higherOrderTraced(program: String, stopped: scala.concurrent.Future[Unit]): Result =
    val (input, output, proof) = higherOrderRan(program, stopped)
    val trace = RewriteTrace.trace(OpentheoryArticle.derivation(higherOrderIndex, input, output, proof))
    val conversions = trace.rounds.flatten.count {
      case TraceCommand.Convert(_, _, _, _) => true
      case _                                => false
    }
    val text = TraceText.written(trace)
    val article = OpentheoryArticle.text(higherOrderIndex, input, output, proof)
    Result
      .all(
        List(
          Result.assert(conversions > 0).log("the trace holds no Convert command"),
          // The writer throws on a union it cannot write; a written article ends with its exported theorem.
          Result.assert(article.linesIterator.toVector.lastOption.contains("thm")).log(article),
          // The trace replays to the output's spelling (`traceProblems`): the round's output may be a node in another
          // spelling, such as `λz. I I` with two equal fillings that a lemma's side as stated adds.
          Result.assert(traceProblems(trace.output(input), output).isEmpty).log(traceProblems(trace.output(input), output).mkString),
          Result.assert(TraceText.read(text, readingLimit(text)) == trace).log(text),
          Result.assert(provenanceProblems(trace.replayed(input).flatten).isEmpty)
            .log(provenanceProblems(trace.replayed(input).flatten).mkString("\n"))
        )
      )
      .log(s"${trace.rounds.flatten.size} commands, $conversions of them Convert")

  /** Purpose: catch an abstraction step (the rule ξ of a body written back)
    * that the flattening loses or turns wrong, an `Abstraction` command
    * whose replay opens, rewrites or writes back otherwise than the proof,
    * or its text read back otherwise (the eigenvariables under λ): the
    * trace of a round that writes a body back must replay to its output,
    * read back as itself, and hold an `Abstraction` command.
    */
  stoppableProperty("the trace of a round that writes a body back replays and reads back") { stopped =>
    openingPrograms.forAllWithLog(identity).map(program =>
      val (input, output, proof) = openingRan(program, stopped)
      val trace = RewriteTrace.trace(OpentheoryArticle.derivation(openingIndex, input, output, proof))
      val abstractions = trace.rounds.flatten.count {
        case TraceCommand.Abstraction(_, _, _) => true
        case _                                 => false
      }
      val text = TraceText.written(trace)
      Result
        .all(
          List(
            Result.assert(abstractions > 0).log("the trace holds no Abstraction command"),
            Result.assert(trace.output(input) eq output).log("the replay's output is not the round's"),
            Result.assert(TraceText.read(text, readingLimit(text)) == trace).log(text)
          )
        )
        .log(s"${trace.rounds.flatten.size} commands, $abstractions of them Abstraction")
    )
  }

  /** The instances a round may add: twice the most a round of the generated
    * programs added, measured on 2026-11-16 (beta-canonical-residual
    * 0889404e9) on 100 programs drawn by `SeededSamples` from the seed
    * 20261116 under a budget of 1,000: every round reached its fixed point
    * after 1 instance.
    */
  private val residualBudget: Int = 2

  private val residualSaturator: StandardSaturator[NoFacts.type] = StandardSaturator(
    SaturationOptions(
      residualLemmas.map(_.lemma),
      BuiltInRule.beforeOptIn,
      residualBudget,
      BaselineLemmaEncoding,
      ClosureCompilation,
      StandardIndexer.of[gezi.ir.NoFacts.type],
      StandardOrientationCompiler,
      MemoRetention.Kept
    , gezi.ir.TermConstruction(gezi.ir.NoFacts))
  )

  /** `(λu. u) (T A)`, T a lambda of `ResidualPrograms`, whose β residual
    * is not the front end's spelling, and A a generated closed term.
    */
  private val residualPrograms: Gen[Term] =
    for
      function <- ResidualPrograms.lambdas
      argument <- HoasGenerators.closedTerm
    yield Term.λ(bound => bound)(function(argument))

  /** Purpose: catch a β union that leaves a residual thunk and that the
    * article writer cannot derive (`ProofMatching`'s residual β proofs: the
    * thunk filled, then matched against the residual node), or derives
    * otherwise than the graph: for every residual thunk in the input's
    * class, the derivation of `input = residual` is written, its steps
    * replay from the input to the residual, and its trace to the residual's
    * front-end spelling, the same lambda term (`traceProblems`). The law asserts that the class holds a residual, without
    * which it checks none.
    */
  stoppableProperty("a β union that leaves a residual is derived, and its steps and its trace replay to it") { stopped =>
    residualPrograms.forAllWithLog(LambdalatticeText.text).map(program =>
      val input = Defunctionalization.thunkInstruction[NoFacts.type](program.deBruijnTerm(Map.empty))
      val run = residualSaturator.saturated(residualIndex, Vector(input), true, StopSignal.completedWith(stopped))
      val Vector(inputNode) = run.inputNodes: @unchecked
      val encoded = residualSaturator.lemmas(residualIndex)
      val terms = OpentheoryArticle.derivation(residualIndex, input, input, GraphProof.proof(run.graph, Vector((input, input)), encoded)).nodeTerm
      val residuals = (0 until run.graph.nodeCount)
        .filter(node => run.graph.root(node) == run.graph.root(inputNode))
        .map(terms)
        .filter(residual => residual.layer match
          case gezi.ir.Thunk(_, holes, _) => holes.nonEmpty
          case _                          => false
        )
        .distinct
      val problems = residuals.flatMap(residual =>
        val derivation =
          OpentheoryArticle.derivation(residualIndex, input, residual, GraphProof.proof(run.graph, Vector((input, residual)), encoded))
        Option.when(!(replayed(RewriteTrace.round(derivation)).last eq residual))(s"the steps do not replay to $residual") ++
          traceProblems(RewriteTrace.trace(derivation).output(input), residual)
      )
      Result
        .all(
          List(
            Result.assert(residuals.nonEmpty).log("the input's class holds no residual: the generator drifted"),
            Result.assert(problems.isEmpty).log(problems.mkString("\n"))
          )
        )
        .log(s"${residuals.size} residuals")
    )
  }

  /** Purpose: show, as a diff, every change of the text a trace is written
    * as (its constructors, its layout, the terms it writes and the commands
    * it keeps), on the traces of programs drawn from a fixed seed.
    */
  stoppableTest("the text of the traces of generated programs") { stopped =>
    assertSeededSnapshot(programs, 20261113L, 4, "rewrite-trace/texts.txt")(
      identity,
      identity[String]
    )(program => TraceText.written(RewriteTrace.trace(derivation(program, StopSignal.completedWith(stopped)))))
  }

  /** Purpose: show, as a diff, how the size of a trace's text grows with the
    * depth of its steps' positions, on right-nested choices of 2, 4, 8 and 16
    * idempotent pairs `T + T`, each T a closed term drawn from a fixed seed,
    * so that the proof rewrites a pair at each depth: each command's
    * position is written
    * as a move from the one before it (`TraceText`'s MOVE), so that the text
    * grows with the commands and not with the commands times the depth,
    * which the sum of the positions' lengths shows beside it.
    */
  stoppableTest("the size of a trace's text on deeper choices") { stopped =>
    val members = gezi.generatedinputs.SeededSamples.samples(closedText, 20261117L, 16)
    val lines = Vector(2, 4, 8, 16).map(count =>
      val program = members.take(count).map(member => s"(($member) + ($member))").reduceRight((member, rest) => s"($rest) + $member")
      val trace = RewriteTrace.trace(derivation(program, StopSignal.completedWith(stopped)))
      val commands = trace.rounds.flatten
      val text = TraceText.written(trace)
      s"$count members: ${commands.size} commands, ${commands.map(_.at.size).sum} position segments, " +
        s"${text.getBytes(java.nio.charset.StandardCharsets.UTF_8).length} bytes of text"
    )
    assertFileSnapshot(lines.mkString("\n") + "\n", "rewrite-trace/text-sizes.txt")
  }

/** The definitions `RewriteTraceLawTest` shares with `ResidualRoundLawTest` and
  * `RoundCertificateCheckTest`.
  */
object RewriteTraceLawTest:

  private given NoFacts.type = NoFacts

  private given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  /** The terms a command gives by writing them (`Given.Written`), its
    * abstraction's commands included.
    */
  def writtenTerms(command: TraceCommand[NoFacts.type]): Vector[Configured[NoFacts.type]] =
    def written(named: Given[NoFacts.type]): Vector[Configured[NoFacts.type]] = named match
      case Given.Written(term) => Vector(term)
      case Given.Value(_)      => Vector.empty
    command match
      case TraceCommand.Rewrite(reason, _, _, bindings) =>
        val thunk = reason match
          case ProvedReason.Fill(shape) => shape.toVector.flatMap(found => written(found.codeOf))
          case ProvedReason.Body(shape) => shape.toVector.flatMap(found => written(found.codeOf))
          case ProvedReason.Eta(shape)  => shape.toVector.flatMap(found => written(found.codeOf))
          case _                        => Vector.empty
        thunk ++ bindings.flatMap((_, named) => written(named))
      case TraceCommand.Convert(_, _, _, bindings)  => bindings.flatMap((_, named) => written(named))
      case TraceCommand.Native(_, _)                => Vector.empty
      case TraceCommand.Abstraction(_, _, commands) => commands.flatMap(writtenTerms)

  private[strategies] val closedText: Gen[String] = HoasGenerators.closedTerm.map(LambdalatticeText.text)

  /** Lemmas with a higher-order occurrence, each sound by the β rule: k is
    * applied inside the thunk `λx. λz. k x`; applied nested inside a
    * filling, `λx. λz. z (k x)`; and applied inside an inner lambda to a term
    * that reads the inner lambda's binder, `λx. λz. z (λw. k (x w))`, the
    * shape of `wren_own_loop_lifted`. The three are shapes the binding
    * normal form (`gezi.ir.BindingNormalForm`) must reduce alike on the
    * saturator's side and on the trace's.
    *
    * FIXME (2026-11-16): the shape of k applied to a lambda, https://github.com/Atry/private-overlay/issues/1964
    * `λk. λa. (λx. λz. k (λw. x)) a = λk. λa. λz. k (λw. a)`, is left out
    * because its trace is not computed yet. The witness is the program
    * `(λx. λz. (λw. x) C) N`. The higher-order matching (`solved`,
    * `argumentOccurrence` in `HigherOrderMatching`) solves k := λf. f C,
    * abstracting the target's own redex `(λw. x) C` as `f C`; the hereditary
    * normal form of the left side then contracts that redex, so the expansion
    * union's backward conversion compares two different terms and the trace
    * has no command for it. A lambda argument abstracted from its body's
    * instance with captures gives the same `f captures` in k's value and
    * does need that reduction (`contest-entries-wren`'s nested_* points), so the union is not
    * a function of the pattern and the bindings. The fix (2026-11-16) is the matcher's: abstract a lambda argument only
    * where it occurs unapplied, leaving an applied occurrence in k's value,
    * so that hereditary re-normalization reproduces the target. Put that
    * lemma and its program shape back with that change.
    */
  private[strategies] val higherOrderLemmas: Vector[LemmaSides[NoFacts.type]] =
    Vector(
      equation(0, "λk. λa. (λx. λz. k x) a", "λk. λa. λz. k a"),
      equation(1, "λk. λa. (λx. λz. z (k x)) a", "λk. λa. λz. z (k a)"),
      equation(2, "λk. λa. (λx. λz. z (λw. k (x w))) a", "λk. λa. λz. z (λw. k (a w))")
    )

  private[strategies] val higherOrderIndex: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(NoFacts, Vector.empty, higherOrderLemmas, Vector.empty, Vector.empty)

  /** The instances a higher-order round may add: twice the most a round of
    * the generated programs added, measured on 2026-11-13 (main 67a1dc101)
    * on 100 programs drawn by `SeededSamples` from the seed 20261113, at
    * sizes 1 to the maximum: every round reached its fixed point, after at
    * most 4 instances, and had 2 to 6 unions of β conversion on the path
    * from its input to its output.
    *
    * FIXME (2026-11-16): measured with the first lemma only; the second and https://github.com/Atry/private-overlay/issues/1962
    * the third and their program shapes are not measured yet. Measure the
    * most a round of the four shapes adds and set twice that, with the
    * measurement.
    */
  private[strategies] val higherOrderBudget: Int = 8

  /** The higher-order saturator with no built-in rule, so that the round's
    * output is reached by the lemma's instance and the β conversions its
    * matching writes, which the article imports as conversion equations.
    */
  private[strategies] val higherOrderStrategy: FixpointEgraph[NoFacts.type] = FixpointEgraph(
    higherOrderIndex,
    HigherOrderSaturator(
      SaturationOptions(
        higherOrderLemmas.map(_.lemma),
        Set.empty,
        higherOrderBudget,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept
      , gezi.ir.TermConstruction(gezi.ir.NoFacts)),
      None,
      None,
      gezi.saturation.OpeningCriterionChoice.CallsAHead
    ),
    CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table[gezi.ir.NoFacts.type])
  )

  /** A redex a higher-order lemma rewrites: `(λx. λz. x C) N`;
    * `(λx. λz. x) (λw. C)`, whose normal form `λz. λw. C` has under its
    * binder a node whose layer is a thunk with a hole, which the front end
    * spells as one thunk of two holes, so that the saturator must fold that
    * node into the chain (d1ce63b27) for the `Convert` command's replay to
    * compute the term the proof holds; `(λx. λz. z (x C)) N`, which the
    * second lemma rewrites with k applied nested in a filling; and
    * `(λx. λz. z (λw. C (D (x w)))) N`, which the third rewrites with k
    * solved as `λy. C (D y)`, a lambda of two captures applied inside the
    * inner lambda. The shape of k applied to a lambda, `(λx. λz. (λw. x) C)
    * N`, is left out with its lemma (the FIXME at `higherOrderLemmas`).
    */
  private[strategies] val higherOrderPrograms: Gen[String] =
    for
      constant <- closedText
      other <- closedText
      argument <- closedText
      shape <- Gen.element1(0, 1, 2, 3)
    yield shape match
      case 0 => s"(λx. λz. x ($constant)) ($argument)"
      case 1 => s"(λx. λz. x) (λw. $constant)"
      case 2 => s"(λx. λz. z (x ($constant))) ($argument)"
      case _ => s"(λx. λz. z (λw. ($constant) (($other) (x w)))) ($argument)"

  /** The lemma `K a b = a` of K = λx. λy. x, which rewrites a closure's body
    * once the higher-order saturator opens it.
    */
  private[strategies] val openingLemmas: Vector[LemmaSides[NoFacts.type]] =
    Vector(equation(0, "λa. λb. (λx. λy. x) a b", "λa. λb. a"))

  private[strategies] val openingIndex: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(NoFacts, Vector.empty, openingLemmas, Vector.empty, Vector.empty)

  /** The higher-order saturator that opens bodies and writes them back,
    * under the budget of `AbstractionRecordLawTest`'s rounds, whose inputs
    * these are. FIXME (2026-11-14): the budget is not measured; measure the https://github.com/Atry/private-overlay/issues/1962
    * most a generated round adds and set twice that, with the measurement.
    */
  private[strategies] val openingStrategy: FixpointEgraph[NoFacts.type] = FixpointEgraph(
    openingIndex,
    HigherOrderSaturator(
      SaturationOptions(
        openingLemmas.map(_.lemma),
        Set.empty,
        16,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept
      , gezi.ir.TermConstruction(gezi.ir.NoFacts)),
      Some(LocalExtraction(Vector(Compression.at[gezi.ir.NoFacts.type]), _ => Set.empty, SpellingRetention.KeptWithinAPass)),
      None,
      gezi.saturation.OpeningCriterionChoice.CallsAHead
    ),
    CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table[gezi.ir.NoFacts.type])
  )

  /** A closure whose body calls K on a closed term and its variable. */
  private[strategies] val openingPrograms: Gen[String] =
    for
      constant <- closedText
      other <- closedText
      shape <- Gen.element1(0, 1)
    yield
      if shape == 0 then s"λz. (λk. λl. k) ($constant) z"
      else s"λz. z ((λk. λl. k) ($constant) z) ($other)"

  /** The input, the output and the proof of the round that writes a body
    * back, on the program.
    */
  private[strategies] def openingRan(program: String, stopped: scala.concurrent.Future[Unit])(Configured[NoFacts.type], Configured[NoFacts.type], StrategyProof[NoFacts.type]) =
    val input = closed(program)
    val outcome = openingStrategy
      .ran(Vector(input), true, StopSignal.completedWith(stopped))
      .getOrElse(throw IllegalStateException(s"the strategy gave no answer on $program"))
    val Vector(output) = outcome.outputs: @unchecked
    (input, output, outcome.proof.getOrElse(throw IllegalStateException(s"the strategy gave no proof on $program")))

  /** The input, the output and the proof of the higher-order round on the
    * program.
    */
  private[strategies] def higherOrderRan(program: String, stopped: scala.concurrent.Future[Unit])(Configured[NoFacts.type], Configured[NoFacts.type], StrategyProof[NoFacts.type]) =
    val input = closed(program)
    val outcome = higherOrderStrategy
      .ran(Vector(input), true, StopSignal.completedWith(stopped))
      .getOrElse(throw IllegalStateException(s"the strategy gave no answer on $program"))
    val Vector(output) = outcome.outputs: @unchecked
    (input, output, outcome.proof.getOrElse(throw IllegalStateException(s"the strategy gave no proof on $program")))

  private[strategies] def closed(text: String): Configured[NoFacts.type] = Defunctionalization.thunkInstruction[NoFacts.type](Lambdalattice.term(text))

  private[strategies] def equation(number: Int, left: String, right: String): LemmaSides[NoFacts.type] =
    LemmaSides(LemmaIdentifier(number), closed(left), closed(right))

  /** The evaluator steps the reading of a trace's text may take: one per
    * character of the text. The reading opens the Scott data of the trace
    * and never a term it holds, so its cost is linear in the data, which grows
    * with the program, and a limit that does not grow with it fails a large
    * enough program. Measured on 2026-11-13 (main 96257add8) on 601 traces,
    * 100 programs drawn by `SeededSamples` from each of the seeds 20261113,
    * 1, 2, 3, 4 and 5 and the counterexample a run of seed 107430364412876
    * shrank to (it read within 1,445 steps, over the constant limit of
    * 1,000 this replaced), the least limit each text reads within found by
    * bisection: 0.06 to 0.47 steps per character, and 3.0 to 7.4 steps per
    * Scott constructor of the data, the most 1,724 steps for 568
    * constructors. One step per character is about twice the most. A string
    * literal costs more, the host reading it bit by bit; the limit is the
    * trace text's own (`TraceText.readingLimit`), which adds 32 steps per
    * character of a literal, with its measurement.
    */
  private[strategies] def readingLimit(text: String): Long = TraceText.readingLimit(text)

  /** The terms before each step and the term after the last. */
  private[strategies] def replayed(round: RewriteRound[NoFacts.type]): Vector[Configured[NoFacts.type]] =
    round.steps.scanLeft(round.input)(RewriteTrace.applied[NoFacts.type])

  /** A lemma sound by the β rule whose right side builds `f a` with the
    * function metavariable f at its head, an application the β rule reads
    * (`gezi.egraph.EGraph.applicationRead`): the instance on
    * `(λu. u) (T A)` makes `T A`, and the β rule fills T's first hole with A,
    * leaving a residual thunk.
    */
  private[strategies] val residualLemmas: Vector[LemmaSides[NoFacts.type]] =
    Vector(equation(0, "λf. λa. (λu. u) (f a)", "λf. λa. f a"))

  private[strategies] val residualIndex: StandardLibraryIndex[NoFacts.type] =
    StandardLibraryIndex(NoFacts, Vector.empty, residualLemmas, Vector.empty, Vector.empty)

  /** The problems of a trace's output against the graph's term it should
    * reach. On main's graph a term may not be in the front end's spelling,
    * while a trace replays in it (`gezi.rewritetrace.ReplaySpelling`): the
    * output must be the term's spelling exactly, as an interned term, and read
    * back as the same lambda term, so that a spelling function that spelled two
    * lambda terms alike could not pass (`ReplaySpellingLawTest`: the spelling keeps the
    * readback).
    */
  private[strategies] def traceProblems(output: Configured[NoFacts.type], term: Configured[NoFacts.type]): Option[String] =
    def readback(of: Configured[NoFacts.type]): String = gezi.frontend.Lambdalattice.closedTextViewed(of)
    Option.when(!(output eq gezi.rewritetrace.ReplaySpelling.term(term)))(s"the trace does not replay to the spelling of $term")
      .orElse(Option.when(readback(output) != readback(term))(s"the trace's output reads back otherwise than $term"))
