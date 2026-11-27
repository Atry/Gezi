package gezi.strategies

import hedgehog.Gen
import hedgehog.Result
import gezi.egraph.MemoRetention
import gezi.ematching.closures.ClosureCompilation
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.BuiltInRule
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.orientation.StandardOrientationCompiler
import gezi.proofs.ArticleDerivation
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteTrace
import gezi.proofs.StrategyProof
import gezi.rewritetrace.TraceText
import gezi.saturation.StopSignal

/** The law of whole rounds whose proofs cross β residuals the e-graph keeps
  * in another spelling than the front end's: their traces and their
  * articles. A suite of its own for its deadline (below).
  */
class ResidualRoundLawTest extends GeneratedProperties:

  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private given gezi.ir.NoFacts.type = gezi.ir.NoFacts
  import RewriteTraceLawTest.*

  // Measured 2026-11-25 (cores 0-5 in contest.slice, two rounds an iteration, the constructed one always
  // crossing): 4.21, 3.47 and 4.06 s under three random seeds; most of it is the OpenTheory tool, a process of
  // its own for each crossing round's article, and the first round's warm-up (about 0.7 s). The bound, set
  // on 2026-11-17 at 1.5 times the slowest reading of the law with one round an iteration (4.40 s), still holds.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(7, "s")

  /** A program with one to three β residuals for the residual lemma to make:
    * `R A` alone, two in a choice, or one in the argument of another, `R`
    * being `(λu. u) (T a)` with T from `ResidualPrograms`. In the last two a
    * step comes after another's residual, at a position in the term that
    * residual left (in the last, inside its fillings).
    */
  private val residualRoundPrograms: Gen[Term] =
    def redex(function: Term, argument: Term): Term = Term.λ(bound => bound)(function(argument))
    for
      shape <- Gen.element1(0, 1, 2)
      first <- ResidualPrograms.lambdas
      second <- ResidualPrograms.lambdas
      argument <- HoasGenerators.closedTerm
      other <- HoasGenerators.closedTerm
    yield shape match
      case 0 => redex(first, argument)
      case 1 => Term.choice(redex(first, argument), redex(second, other))
      case _ => redex(first, redex(second, argument))

  /** `(λu. u) (T A)`, T of `ResidualPrograms.lambdasIgnoringTheFirstBinder`:
    * a round whose output is read through the β residual of `T A`.
    */
  private val crossingRoundPrograms: Gen[Term] =
    for
      function <- ResidualPrograms.lambdasIgnoringTheFirstBinder
      argument <- HoasGenerators.closedTerm
    yield Term.λ(bound => bound)(function(argument))

  /** The instances a round of `residualRoundPrograms` may add: twice the
    * most a round added, measured on 2026-11-16 (trace-side-spelling
    * 1ecce8bdc) on 100 programs drawn by `SeededSamples` from the seed
    * 20261116 under a budget of 1,000: 39 rounds added 1 instance and 61
    * added 2, each then at its fixed point.
    */
  private val residualRoundBudget: Int = 4

  private val residualStrategy: FixpointEgraph[NoFacts.type] = FixpointEgraph(
    residualIndex,
    StandardSaturator(
      SaturationOptions(
        residualLemmas.map(_.lemma),
        BuiltInRule.beforeOptIn,
        residualRoundBudget,
        BaselineLemmaEncoding,
        ClosureCompilation,
        StandardIndexer.of[gezi.ir.NoFacts.type],
        StandardOrientationCompiler,
        MemoRetention.Kept
      , gezi.ir.TermConstruction(gezi.ir.NoFacts))
    ),
    CountedExtractor(ExtractionOptions(Vector("compression")), BaselineModules.table[gezi.ir.NoFacts.type])
  )

  /** Purpose: catch a trace whose later commands are indexed against a term
    * other than the one the player holds once a step has crossed a β
    * residual the e-graph keeps unspelled (the player holds the residual's
    * spelling, `ReplaySpelling`), and an article the writer derives through
    * such a residual that the OpenTheory tool rejects: on a whole round,
    * saturation and extraction, whose proof crosses a residual, the trace
    * replays to the output's spelling and reads back as the output
    * (`traceProblems`), its text reads back as the trace, and, on a round
    * that crosses one, the tool accepts the round's article with nothing on
    * standard error (a round that crosses none writes an article of the kind
    * the other proof laws check).
    *
    * Whether a round's proof crosses a residual is the extraction's choice
    * (the round's output need not be reached through one), so each
    * iteration checks the law on a round of `residualRoundPrograms` and on a
    * round that crosses one by construction: `(λu. u) (T A)` with T of
    * `ResidualPrograms.lambdasIgnoringTheFirstBinder`, whose β reduct is
    * smaller than `T A`, so that the compression extraction reads the
    * output through the residual the β rule leaves (a step's term holding a
    * thunk that is not its own respelling).
    */
  stoppableProperty("the trace of a round that crosses β residuals replays to its output, and its article checks") { stopped =>
    def checked(round: ResidualRound): Result =
      val trace = RewriteTrace.trace(round.derivation)
      val text = TraceText.written(trace)
      val checked =
        if round.crossings == 0 then (0, "")
        else
          val article = java.nio.file.Files.createTempFile("residual_round", ".art")
          try
            OpentheoryArticle.written(residualIndex, round.input, round.output, round.proof, article)
            gezi.proofs.ProofTestFiles.toolChecked(article)
          finally java.nio.file.Files.delete(article)
      Result
        .all(
          List(
            Result.assert(traceProblems(trace.output(round.input), round.output).isEmpty).log(traceProblems(trace.output(round.input), round.output).mkString),
            Result.assert(TraceText.read(text, readingLimit(text)) == trace).log(text),
            Result.diff(checked, (0, ""))(_ == _).log("the OpenTheory tool's exit status and standard error")
          )
        )
        .log(s"${trace.rounds.flatten.size} commands, ${round.crossings} terms crossing a residual")
    for
      drawn <- residualRoundPrograms.forAllWithLog(LambdalatticeText.text)
      crossing <- crossingRoundPrograms.forAllWithLog(LambdalatticeText.text)
    yield
      val stop = StopSignal.completedWith(stopped)
      val crossed = residualRound(crossing, stop)
      Result.all(List(checked(residualRound(drawn, stop)), Result.assert(crossed.crossings > 0).log("the constructed round crosses no residual"), checked(crossed)))
  }

  /** A round of `residualStrategy`: its input, its output, its proof, the
    * derivation the article writer builds of it, and the number of its
    * steps' terms that hold a thunk that is not its own respelling.
    */
  private final case class ResidualRound(
      input: Configured[NoFacts.type],
      output: Configured[NoFacts.type],
      proof: StrategyProof[NoFacts.type],
      derivation: ArticleDerivation[NoFacts.type],
      crossings: Int
  )

  private def residualRound(program: Term, stop: StopSignal): ResidualRound =
    val input = Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](program.deBruijnTerm(Map.empty))(using gezi.ir.NoFacts)
    val outcome = residualStrategy.ran(Vector(input), true, stop).getOrElse(fail("the strategy gave no answer"))
    val Vector(output) = outcome.outputs: @unchecked
    val proof = outcome.proof.getOrElse(fail("the strategy gave no proof"))
    val derivation = OpentheoryArticle.derivation(residualIndex, input, output, proof)
    ResidualRound(
      input,
      output,
      proof,
      derivation,
      replayed(RewriteTrace.round(derivation)).count(ResidualPrograms.respellable(_).nonEmpty)
    )
