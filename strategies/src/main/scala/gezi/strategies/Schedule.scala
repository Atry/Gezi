package gezi.strategies

import java.nio.file.Path
import gezi.standardlibrary.StandardLibraryIndex
import gezi.proofs.OpentheoryArticle
import gezi.proofs.RewriteTrace
import gezi.proofs.StrategyProof
import gezi.rewritetrace.Trace
import gezi.ir.Instruction
import gezi.saturation.StopSignal

/** A strategy's report of a round, which the schedule passes on and does
  * not read.
  */
trait StrategyReport

/** What a strategy's search gives: one output for
  * each input, in order, its report, the proof when it was asked for, and
  * the strategy after the search: a strategy that carries state from one search to the next gives it
  * as a field of the strategy after; a strategy with no such state gives
  * itself.
  */
final case class StrategyOutcome(
    outputs: Vector[Instruction],
    report: StrategyReport,
    proof: Option[StrategyProof],
    strategyAfter: SearchStrategy
)

/** A search strategy (THE SEARCH STRATEGIES of `schedule.pl`): it searches
  * from the inputs and gives their outputs, or
  * nothing when it does not answer. It holds its own options, the knowledge
  * modules it enables and its budget among them. It reads the stop signal
  * at its checks and, once a stop is requested, ends early with what it has
  * (judge record 4.4); its outputs are then still equal to its inputs, only
  * less refined.
  */
trait SearchStrategy:
  def ran(inputs: Vector[Instruction], proofWanted: Boolean, stop: StopSignal): Option[StrategyOutcome]

/** A round: its strategy, and the file its article is written to, when it
  * writes one.
  */
final case class Round(strategy: SearchStrategy, article: Option[Path])

/** The record of one round: its inputs, its strategy's report and its
  * outputs.
  */
final case class RoundRan(inputs: Vector[Instruction], report: StrategyReport, outputs: Vector[Instruction])

/** A schedule's result: the last round's
  * outputs, the record of each round, in order, and the schedule after the
  * run: each round's strategy replaced by its strategy after
  * (`StrategyOutcome.strategyAfter`), its article kept.
  */
final case class Scheduled(
    outputs: Vector[Instruction],
    records: Vector[RoundRan],
    scheduleAfter: Vector[Round]
)

/** Why a schedule could not run (`schedule_error(Reason)`). */
enum ScheduleErrorReason:
  case NotInputs(inputs: Vector[Instruction])
  case NotASchedule(rounds: Vector[Round])
  case StrategyUnanswered(strategy: SearchStrategy)
  case OutputsUnmatched(strategy: SearchStrategy)
  case NotAProof(strategy: SearchStrategy)

/** A schedule that could not run. */
final case class ScheduleError(reason: ScheduleErrorReason)
    extends RuntimeException(s"schedule error: $reason")

/** A schedule of rounds, each a search strategy, the port of
  * `gezi/prolog/gezi/schedule.pl`, whose module documentation
  * (THE SEARCH STRATEGIES, THE PROOF, THE ROUNDS) this follows. It names no
  * strategy, no knowledge module and no option.
  *
  * The inputs of the first round are the schedule's inputs; the inputs of
  * every later round are the outputs of the round before it, and nothing
  * else passes between rounds: no class,
  * no pool, no state of a strategy. A round's strategy may carry state from
  * one run of the schedule to the next: the run gives the schedule after,
  * each round holding the strategy its search gave after it
  * (`Scheduled.scheduleAfter`), and the caller runs that schedule next.
  * A round with an article asks its
  * strategy for the proof (`gezi.proofs.StrategyProof`, THE PROOF) and
  * writes to its file the OpenTheory article of its first equation, the
  * first input's, from the proof with that equation alone
  * (`gezi.proofs.OpentheoryArticle.written`, the port of
  * `opentheory_article_written/4`). The article's two sides are the round's
  * first input and first output as the instructions they are; the writer reads
  * the lemmas a union names from the library's index the schedule is given.
  *
  * THE TRACE. When every round has an article, the schedule also writes the
  * trace of its rounds, one file: the lemmas the rounds' commands name, and
  * each round's commands, from the first round's first input, from the same
  * proofs the articles are written from (`RewriteTrace.trace` of each
  * round's `OpentheoryArticle.derivation`, joined by `Trace.joined`), as
  * `TraceText.written` writes it, with the text of that input beside it and
  * the player's page of both (`TraceFiles.written`, an HTML page).
  * Its file is the first
  * round's article's name with `.art` replaced by `.trace.lambdalattice`
  * (`traceFile`): the trace from that round on. A judge's point runs one
  * cell, so one schedule, and so one file; a session of several cells writes
  * one file per cell.
  *
  * FIXME (carried from schedule.pl:70): https://github.com/Atry/private-overlay/issues/1958
  * the articles of a schedule are one per round, and their equations chain,
  * the output of each round being the input of the next, so the first
  * input's equation follows by transitivity; no article and no Lean theorem
  * states that composition yet, and the end-to-end theorem is stated for one
  * round only.
  *
  * FIXME (carried from schedule.pl:75): https://github.com/Atry/private-overlay/issues/1958
  * no article
  * states the equation of an input after the first, though the proof holds
  * it; candidate: an article that exports one theorem for each equation.
  *
  * Departures from the Prolog: a round
  * and a strategy are typed values, so the Prolog's errors for a round or a
  * list of inputs of another shape cannot arise; and the library's index the writer reads is given to `run`, where the Prolog
  * writer read the one global index.
  */
object Schedule:

  /** The rounds run in order from the inputs, the
    * articles written with the lemmas of the library's index, each round's
    * strategy given the stop signal. Throws
    * `ScheduleError` with `NotInputs` for no input, `NotASchedule` for no
    * round, `StrategyUnanswered` for a round whose strategy gives no answer,
    * `OutputsUnmatched` for one that gives as many outputs as inputs not,
    * and `NotAProof` for a round with an article whose strategy gives no
    * proof; and `OpentheoryArticleError` as the writer throws it.
    */
  def run(index: StandardLibraryIndex, inputs: Vector[Instruction], rounds: Vector[Round], stop: StopSignal): Scheduled =
    if inputs.isEmpty then throw ScheduleError(ScheduleErrorReason.NotInputs(inputs))
    if rounds.isEmpty then throw ScheduleError(ScheduleErrorReason.NotASchedule(rounds))
    val (scheduled, traces) =
      rounds.foldLeft((Scheduled(inputs, Vector.empty, Vector.empty), Vector.empty[(Instruction, Trace)])) {
        case ((scheduled, traces), round) =>
          val (outcome, trace) = roundRan(index, scheduled.outputs, round, stop)
          (
            Scheduled(
              outcome.outputs,
              scheduled.records :+ RoundRan(scheduled.outputs, outcome.report, outcome.outputs),
              scheduled.scheduleAfter :+ Round(outcome.strategyAfter, round.article)
            ),
            traces ++ trace
          )
      }
    tracedArticle(rounds).foreach(first => TraceFiles.written(first, inputs.head, Trace.joined(traces)))
    scheduled

  /** The file of the trace of the rounds, when every round has an article:
    * `TraceFiles.traceFile` of the first round's article. Throws
    * `IllegalArgumentException` for an article whose name does not end in
    * `.art`.
    */
  def traceFile(rounds: Vector[Round]): Option[Path] = tracedArticle(rounds).map(TraceFiles.traceFile)

  /** The first round's article, when every round has one. */
  private def tracedArticle(rounds: Vector[Round]): Option[Path] =
    val articles = rounds.flatMap(_.article)
    Option.when(articles.size == rounds.size)(articles).flatMap(_.headOption)

  /** The rounds, each given the article file `round-<n>.art` of the
    * directory, `n` counting from `firstNumber`: the first round's article
    * is `round-<firstNumber>.art`, the next round's the next number, and so
    * on; a round's strategy is kept. The schedules an entry runs for one
    * point number their articles on from one another, the first schedule
    * from 1 and each later one from the number after the last round of the
    * one before (`firstNumber + rounds.size`), so that the judge reads the
    * articles of the point's compilation in order from `round-1.art`.
    */
  def articled(rounds: Vector[Round], directory: Path, firstNumber: Int): Vector[Round] =
    rounds.zipWithIndex.map((round, position) =>
      round.copy(article = Some(directory.resolve(s"round-${firstNumber + position}.art")))
    )

  /** The round's strategy's outcome on the inputs, checked, its article
    * written, with the trace of the round when it has an article and the
    * input the trace starts from.
    */
  private def roundRan(
      index: StandardLibraryIndex,
      inputs: Vector[Instruction],
      round: Round,
      stop: StopSignal
  ): (StrategyOutcome, Option[(Instruction, Trace)]) =
    val outcome = round.strategy
      .ran(inputs, round.article.isDefined, stop)
      .getOrElse(throw ScheduleError(ScheduleErrorReason.StrategyUnanswered(round.strategy)))
    if outcome.outputs.size != inputs.size then
      throw ScheduleError(ScheduleErrorReason.OutputsUnmatched(round.strategy))
    val trace = round.article.map { file =>
      val proof = outcome.proof.getOrElse(throw ScheduleError(ScheduleErrorReason.NotAProof(round.strategy)))
      val first = proof.equations.headOption.getOrElse(
        throw ScheduleError(ScheduleErrorReason.NotAProof(round.strategy))
      )
      val firstProof = proof.copy(equations = Vector(first))
      OpentheoryArticle.written(index, inputs.head, outcome.outputs.head, firstProof, file)
      (inputs.head, RewriteTrace.trace(OpentheoryArticle.derivation(index, inputs.head, outcome.outputs.head, firstProof)))
    }
    (outcome, trace)
