package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.weakhead.Mode
import gezi.contest.corpora.common.DeBruijnTerms
import gezi.contest.corpora.reductions.NormalFormReading
import gezi.contest.corpora.reductions.DrawnPoint
import gezi.contest.corpora.reductions.Reduction
import gezi.contest.corpora.reductions.Reference
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.ExchangeText
import gezi.frontend.ProgramPurity
import gezi.frontend.Term
import scala.collection.View
import scala.jdk.CollectionConverters.*
import gezi.ir.{Configured, NoFacts}

/** What a point asks: every normal form of the program (an evaluation
  * point, its reference the finite set tabling(weak_head) reads), or whether a
  * candidate is one of them (a judgment point, its expected answer whether
  * the candidate is a member). An evaluation asks for as many solutions as
  * an entry can find; a judgment asks whether one value is a solution.
  */
enum Question:
  case Evaluation(reference: Set[Configured[NoFacts.type]])
  case Judgment(candidate: Configured[NoFacts.type], member: Boolean)

/** A point of a round: its name, stage, family and weight, its closed
  * program as the `ExchangeText.line` its points file holds, and what it
  * asks. The program stays its line: the supervisor hands it to the runner
  * as it is (`gezi.contest.runner.PipeLines.evaluationLine`), and the runner
  * reads it in the entry's JVM, so that the supervisor's heap holds the
  * points file's text and not the programs' IR (measured 2026-11-22 on the
  * points of five MIXINv2 builtin families, seed 20261122, R = 64, ten
  * points, 6.07 MB: read as instructions, out of memory at 256 MB, and at
  * 4 GB 277 to 292 s with 675 to 730 MB live afterwards). The reference's
  * normal forms and a judgment's candidate are small and are instructions;
  * an answer is compared with them as instructions (`Outcome.judged`).
  */
final case class Point(
    name: String,
    stage: String,
    family: String,
    weight: BigDecimal,
    programLine: String,
    question: Question
):

  /** The program's instruction, read from its line now and not kept: for
    * the few readers that need it (the article manifest), never for the
    * pass. Throws `IllegalArgumentException` for a line that is no line of
    * the exchange format.
    */
  def program: Configured[NoFacts.type] =
    ExchangeText.term[NoFacts.type](programLine).fold(reason => throw IllegalArgumentException(s"the program of $name: $reason"), identity)

/** A point of a points file: an evaluation point, whose reference the
  * writer reads by tabling(weak_head) (`Reference.Read`, the default) or takes as
  * the source computed it (`Reference.Computed`), with the trap candidates
  * its family computed for it (`DrawnPoint.trapCandidates`, none by default),
  * or a judgment point, written as given (the proof of a candidate that is
  * not a member is kept beside the file).
  */
enum PointSource:
  case EvaluationSource(
      name: String,
      stage: String,
      family: String,
      weight: BigDecimal,
      program: gezi.contest.corpora.common.ProblemTerm,
      reference: Reference = Reference.Read,
      trapCandidates: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm] = Vector.empty
  )
  case JudgmentSource(
      name: String,
      stage: String,
      family: String,
      weight: BigDecimal,
      program: gezi.contest.corpora.common.ProblemTerm,
      candidate: gezi.contest.corpora.common.ProblemTerm,
      member: Boolean
  )

  /** The point's name. */
  def pointName: String = this match
    case EvaluationSource(name, _, _, _, _, _, _) => name
    case JudgmentSource(name, _, _, _, _, _, _) => name

/** An evaluation source the writer did not write: its reading by
  * tabling(weak_head) stopped within the budget, as the reading says.
  */
final case class Unwritten(name: String, reading: NormalFormReading)

/** The judgment points the writer adds to each evaluation point written
  * (`PointsFile.written`): of the weight, one per member of the reference
  * and, with a trap draw, one per trap, a point that gets no trap getting
  * no judgment point at all; with `judgmentsOnly`, the
  * evaluation point's own row is not written, only its judgment points.
  * Traps are written only with a trap draw, whose count bounds them, the
  * candidates a family computes included.
  */
final case class JudgmentPoints(weight: BigDecimal, judgmentsOnly: Boolean, traps: Option[TrapDraw])

/** The second source of trap candidates, after the candidates a point's
  * family computes (`PointSource.EvaluationSource.trapCandidates`): a second
  * instance of the evaluation sources, the same points (by name) drawn from
  * another seed, whose own computed candidates are not read; and the most
  * traps an evaluation point gets, from either source.
  */
final case class TrapDraw(secondInstance: Vector[PointSource], count: Int)

/** Why an evaluation point got no traps. */
enum TrapWithheld(val reported: String):

  /** Its program holds a choice, a parallel or a constant. */
  case NotPure extends TrapWithheld("not pure")

  /** Its reference holds more than one normal form. */
  case MoreThanOneNormalForm extends TrapWithheld("more than one normal form")

  /** Its reference holds no normal form. */
  case NoNormalForm extends TrapWithheld("no normal form")

  /** The point's computed candidates hold none outside the reference, and
    * the reading of the second instance's point of the same name stopped.
    */
  case ReadingIncomplete extends TrapWithheld("reading incomplete")

  /** Neither the point's computed candidates nor the second instance's
    * points of its family hold a normal form outside the reference.
    */
  case NoOtherNormalForm extends TrapWithheld("no normal form outside the reference")

/** What the writer did about traps for an evaluation point: the traps
  * written, at least one, with the point's judgment points; or the reasons
  * none was, and then the point has no judgment point at all.
  */
enum TrapOutcome:
  case Written(count: Int)
  case Withheld(reasons: Vector[TrapWithheld])

  /** The outcome as the writer prints it. */
  def reported: String = this match
    case Written(count)    => s"$count written"
    case Withheld(reasons) => s"0 written (${reasons.map(_.reported).mkString(", ")}), no judgment point written"

/** What the writer reports back: the evaluation sources not written, and,
  * with a trap draw, each evaluation point written with its trap outcome.
  */
final case class WrittenFile(unwritten: Vector[Unwritten], traps: Vector[(String, TrapOutcome)])

/** A round's points file, `points.tsv` in a directory:
  * a header naming the
  * columns, then one point a line, tab-separated:
  *
  *   - `name`, `stage`, `family`: free text without tabs;
  *   - `weight`: a decimal number;
  *   - `kind`: `evaluation` or `judgment`;
  *   - `program`: for an evaluation point the closed program, an
  *     instruction as one `ExchangeText.line`, which `read` checks for the
  *     line's shape only (`ExchangeText.shaped`) and the runner reads; for a
  *     judgment point `@<program name>`, a reference to a row of the programs
  *     file;
  *   - `candidate`: for a judgment point the candidate as such a line, empty
  *     for an evaluation point;
  *   - `normal_forms`: for an evaluation point the reference, the finite set
  *     of normal forms tabling(weak_head) reads as one `ExchangeText.normalFormsLine`
  *     of their instructions (their choice, sorted by their lines; for none, the line of no
  *     normal form, a hole, `ExchangeText.noNormalFormLine`); for a judgment
  *     point `member` or `not_member`.
  *
  * The programs file, `programs.tsv` beside it, holds each program a
  * judgment point judges once: a header naming the columns, then one
  * program a line, tab-separated, `program` (its name), `family` (the
  * family of the judgment points that refer to it) and `term` (the program
  * as one `ExchangeText.line`). A program is named after the first judgment
  * point written that judges it, so program names are unique wherever point
  * names are, and the files of several families, concatenated under one
  * header, stay consistent.
  *
  * The programs hold no library name, so a line holds no constant.
  */
object PointsFile:

  val fileName: String = "points.tsv"

  val header: String = "name\tstage\tfamily\tweight\tkind\tprogram\tcandidate\tnormal_forms"

  val programsFileName: String = "programs.tsv"

  val programsHeader: String = "program\tfamily\tterm"

  /** The points of the directory's file, in file order, each judgment
    * point's program resolved from the programs file. Throws
    * `IllegalArgumentException` naming the file and the line for a
    * malformed line, a missing or other header, a name met twice, a
    * judgment point whose program column is not a reference `@<name>`, a
    * reference to a program the programs file does not hold, a judgment
    * point when the programs file is missing, and a program name met twice
    * in the programs file.
    */
  def read(directory: Path): Vector[Point] =
    val file = directory.resolve(fileName)
    val lines = Files.readAllLines(file, StandardCharsets.UTF_8).asScala.toVector
    if lines.headOption != Some(header) then throw IllegalArgumentException(s"$file:1: the header is not $header")
    val programsFile = directory.resolve(programsFileName)
    val programs = Option.when(Files.exists(programsFile))(programsRead(programsFile))
    val points = lines.zipWithIndex.drop(1).map((line, index) => pointRead(file, index + 1, line, programsFile, programs))
    repeatedName(points.map(_.name)).foreach(name => throw IllegalArgumentException(s"$file: the point $name is written twice"))
    points

  /** The programs of a programs file, by name, each its line. */
  private def programsRead(file: Path): Map[String, String] =
    val lines = Files.readAllLines(file, StandardCharsets.UTF_8).asScala.toVector
    if lines.headOption != Some(programsHeader) then throw IllegalArgumentException(s"$file:1: the header is not $programsHeader")
    val programs = lines.zipWithIndex.drop(1).map((line, index) =>
      def malformed(reason: String): Nothing = throw IllegalArgumentException(s"$file:${index + 1}: $reason")
      line.split("\t", -1).toVector match
        case Vector(name, _, termText) =>
          if ExchangeText.shaped(termText) then name -> termText else malformed(s"the term is no line of the exchange format: ${termText.take(80)}")
        case fields => malformed(s"${fields.size} fields, not 3")
    )
    repeatedName(programs.map(_._1)).foreach(name => throw IllegalArgumentException(s"$file: the program $name is written twice"))
    programs.toMap

  private def pointRead(
      file: Path,
      number: Int,
      line: String,
      programsFile: Path,
      programs: Option[Map[String, String]]
  ): Point =
    def malformed(reason: String): Nothing = throw IllegalArgumentException(s"$file:$number: $reason")
    def term(text: String, column: String): Configured[NoFacts.type] =
      ExchangeText.term[NoFacts.type](text).fold(reason => malformed(s"the $column: $reason"), identity)
    def programLine(text: String, column: String): String =
      if ExchangeText.shaped(text) then text else malformed(s"the $column is no line of the exchange format: ${text.take(80)}")
    def judgedProgram(text: String): String =
      if !text.startsWith("@") then
        malformed(s"a judgment point's program is a reference @<name> to $programsFile, not ${text.take(40)}")
      val name = text.drop(1)
      programs match
        case None        => malformed(s"a judgment point refers to the program $name, and $programsFile is missing")
        case Some(found) => found.getOrElse(name, malformed(s"the program $name is not in $programsFile"))
    line.split("\t", -1).toVector match
      case Vector(name, stage, family, weightText, kind, programText, candidateText, normalFormsText) =>
        val weight =
          if weightText.matches("""-?[0-9]+(\.[0-9]+)?""") then BigDecimal(weightText)
          else malformed(s"the weight $weightText is not a decimal number")
        val (program, question) = kind match
          case "evaluation" =>
            if candidateText.nonEmpty then malformed("an evaluation point has a candidate")
            (
              programLine(programText, "program"),
              Question.Evaluation(
                ExchangeText
                  .normalForms[NoFacts.type](normalFormsText)
                  .fold(reason => malformed(s"the normal forms: $reason"), _.toSet)
              )
            )
          case "judgment" =>
            val member = normalFormsText match
              case "member"     => true
              case "not_member" => false
              case other        => malformed(s"a judgment point expects member or not_member, not $other")
            (judgedProgram(programText), Question.Judgment(term(candidateText, "candidate"), member))
          case other => malformed(s"the kind $other")
        Point(name, stage, family, weight, program, question)
      case fields => malformed(s"${fields.size} fields, not 8")

  /** The points file and the programs file of the sources written to the
    * directory, the programs file with its header alone when no judgment
    * point is written, the sources not written reported back: each
    * evaluation source's normal forms read
    * by tabling(weak_head) within the budget of steps (`Reduction.answeredNormalForms`,
    * the reference reading of the corpora's tests), a source whose reading
    * stops not written, or, for a source whose reference is
    * `Reference.Computed`, its normal forms as given, sorted the same way,
    * with nothing read; each judgment source written as given. Throws
    * `IllegalArgumentException` for a name, stage or family holding a tab or
    * a line break, or a name given twice.
    */
  def written(directory: Path, sources: Vector[PointSource], budget: Long): Vector[Unwritten] =
    written(directory, sources, budget, None).unwritten

  /** The points file of the sources, as the three-argument `written`, and,
    * with judgment points, for each evaluation point written its judgment
    * points (`judgmentPoints`) after its row, or in place of it with
    * `judgmentsOnly`. An evaluation source not written gets none. Throws
    * `IllegalArgumentException` as the three-argument `written` does, for a
    * trap count below 1, for a name given twice in the second instance, for
    * an evaluation point the second instance has no point of the same name
    * for, for a computed trap candidate of an evaluation source that is not
    * a closed βη normal form (`Reduction.normalFormTerm`: no choice, no
    * parallel, no constant), and for a name met twice among the points
    * written.
    */
  def written(
      directory: Path,
      sources: Vector[PointSource],
      budget: Long,
      judgments: Option[JudgmentPoints]
  ): WrittenFile =
    repeatedName(sources.map(_.pointName)).foreach(name => throw IllegalArgumentException(s"the point $name is given twice"))
    sources.foreach {
      case PointSource.EvaluationSource(name, _, _, _, _, _, trapCandidates) =>
        trapCandidates.find(candidate => !Reduction.normalFormTerm(candidate)).foreach(candidate =>
          throw IllegalArgumentException(
            s"the point $name has a computed trap candidate that is not a closed βη normal form: ${candidate.toString.take(80)}"
          )
        )
      case _: PointSource.JudgmentSource => ()
    }
    val trapDraw = judgments.flatMap(_.traps)
    trapDraw.foreach(draw =>
      if draw.count < 1 then throw IllegalArgumentException(s"a trap count is at least 1, not ${draw.count}")
      repeatedName(draw.secondInstance.map(_.pointName)).foreach(name =>
        throw IllegalArgumentException(s"the point $name is given twice in the second instance")
      )
    )
    val secondPoints = trapDraw.toVector.flatMap(_.secondInstance).collect {
      case PointSource.EvaluationSource(name, _, family, _, program, reference, _) => name -> SecondPoint(family, DrawnPoint(program, reference))
    }.toMap
    val outcomes = sources.map(source => source -> rows(source, budget, judgments, secondPoints))
    val writtenRows = outcomes.collect { case (_, Right(found)) => found.rows }.flatten
    val programRows = outcomes.collect { case (_, Right(found)) => found.program }.flatten
    repeatedName(writtenRows.map(_.name)).foreach(name => throw IllegalArgumentException(s"the point $name is written twice"))
    Files.createDirectories(directory)
    linesWritten(directory.resolve(fileName), header, writtenRows.view.map(_.text))
    linesWritten(directory.resolve(programsFileName), programsHeader, programRows.view.map(_.text))
    WrittenFile(
      outcomes.collect { case (source, Left(reading)) => Unwritten(source.pointName, reading) },
      outcomes.collect { case (source, Right(SourceRows(_, _, Some(trapOutcome)))) => source.pointName -> trapOutcome }
    )

  /** Writes the header and the lines to the file, each line followed by a
    * line break, as a stream: the lines are a view, each made when the file
    * takes it and dropped once written, so neither the whole file nor every
    * row's text is held in memory at once.
    */
  private def linesWritten(file: Path, header: String, lines: View[String]): Unit =
    Files.write(file, (View.Single(header) ++ lines).asJava, StandardCharsets.UTF_8)

  /** The judgment points of an evaluation point: one per member of its
    * reference, expected member, and one per trap, expected not_member, each
    * with the evaluation point's program and stage, the candidate, the
    * weight, the family `<family>_judgments` (so that they are timed as a
    * family of their own) and the name `<name>/candidate_<k>`, k the
    * candidate's index among all the point's candidates, members and traps
    * together, sorted by their `ExchangeText.line`. The name does not say
    * whether the candidate is a member: an entry receives the name on the
    * pipe (`PipeLines.evaluationLine`, `PipeLines.judgmentLine`), and a name that said it would give the
    * answer away.
    */
  private def judgmentPoints(
      evaluation: PointSource.EvaluationSource,
      reference: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm],
      traps: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm],
      weight: BigDecimal
  ): Vector[PointSource.JudgmentSource] =
    (reference.map(_ -> true) ++ traps.map(_ -> false)).sortBy((candidate, _) => line(candidate)).zipWithIndex.map {
      case ((candidate, member), index) =>
        PointSource.JudgmentSource(
          s"${evaluation.name}/candidate_$index",
          evaluation.stage,
          s"${evaluation.family}_judgments",
          weight,
          evaluation.program,
          DeBruijnTerms.hoas(candidate),
          member
        )
    }

  /** The reference of a program: tabling(weak_head)'s reading within the budget for
    * `Reference.Read`; for `Reference.Computed` the normal forms given,
    * nothing read.
    */
  private def referenceReading(point: DrawnPoint, budget: Long): NormalFormReading = point.reference match
    case Reference.Read                    => Reduction.answeredNormalForms(Mode.TablingWeakHead, point.program, budget)
    case Reference.Computed(normalForms, _) => NormalFormReading.Finished(normalForms)

  /** A point of the second instance with its family. */
  private final case class SecondPoint(family: String, point: DrawnPoint)

  /** The traps of an evaluation point whose reference finished: up to
    * `count` closed βη normal forms that are not in the reference, compared
    * as `DeBruijnTerm` values, sorted by their `ExchangeText.line`. They are
    * taken, from the first of these sources that yields one, the next read
    * only when needed:
    *
    *   1. the point's own computed candidates (`trapCandidates`, which
    *      `written` checked to be closed βη normal forms, as the proof
    *      below needs of every candidate), deduplicated;
    *   2. the second instance's point of the same name (its reference,
    *      `referenceReading`: read within the same budget, or computed);
    *   3. the references of the second instance's other points of the same
    *      family (other names), read the same way, deduplicated. A
    *      reference of such a peer that does not finish contributes nothing.
    *
    * The sources are not mixed: a point whose computed candidates hold one
    * outside its reference gets only those, so that its traps are the
    * wrong answers its family chose, and its second instance is not read.
    * A family that computes none gets the traps it got before computed
    * candidates existed.
    *
    * A point gets traps only when its program is a pure λ term
    * (`ProgramPurity.pureInstruction`) and its reference holds
    * exactly one normal form N0. The reference reading proves only that
    * T ⊑_O N for each normal form N it reads, never that nothing else is. For a
    * pure program T read to the one normal form N0, the reading applies the
    * η rule at abstraction, so T =βη N0, inside ⊢_{λ-lattice-unit-η}, and
    * NF◇(T) = {N0} by Böhm's separation of distinct βη normal
    * forms: T ⊑_O N holds of no other closed βη normal form N, proved
    * wherever N was read or computed, so the source of the candidates does
    * not enter the proof. A computed reference
    * stands for that reading on the strength of its claim, the family's test
    * that checks it against the reading on small draws. For a program with a
    * choice or a parallel no such proof exists yet, so it gets none: such a
    * reading need not derive T equal to the choice of its normal forms
    * (a counterexample exists), and whether
    * every N with T ⊑_O N is in the read set is not proved.
    * Every reason that holds is reported; neither the computed candidates
    * nor the second instance are looked at unless the point itself
    * qualifies. A point that qualifies but finds no normal form outside its
    * reference, among its computed candidates, in the point of the same name
    * or in its family's other points, is withheld as well, so that a written
    * outcome always has at least one trap.
    */
  private def traps(
      name: String,
      program: Configured[NoFacts.type],
      reference: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm],
      computedCandidates: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm],
      secondPoint: SecondPoint,
      secondPoints: Map[String, SecondPoint],
      budget: Long,
      count: Int
  ): (Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm], TrapOutcome) =
    val withheld = Vector(
      Option.when(!ProgramPurity.pureInstruction(program))(TrapWithheld.NotPure),
      Option.when(reference.size > 1)(TrapWithheld.MoreThanOneNormalForm),
      Option.when(reference.isEmpty)(TrapWithheld.NoNormalForm)
    ).flatten
    def outside(normalForms: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm]): Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm] =
      normalForms.distinct.filterNot(reference.contains).sortBy(line).take(count)
    lazy val computed = outside(computedCandidates)
    if withheld.nonEmpty then (Vector.empty, TrapOutcome.Withheld(withheld))
    else if computed.nonEmpty then (computed, TrapOutcome.Written(computed.size))
    else
      referenceReading(secondPoint.point, budget) match
        case NormalFormReading.Finished(secondNormalForms) =>
          val sameName = outside(secondNormalForms)
          val found =
            if sameName.nonEmpty then sameName
            else
              outside(secondPoints.collect {
                case (peerName, peer) if peerName != name && peer.family == secondPoint.family =>
                  referenceReading(peer.point, budget) match
                    case NormalFormReading.Finished(peerNormalForms) => peerNormalForms
                    case _                                           => Vector.empty
              }.toVector.flatten)
          if found.isEmpty then (Vector.empty, TrapOutcome.Withheld(Vector(TrapWithheld.NoOtherNormalForm)))
          else (found, TrapOutcome.Written(found.size))
        case _ => (Vector.empty, TrapOutcome.Withheld(Vector(TrapWithheld.ReadingIncomplete)))

  private def repeatedName(names: Vector[String]): Option[String] =
    names.groupBy(identity).collectFirst { case (name, found) if found.size > 1 => name }

  /** The rows of a source, the program its judgment points judge, and for
    * an evaluation source under a trap draw its trap outcome: an evaluation
    * source's row (not with `judgmentsOnly`), followed by its judgment
    * points' rows when judgment points are asked, all referring to one
    * program named after the first of them, or the reading that stopped; a
    * judgment source's row, referring to its program named after itself.
    * Throws `IllegalArgumentException` for a name, stage or family holding
    * a tab or a line break. Under a trap draw, a point withheld
    * from traps gets no judgment point at all, its members included: in a
    * family where some judgment points are traps, a point whose judgment
    * points all expect member could be answered `proved` without reading
    * anything.
    */
  private def rows(
      source: PointSource,
      budget: Long,
      judgments: Option[JudgmentPoints],
      secondPoints: Map[String, SecondPoint]
  ): Either[NormalFormReading, SourceRows] = source match
    case evaluation @ PointSource.EvaluationSource(name, stage, family, _, program, reference, computedCandidates) =>
      Vector(name, stage, family).foreach(textChecked)
      referenceReading(DrawnPoint(program, reference), budget) match
        case NormalFormReading.Finished(normalForms) =>
          // The program's instruction, converted once for its rows and its traps.
          val programInstruction = closedTerm(program)
          val evaluationRow = WrittenRow.EvaluationRow(evaluation, programInstruction, normalForms)
          judgments match
            case None => Right(SourceRows(Vector(evaluationRow), None, None))
            case Some(JudgmentPoints(judgmentWeight, judgmentsOnly, trapDraw)) =>
              val (trapCandidates, trapOutcome) = trapDraw match
                case None => (Vector.empty, None)
                case Some(TrapDraw(_, count)) =>
                  val secondPoint = secondPoints.getOrElse(
                    name,
                    throw IllegalArgumentException(s"the second instance has no evaluation point $name")
                  )
                  val (found, outcome) = traps(name, programInstruction, normalForms, computedCandidates, secondPoint, secondPoints, budget, count)
                  (found, Some(outcome))
              val judged = trapOutcome match
                case Some(TrapOutcome.Withheld(_)) => Vector.empty
                case _                             => judgmentPoints(evaluation, normalForms, trapCandidates, judgmentWeight)
              val programRow = judged.headOption.map(first => ProgramRow(first.pointName, first.family, programInstruction))
              val judgmentRows = programRow.toVector.flatMap(found => judged.map(WrittenRow.JudgmentRow(_, found.name)))
              Right(SourceRows((if judgmentsOnly then Vector.empty else Vector(evaluationRow)) ++ judgmentRows, programRow, trapOutcome))
        case stopped => Left(stopped)
    case judgment: PointSource.JudgmentSource =>
      Vector(judgment.name, judgment.stage, judgment.family).foreach(textChecked)
      Right(SourceRows(Vector(WrittenRow.JudgmentRow(judgment, judgment.pointName)), Some(ProgramRow(judgment.pointName, judgment.family, closedTerm(judgment.program))), None))

  /** The rows a source writes to the points file, the program its judgment
    * points judge, written once to the programs file, and, for an
    * evaluation source under a trap draw, its trap outcome.
    */
  private final case class SourceRows(rows: Vector[WrittenRow], program: Option[ProgramRow], trapOutcome: Option[TrapOutcome])

  /** A row of the programs file: the program's name, the family of the
    * judgment points that refer to it, and the program, whose line is made
    * only when the file is written.
    */
  private final case class ProgramRow(name: String, family: String, program: Configured[NoFacts.type]):
    def text: String = Vector(name, family, ExchangeText.line(program)).mkString("\t")

  /** A row of the points file, whose text is made only when the file is
    * written (`rows` checks its name, stage and family before, so that a
    * bad row is refused before the file is opened).
    */
  private enum WrittenRow:
    case EvaluationRow(source: PointSource.EvaluationSource, program: Configured[NoFacts.type], normalForms: Vector[gezi.contest.corpora.common.ProblemDeBruijnTerm])
    case JudgmentRow(source: PointSource.JudgmentSource, programName: String)

    def name: String = this match
      case EvaluationRow(source, _, _) => source.name
      case JudgmentRow(source, _)   => source.name

    def stage: String = this match
      case EvaluationRow(source, _, _) => source.stage
      case JudgmentRow(source, _)   => source.stage

    def family: String = this match
      case EvaluationRow(source, _, _) => source.family
      case JudgmentRow(source, _)   => source.family

    def text: String = this match
      case EvaluationRow(source, program, normalForms) =>
        Vector(
          name,
          stage,
          family,
          source.weight.toString,
          "evaluation",
          ExchangeText.line(program),
          "",
          ExchangeText.normalFormsLine(normalForms.map(Defunctionalization.thunkInstruction[NoFacts.type](_)).sortBy(ExchangeText.line))
        ).mkString("\t")
      case JudgmentRow(source, programName) =>
        Vector(
          name,
          stage,
          family,
          source.weight.toString,
          "judgment",
          s"@$programName",
          ExchangeText.line(closedTerm(source.candidate)),
          if source.member then "member" else "not_member"
        ).mkString("\t")

  private def textChecked(text: String): Unit =
    if text.exists(character => character == '\t' || character == '\n' || character == '\r') then
      throw IllegalArgumentException(s"the text ${text.take(40)} holds a tab or a line break")

  /** The line of a normal form, by which candidates are ranked. */
  private def line(term: gezi.contest.corpora.common.ProblemDeBruijnTerm): String = ExchangeText.line(Defunctionalization.thunkInstruction[NoFacts.type](term))

  /** The instruction of a HOAS program or candidate, each closed
    * instruction it holds (`Term.closed`, a library term read by projection)
    * the instruction it is, not read back into a tree, so that its line is
    * written at the size of its graph.
    * An opaque instruction stays one, and `ExchangeText.line` throws for it.
    */
  def closedTerm(term: gezi.contest.corpora.common.ProblemTerm): Configured[NoFacts.type] = Defunctionalization.thunkInstruction[NoFacts.type](term.deBruijnTerm(Map.empty))

  /** The points by family, in the order the seed draws (`SeededOrder`):
    * the family names, sorted, shuffled from the seed, then each family's
    * points, sorted by name, shuffled in turn, the state carried from one
    * shuffle to the next; so every entry reads the same order, a family's
    * points one after another. Throws `IllegalArgumentException` for a name
    * written twice.
    */
  def ordered(points: Vector[Point], seed: Long): Vector[(String, Vector[Point])] =
    val byFamily = points.groupBy(_.family)
    val (families, afterFamilies) = SeededOrder.shuffled(byFamily.keys.toVector.sorted, seed)
    families
      .foldLeft((Vector.empty[(String, Vector[Point])], afterFamilies)) { case ((done, state), family) =>
        val (members, after) = SeededOrder.shuffled(byFamily(family).sortBy(_.name), state)
        (done :+ (family -> members), after)
      }
      ._1

/** A row of `ComputedReferences`: an evaluation point whose reference its
  * family computed, the point's family, and the claim, the test that checks
  * the computed reference against tabling(weak_head)'s reading.
  */
final case class ComputedReference(point: String, family: String, claim: String)

/** The provenance of a points file's computed references,
  * `computed-references.tsv` beside `points.tsv`, which has no column for
  * it: a header naming the columns, then one row per evaluation source
  * whose reference is `Reference.Computed`, in source order, tab-separated.
  */
object ComputedReferences:

  val fileName: String = "computed-references.tsv"

  val header: String = "point\tfamily\tclaim"

  /** The rows of the sources. */
  def of(sources: Vector[PointSource]): Vector[ComputedReference] =
    sources.collect { case PointSource.EvaluationSource(name, _, family, _, _, Reference.Computed(_, claim), _) =>
      ComputedReference(name, family, claim)
    }

  /** Writes the file of the sources' computed references to the directory,
    * the header alone when there is none. Throws `IllegalArgumentException`
    * for a field holding a tab or a line break.
    */
  def written(directory: Path, sources: Vector[PointSource]): Vector[ComputedReference] =
    val rows = of(sources)
    val lines = rows.map(row =>
      Vector(row.point, row.family, row.claim).foreach(text =>
        if text.exists(character => character == '\t' || character == '\n' || character == '\r') then
          throw IllegalArgumentException(s"the text ${text.take(40)} holds a tab or a line break")
      )
      Vector(row.point, row.family, row.claim).mkString("\t")
    )
    Files.createDirectories(directory)
    Files.writeString(directory.resolve(fileName), (header +: lines).mkString("", "\n", "\n"))
    rows

  /** The rows of the directory's file, in file order. Throws
    * `IllegalArgumentException` naming the file and the line for a missing
    * or other header or a line of other than three fields.
    */
  def read(directory: Path): Vector[ComputedReference] =
    val file = directory.resolve(fileName)
    val lines = Files.readAllLines(file, StandardCharsets.UTF_8).asScala.toVector
    if lines.headOption != Some(header) then throw IllegalArgumentException(s"$file:1: the header is not $header")
    lines.zipWithIndex.drop(1).map((line, index) =>
      line.split("\t", -1).toVector match
        case Vector(point, family, claim) => ComputedReference(point, family, claim)
        case fields                       => throw IllegalArgumentException(s"$file:${index + 1}: ${fields.size} fields, not 3")
    )
