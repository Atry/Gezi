package gezi.contest.runner

import java.util.Locale
import gezi.contest.entry.Count
import gezi.contest.entry.OutputDisplay
import gezi.contest.entry.Phase
import gezi.contest.entry.Report
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.frontend.ExchangeText
import gezi.hotspot.LifecycleEvent
import gezi.ir.{Configured, NativeSpecializer, NoFacts, StorageAccess}
import gezi.weakhead.ScottADTChoices

/** The lines of the judge's pipe. Every term is an `ExchangeText.line`, which
  * holds no tab and no newline; fields are tab-separated. The judge writes a
  * point as the lines of its terms, as its points file holds them, and the
  * runner builds the point's cell from them (`pointCell`), in the configuration
  * of the entry it serves (`Entry.specializer`); the entry is given the cell as
  * the de Bruijn term of that term, and its display is written as the line of
  * its Scott ADT values (the Scott ADT reading of `ReadableText`) or of its
  * remainder, and the judge reads the line as a term under no facts, never as a
  * tree.
  *
  *   - a point, which the runner reads as a cell, a closed term `State →
  *     (State, Output)`: an evaluation `<name> evaluation <program>`, whose
  *     cell is `λs.λk. k s p`, or a judgment of a candidate
  *     `<name> judgment <candidate> <program>`, whose cell is
  *     `λs.λk. k s (N ∥ p)`, p the program and N the candidate. The name and
  *     the kind are the judge's and never reach the entry: only the runner
  *     reads the pipe, and an entry is given the cell alone
  *     (`gezi.contest.entry.Entry.run`), as it was when the judge wrote the
  *     cell's line itself. A judgment's cell shows its kind as a parallel at
  *     its root, so the pipe tells the runner nothing the cell does not. The
  *     judge holds a program as the line its points file writes and never as an
  *     instruction, so that its heap holds the file's text and not the
  *     programs' IR; the runner reads the line on the point's clock, as it read
  *     the cell's line before;
  *   - a lifecycle event of the cache service, which the supervisor writes
  *     (`lifecycle round_started`, `lifecycle family_started`,
  *     `lifecycle family_finished`, `lifecycle round_finished`), answered, once
  *     the entry has taken it, by the line `lifecycle_done` (`lifecycleDone`);
  *   - `cancel` (`cancelLine`), which the supervisor writes while a cell is
  *     read and its point's budget has run out: the entry's current call is
  *     asked to stop; it is answered by the cell's answer line, if the call
  *     returns in time;
  *   - a cell's answer: `answer <name> <phases> <display>`, the display of the
  *     cell's Output that the entry finished with.
  *
  * The field `<phases>` is the reports the entry gave for the cell
  * (`Interaction.Finished`, `phasesField`): `-` when there are none, else each
  * phase written `<name>:<seconds>`, the seconds with six decimals, and each
  * count `<name>#<value>`, joined by `;` in the order reported.
  *
  * The runner reads cells and writes answers; the supervisor writes cells and
  * reads answers. Every answer line starts with the field `answer`
  * (`answerPrefix`) followed by a tab: the JVM writes its own messages on the
  * same standard output (with `-XX:+ExitOnOutOfMemoryError`, the line
  * `Terminating due to java.lang.OutOfMemoryError: Java heap space`), and no
  * message of the JVM starts with that field and a tab.
  */
object PipeLines:

  /** The first field of every answer line. */
  val answerPrefix: String = "answer"

  /** What a line of the pipe where an answer is awaited is: an answer line, its
    * cell's name, the phases and the display, or any other line, which the
    * supervisor reads as the reader no longer answering. The line comes from an
    * untrusted process, the entry's JVM, so a line that is not an answer is an
    * expected input, not an error.
    */
  enum AnswerRead:
    case Answer(
        name: String,
        phases: Vector[Report],
        display: OutputDisplay[NoFacts.type]
    )
    case NotAnswer(line: String)

  /** What a line the supervisor writes is: a point's cell, a lifecycle event of
    * the cache service that the runner hands to the entry and answers with the
    * line `lifecycleDone`, or the cancel of the call in progress
    * (`cancelLine`).
    */
  enum Received[+Constant]:
    case Cell(name: String, cell: DeBruijnTermOf[Constant])
    case Lifecycle(event: LifecycleEvent)
    case Cancel

  /** The line that asks the entry's current call to stop: one field, so that no
    * cell line (three fields) and no lifecycle line (two) is read as it.
    */
  val cancelLine: String = "cancel"

  /** The first field of a lifecycle line. */
  val lifecyclePrefix: String = "lifecycle"

  /** The line the runner writes once the entry has taken a lifecycle event, so
    * that the supervisor knows when the event's work is over and can start the
    * next cell's clock after it. No answer line is this line (an answer line
    * starts with `answerPrefix` and a tab).
    */
  val lifecycleDone: String = "lifecycle_done"

  /** The line of a lifecycle event: `lifecycle <event>`, the event's name in
    * lowercase words joined by underscores (`family_started`).
    */
  def lifecycleLine(event: LifecycleEvent): String =
    s"$lifecyclePrefix\t${eventName(event)}"

  /** What the line is: the cancel line, of one field; a lifecycle line, of
    * exactly two fields; or a point's line (`cellRead`), of three or four, so
    * that a point of any name, `lifecycle` and `cancel` included, is read as a
    * cell. Throws `IllegalArgumentException` for any other line.
    */
  def receivedRead[C <: NativeSpecializer & Singleton](
      text: String
  )(using C, StorageAccess): Received[Configured[C]] =
    text.split('\t').toVector match
      case Vector(`cancelLine`)            => Received.Cancel
      case Vector(`lifecyclePrefix`, name) =>
        LifecycleEvent.values.find(eventName(_) == name) match
          case Some(event) => Received.Lifecycle(event)
          case None        =>
            throw IllegalArgumentException(s"no lifecycle event $name")
      case _ =>
        val (name, cell) = cellRead[C](text)
        Received.Cell(name, cell)

  /** The event's name: `RoundStarted` is `round_started`. */
  private def eventName(event: LifecycleEvent): String =
    event.toString
      .replaceAll("([a-z])([A-Z])", "$1_$2")
      .toLowerCase(Locale.ROOT)

  /** The line of an evaluation point, its program given as its line. */
  def evaluationLine(name: String, programLine: String): String =
    s"$name\t$evaluationKind\t$programLine"

  /** The line of a judgment point, its candidate and its program given as their
    * lines.
    */
  def judgmentLine(
      name: String,
      candidateLine: String,
      programLine: String
  ): String =
    s"$name\t$judgmentKind\t$candidateLine\t$programLine"

  private val evaluationKind: String = "evaluation"

  private val judgmentKind: String = "judgment"

  /** The cell of a point whose Output is the term: `λs.λk. k s t`
    * (`gezi.contest.entry.Cells.cell`), the term a constant, so that the cell
    * is converted with it as it is, never read back into a tree. For an
    * evaluation the term is the program; for a judgment the parallel of the
    * candidate and the program.
    */
  def pointCell[C <: NativeSpecializer & Singleton](
      output: Configured[C]
  )(using C): Configured[C] =
    Defunctionalization.thunkInstruction[C](
      gezi.contest.entry.Cells
        .cell[Configured[C]](DeBruijnTerm.Constant[Configured[C]](output))
    )

  /** Whether the line is a point's line, `receivedRead`'s `Received.Cell`, told
    * by its fields alone, before its terms are read.
    */
  def isCellLine(text: String): Boolean = text.split('\t').toVector match
    case Vector(_, `evaluationKind`, _)  => true
    case Vector(_, `judgmentKind`, _, _) => true
    case _                               => false

  /** The name and the cell of a line `evaluationLine` or `judgmentLine` writes:
    * the cell of the point (`pointCell`) built from the instructions its lines
    * read as, as the de Bruijn term an entry is given
    * (`gezi.contest.entry.Entry.run`), with each filling of the cell's thunk, a
    * closed instruction, written as a `Constant` (`cellTerm`).
    */
  def cellRead[C <: NativeSpecializer & Singleton](text: String)(using
      specializer: C,
      access: StorageAccess
  ): (String, DeBruijnTermOf[Configured[C]]) =
    text.split('\t').toVector match
      case Vector(name, `evaluationKind`, program) =>
        (name, cellTerm(pointCell(term[C](program))))
      case Vector(name, `judgmentKind`, candidate, program) =>
        (
          name,
          cellTerm(
            pointCell(
              specializer.parallel(term[C](candidate), term[C](program))
            )
          )
        )
      case _ =>
        throw IllegalArgumentException(s"no point line: ${text.take(80)}")

  /** The de Bruijn term of a cell's instruction, each filling of its thunk
    * written as a `Constant` rather than read back, and each side of a filling
    * that is a parallel (`Defunctionalization.instructionTerm` with those as
    * stops): a point's cell `λs.λk. k s p` reads as `λs.λk. k s p` with p a
    * constant, and a judgment's `λs.λk. k s (N ∥ p)` with N and p constants
    * under a parallel an entry can tell, and the front end turns each constant
    * back into its instruction itself. A filling of a closed thunk is closed,
    * so the constant stands for exactly the term the full readback writes out.
    * Reading the program back into a tree instead loses the IR's sharing, and
    * so does writing the tree back to the IR: measured 2026-11-21 on generated
    * points of the list program families, the two together took 7.7 s of a 10 s
    * point on the longest common subsequences at 4 repetitions, and the
    * readback of the edit distances at 1 repetition ran a 1.5 GB heap out of
    * memory, neither reading the judge's cancel.
    */
  def cellTerm[C <: NativeSpecializer & Singleton](cell: Configured[C])(using
      C
  ): DeBruijnTermOf[Configured[C]] = cell.layer match
    case gezi.ir.Thunk(_, _, fillings) =>
      Defunctionalization.instructionTerm[C](
        cell,
        fillings
          .flatMap(filling =>
            filling.layer match
              case gezi.ir.Parallel(left, right) => Vector(left, right)
              case _                             => Vector(filling)
          )
          .toSet
      )
    case _ => Defunctionalization.instructionTerm[C](cell)

  def answerLine[C <: NativeSpecializer & Singleton](
      name: String,
      phases: Vector[Report],
      display: OutputDisplay[C]
  )(using C, StorageAccess): String =
    Vector(answerPrefix, name, phasesField(phases), displayWritten(display))
      .mkString("\t")

  /** The display as the line of its field: the Scott ADT values as the Scott
    * ADT reading writes them (`ExchangeText.scottADTLine`, each member with its
    * filters back, `ScottADTChoices.withFilters`), a remainder as the exchange
    * format writes any term of the configuration, both on one line, bound by
    * one table, when the display has both (`ExchangeText.mixedLine`); no Scott
    * ADT value at all as the format's own line of no normal form.
    */
  private def displayWritten[C <: NativeSpecializer & Singleton](
      display: OutputDisplay[C]
  )(using C, StorageAccess): String = display match
    case OutputDisplay.Values(choices) =>
      ExchangeText.scottADTLine(
        ScottADTChoices.members(choices).map(ScottADTChoices.withFilters)
      )
    case OutputDisplay.Remainder(term)           => ExchangeText.line(term)
    case OutputDisplay.Mixed(choices, remainder) =>
      ExchangeText.mixedLine(
        ScottADTChoices.members(choices).map(ScottADTChoices.withFilters),
        remainder
      )

  /** The display of a field `answerLine` writes, or none for any other text,
    * read under no facts as the judge reads every line: the line of no normal
    * form is the display of no Scott ADT value, any other line the term it
    * reads as, the remainder whose members the judge classifies one by one
    * (`Supervisor.asserted`), never read back into a tree, which a short line
    * of an untrusted process can make too large to build.
    */
  private def displayRead(text: String): Option[OutputDisplay[NoFacts.type]] =
    given NoFacts.type = NoFacts
    given StorageAccess = noFactsAccess
    if text == ExchangeText.noNormalFormLine then
      Some(OutputDisplay.noScottADTValue[NoFacts.type])
    else
      ExchangeText
        .term[NoFacts.type](text)
        .toOption
        .map(OutputDisplay.Remainder(_))

  /** The capability to read a storage's view under no facts, which have none:
    * the judge reads a line's terms with it.
    */
  private val noFactsAccess: StorageAccess = StorageAccess.granted()

  /** The answer of a line `answerLine` writes, or `NotAnswer` for any other
    * line: one without the prefix, with another number of fields, with a phases
    * field `phasesRead` does not read, or with a display that is neither the
    * line of no normal form nor the line of a closed term (`ExchangeText.term`,
    * which also rejects another spelling of the same term).
    */
  def answerRead(text: String): AnswerRead = text.split("\t", -1).toVector match
    case Vector(`answerPrefix`, name, phasesText, displayText) =>
      phasesRead(phasesText)
        .flatMap(phases =>
          displayRead(displayText).map(AnswerRead.Answer(name, phases, _))
        )
        .getOrElse(AnswerRead.NotAnswer(text))
    case _ => AnswerRead.NotAnswer(text)

  /** The reports written as one field: `-` when there are none, else each phase
    * `<name>:<seconds>`, the seconds with six decimals, and each count
    * `<name>#<value>`, joined by `;`. The field holds no tab and no newline,
    * since a report's name is of lowercase letters and underscores.
    */
  def phasesField(phases: Vector[Report]): String =
    if phases.isEmpty then "-"
    else
      phases
        .map {
          case Phase(name, seconds) =>
            s"$name:${"%.6f".formatLocal(Locale.ROOT, seconds)}"
          case Count(name, value) => s"$name#$value"
        }
        .mkString(";")

  /** The reports of a field `phasesField` writes, or none for any other text:
    * an item that is neither a phase nor a count as `phasesField` writes them,
    * a name `Phase` or `Count` refuses, seconds that are not six decimals of a
    * number `Phase` accepts, or a count that is not digits. A field of phases
    * only, as entries wrote before counts, reads as before. The field comes
    * from an untrusted process, so a malformed field is an expected input, not
    * an error.
    */
  def phasesRead(field: String): Option[Vector[Report]] =
    if field == "-" then Some(Vector.empty)
    else
      val read = field.split(";", -1).toVector.map(reportRead)
      Option.when(read.forall(_.isDefined))(read.flatten)

  /** The report of a text `<name>:<seconds>` or `<name>#<value>` as
    * `phasesField` writes it, or none for any other text.
    */
  private def reportRead(text: String): Option[Report] =
    text.split(":", -1).toVector match
      case Vector(name, seconds)
          if Phase.namePattern
            .matches(name) && secondsPattern.matches(seconds) =>
        seconds.toDoubleOption.filter(_.isFinite).map(Phase(name, _))
      case Vector(counted) =>
        counted.split("#", -1).toVector match
          case Vector(name, value)
              if Phase.namePattern
                .matches(name) && countPattern.matches(value) =>
            value.toLongOption.map(Count(name, _))
          case _ => None
      case _ => None

  /** The values `phasesField` writes for a count: digits. */
  private val countPattern: scala.util.matching.Regex = "[0-9]+".r

  /** The seconds `phasesField` writes: digits, a point and six decimals. */
  private val secondsPattern: scala.util.matching.Regex =
    """[0-9]+\.[0-9]{6}""".r

  private def term[C <: NativeSpecializer & Singleton](
      text: String
  )(using C, StorageAccess): Configured[C] =
    ExchangeText
      .term[C](text)
      .fold(
        reason =>
          throw IllegalArgumentException(s"no term on the pipe: $reason"),
        identity
      )
