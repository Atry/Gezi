package gezi.contest.runner

import java.util.Locale
import gezi.contest.entry.Count
import gezi.contest.entry.OutputDisplay
import gezi.contest.entry.Phase
import gezi.contest.entry.Report
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.ExchangeText
import gezi.hotspot.LifecycleEvent
import gezi.ir.Instruction

/** The lines of the judge's pipe. Every term is an `ExchangeText.line`, which holds no tab and no
  * newline; fields are tab-separated. The judge writes a cell as the
  * instruction it holds; the entry is given the cell as the de Bruijn term of
  * the instruction its line reads as, and its display is written as the
  * line of its instruction and read as the instruction, never as a tree.
  *
  *   - a cell: `<name> cell <cell>`, a closed term `State → (State,
  *     Output)`; the name
  *     is the judge's and never reaches the entry;
  *   - a lifecycle event of the cache service, which the supervisor writes
  *     (`lifecycle round_started`, `lifecycle family_started`,
  *     `lifecycle family_finished`, `lifecycle round_finished`), answered,
  *     once the entry has taken it, by the line `lifecycle_done`
  *     (`lifecycleDone`);
  *   - `cancel` (`cancelLine`), which the supervisor writes while a cell
  *     is read and its point's budget has run out: the entry's current call
  *     is asked to stop; it
  *     is answered by the cell's answer line, if the call returns in time;
  *   - a cell's answer: `answer <name> <phases> <display>`, the display of
  *     the cell's Output that the entry finished with.
  *
  * The field `<phases>` is the reports the entry gave for the cell
  * (`Interaction.Finished`, `phasesField`): `-` when there are none, else each
  * phase written `<name>:<seconds>`, the seconds with six decimals, and each
  * count `<name>#<value>`, joined by `;` in the order reported.
  *
  * The runner reads cells and writes answers; the supervisor writes cells
  * and reads answers. Every answer line starts with the field `answer`
  * (`answerPrefix`) followed by a tab: the JVM writes its own messages on the
  * same standard output (with `-XX:+ExitOnOutOfMemoryError`, the line
  * `Terminating due to java.lang.OutOfMemoryError: Java heap space`), and no
  * message of the JVM starts with that field and a tab.
  */
object PipeLines:

  /** The first field of every answer line. */
  val answerPrefix: String = "answer"

  /** What a line of the pipe where an answer is awaited is: an answer line,
    * its cell's name, the phases and the display, or any other line, which the
    * supervisor reads as the reader no longer answering. The line comes from
    * an untrusted process, the entry's JVM, so a line that is not an answer
    * is an expected input, not an error.
    */
  enum AnswerRead:
    case Answer(name: String, phases: Vector[Report], display: OutputDisplay)
    case NotAnswer(line: String)

  /** What a line the supervisor writes is: a cell, a lifecycle event of
    * the cache service that the runner hands to the entry and answers with the
    * line `lifecycleDone`, or the cancel of the call in progress
    * (`cancelLine`).
    */
  enum Received:
    case Cell(name: String, cell: DeBruijnTerm)
    case Lifecycle(event: LifecycleEvent)
    case Cancel

  /** The line that asks the entry's current call to stop: one field, so
    * that no cell line (three fields) and no lifecycle line (two) is read
    * as it.
    */
  val cancelLine: String = "cancel"

  /** The first field of a lifecycle line. */
  val lifecyclePrefix: String = "lifecycle"

  /** The line the runner writes once the entry has taken a lifecycle event,
    * so that the supervisor knows when the event's work is over and can
    * start the next cell's clock after it. No answer line is this line
    * (an answer line starts with `answerPrefix` and a tab).
    */
  val lifecycleDone: String = "lifecycle_done"

  /** The line of a lifecycle event: `lifecycle <event>`, the event's name in
    * lowercase words joined by underscores (`family_started`).
    */
  def lifecycleLine(event: LifecycleEvent): String = s"$lifecyclePrefix\t${eventName(event)}"

  /** What the line is: the cancel line, of one field; a lifecycle line, of
    * exactly two fields; or a cell line (`cellRead`), of three, so that a
    * cell of any name, `lifecycle` and `cancel` included, is read as a cell.
    * Throws `IllegalArgumentException` for any other line.
    */
  def receivedRead(text: String): Received = text.split('\t').toVector match
    case Vector(`cancelLine`) => Received.Cancel
    case Vector(`lifecyclePrefix`, name) =>
      LifecycleEvent.values.find(eventName(_) == name) match
        case Some(event) => Received.Lifecycle(event)
        case None        => throw IllegalArgumentException(s"no lifecycle event $name")
    case _ =>
      val (name, cell) = cellRead(text)
      Received.Cell(name, cell)

  /** The event's name: `RoundStarted` is `round_started`. */
  private def eventName(event: LifecycleEvent): String =
    event.toString.replaceAll("([a-z])([A-Z])", "$1_$2").toLowerCase(Locale.ROOT)

  /** The line of the cell. */
  def cellLine(name: String, cell: Instruction): String = s"$name\tcell\t${ExchangeText.line(cell)}"

  /** Whether the line is a cell line, `receivedRead`'s `Received.Cell`,
    * told by its fields alone, before its term is read.
    */
  def isCellLine(text: String): Boolean = text.split('\t').toVector match
    case Vector(_, "cell", _) => true
    case _                    => false

  /** The name and the cell of a line `cellLine` writes, the cell the de
    * Bruijn term of the instruction its line reads as, which an entry is
    * given (`gezi.contest.entry.Entry.run`), with each filling of the cell's
    * thunk, a closed instruction, written as a `Constant`
    * (`cellTerm`).
    */
  def cellRead(text: String): (String, DeBruijnTerm) = text.split('\t').toVector match
    case Vector(name, "cell", cell) => (name, cellTerm(term(cell)))
    case _                          => throw IllegalArgumentException(s"no cell line: ${text.take(80)}")

  /** The de Bruijn term of a cell's instruction, each filling of its thunk
    * written as a `Constant` rather than read back, and each side of a
    * filling that is a parallel (`Defunctionalization.instructionTerm` with
    * those as stops): a point's cell `λs.λk. k s p` reads as `λs.λk. k s p`
    * with p a constant, and a judgment's `λs.λk. k s (N ∥ p)` with N and p
    * constants under a parallel an entry can tell, and the front end turns
    * each constant back into its instruction itself. A filling of a
    * closed thunk is closed, so the constant stands for exactly the term the
    * full readback writes out. Reading the program back into a tree instead
    * loses the IR's sharing, and so does writing the tree back to the IR:
    * measured 2026-11-21 on generated points of the list program families,
    * the two together took 7.7 s of a 10 s point on the longest common
    * subsequences at 4 repetitions, and the readback of the edit distances at
    * 1 repetition ran a 1.5 GB heap out of memory, neither reading the
    * judge's cancel.
    */
  def cellTerm(cell: Instruction): DeBruijnTerm = cell match
    case Instruction.Thunk(_, _, fillings) =>
      Defunctionalization.instructionTerm(
        cell,
        fillings.flatMap {
          case Instruction.Parallel(left, right) => Vector(left, right)
          case filling                           => Vector(filling)
        }.toSet
      )
    case _ => Defunctionalization.instructionTerm(cell)

  def answerLine(name: String, phases: Vector[Report], display: OutputDisplay): String =
    Vector(answerPrefix, name, phasesField(phases), display.written(ExchangeText.line)).mkString("\t")

  /** The display of a field `OutputDisplay.written` writes with the lines
    * of terms, or none for any other text: the instruction the line reads
    * as, never read back into a tree, which a short line of an untrusted
    * process can make too large to build.
    */
  private def displayRead(text: String): Option[OutputDisplay] =
    if text == ExchangeText.noNormalFormLine then Some(OutputDisplay.NoNormalForm)
    else ExchangeText.term(text).toOption.map(OutputDisplay.Shown(_))

  /** The answer of a line `answerLine` writes, or `NotAnswer` for any other
    * line: one without the prefix, with another number of fields, with a
    * phases field `phasesRead` does not read, or with a display that is
    * neither the line of no normal form nor the line of a closed term
    * (`ExchangeText.term`, which also rejects another spelling of the same
    * term).
    */
  def answerRead(text: String): AnswerRead = text.split("\t", -1).toVector match
    case Vector(`answerPrefix`, name, phasesText, displayText) =>
      phasesRead(phasesText)
        .flatMap(phases => displayRead(displayText).map(AnswerRead.Answer(name, phases, _)))
        .getOrElse(AnswerRead.NotAnswer(text))
    case _ => AnswerRead.NotAnswer(text)

  /** The reports written as one field: `-` when there are none, else each
    * phase `<name>:<seconds>`, the seconds with six decimals, and each count
    * `<name>#<value>`, joined by `;`. The field holds no tab and no newline,
    * since a report's name is of lowercase letters and underscores.
    */
  def phasesField(phases: Vector[Report]): String =
    if phases.isEmpty then "-"
    else
      phases
        .map {
          case Phase(name, seconds) => s"$name:${"%.6f".formatLocal(Locale.ROOT, seconds)}"
          case Count(name, value)   => s"$name#$value"
        }
        .mkString(";")

  /** The reports of a field `phasesField` writes, or none for any other
    * text: an item that is neither a phase nor a count as `phasesField`
    * writes them, a name `Phase` or `Count` refuses, seconds that are not six
    * decimals of a number `Phase` accepts, or a count that is not digits. A
    * field of phases only, as entries wrote before counts, reads as before.
    * The field comes from an untrusted process, so a malformed field is an
    * expected input, not an error.
    */
  def phasesRead(field: String): Option[Vector[Report]] =
    if field == "-" then Some(Vector.empty)
    else
      val read = field.split(";", -1).toVector.map(reportRead)
      Option.when(read.forall(_.isDefined))(read.flatten)

  /** The report of a text `<name>:<seconds>` or `<name>#<value>` as
    * `phasesField` writes it, or none for any other text.
    */
  private def reportRead(text: String): Option[Report] = text.split(":", -1).toVector match
    case Vector(name, seconds) if Phase.namePattern.matches(name) && secondsPattern.matches(seconds) =>
      seconds.toDoubleOption.filter(_.isFinite).map(Phase(name, _))
    case Vector(counted) =>
      counted.split("#", -1).toVector match
        case Vector(name, value) if Phase.namePattern.matches(name) && countPattern.matches(value) =>
          value.toLongOption.map(Count(name, _))
        case _ => None
    case _ => None

  /** The values `phasesField` writes for a count: digits. */
  private val countPattern: scala.util.matching.Regex = "[0-9]+".r

  /** The seconds `phasesField` writes: digits, a point and six decimals. */
  private val secondsPattern: scala.util.matching.Regex = """[0-9]+\.[0-9]{6}""".r

  private def term(text: String): Instruction =
    ExchangeText.term(text).fold(reason => throw IllegalArgumentException(s"no term on the pipe: $reason"), identity)
