package com.yang_bo.gezi.jupyter.kernel

import almond.interpreter.Interpreter
import almond.interpreter.IsCompleteResult
import almond.interpreter.Message
import almond.interpreter.api.DisplayData
import almond.interpreter.api.ExecuteResult
import almond.interpreter.api.OutputHandler
import almond.interpreter.input.InputManager
import almond.protocol.Execute
import almond.protocol.KernelInfo
import java.nio.file.Path
import com.yang_bo.gezi.contest.entry.Cells
import com.yang_bo.gezi.contest.entry.Entry
import com.yang_bo.gezi.contest.entry.Interaction
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.contest.entry.OutputDisplay
import com.yang_bo.gezi.weakhead.ScottADTChoices
import com.yang_bo.gezi.directorysugar.DirectoryTree
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.LambdalatticeMalformed
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ir.{Closed, Configured, NativeSpecializer, StorageAccess}
import com.yang_bo.gezi.frontend.DeBruijnTermOf

/** The kernel's session of the configuration `C` of its entry: the notebook,
  * the entry as the cells so far left it (what its executor keeps from call to
  * call, `Interaction.Finished`), and the count of cells. The kernel holds it
  * as a `Session[?]` and opens it for each message by a method generic in `C`
  * (capture conversion), never by a type pattern.
  */
final case class Session[C <: NativeSpecializer & Singleton](
    notebook: Notebook[C],
    entry: Entry[C],
    count: Int
)

/** The Jupyter kernel of lambdalattice cells, an adapter of almond's
  * `Interpreter`, whose cells are the mixins of one notebook: each cell's
  * content is read after the notebook's location (`NotebookLocation.prefix`),
  * the cells are joined by choice with the tree of URIs (`Notebook`), and a
  * cell whose content is a chain of + of partial functions outputs the members
  * at its key paths (`CellContent`): a value as the entry the kernel was
  * started with reads it, and a member under `"io"` as a Moore machine state
  * (`CONTRIBUTING.md`, "Terms"). The kernel runs no evaluator itself
  * (CONTRIBUTING.md, "The Architecture"): each member is the Output of a cell
  * it hands the entry (`Entry.run`), and the entry each run returns runs the
  * next. Only the new cell's keys are read; an earlier cell is not run again.
  *
  * FIXME: a later cell that adds a value to an earlier cell's
  * https://github.com/Atry/private-overlay/issues/2005 key leaves the earlier
  * cell's output stale. Candidate fix: Jupyter's `display_id` and
  * `update_display_data`, as Pluto.jl updates the cells a change reaches.
  *
  * almond keeps one interpreter across cells and calls `execute` synchronously,
  * so the kernel's state stands in one mutable cell, the module's one mutable
  * line, which the whole module's exception covers ([[com.yang_bo.gezi.jupyter.kernel]]).
  */
@SuppressWarnings(
  Array("com.yang_bo.gezi.warts.NoJavaUtilConcurrent")
) // 可以用almond。可以把整个基于almond的适配层都当成”局部“ (the user, 2026-11-02)
final class CellInterpreter(initial: Session[?], traces: Option[CellTraces])
    extends Interpreter:

  // 可以用almond。可以把整个基于almond的适配层都当成”局部“
  private val current =
    java.util.concurrent.atomic.AtomicReference[Session[?]](initial)

  // 可以用almond。可以把整个基于almond的适配层都当成”局部“: the count of the
  // interrupts Jupyter has sent, which almond's control thread raises while a
  // cell runs on the interpreter's thread (`CellInterpreter.Interrupted`).
  private val interrupts = java.util.concurrent.atomic.AtomicLong(0)

  override def interruptSupported: Boolean = true

  override def interrupt(): Unit =
    val _ = interrupts.incrementAndGet()

  def kernelInfo(): KernelInfo =
    KernelInfo(
      "lambdalattice",
      "0.1.0",
      KernelInfo.LanguageInfo(
        "lambdalattice",
        "0.1.0",
        "text/x-lambdalattice",
        ".lambdalattice",
        "text"
      ),
      "lambdalattice cells: the mixins of one notebook, a chain of + of partial functions outputting the members at their keys"
    )

  def execute(
      code: String,
      storeHistory: Boolean,
      inputManager: Option[InputManager],
      outputHandler: Option[OutputHandler],
      messageOpt: Option[Message[Execute.Request]]
  ): ExecuteResult =
    // The count of interrupts read before anything else, so that an
    // interrupt that arrives while the cell is still being read stops it.
    val interrupted =
      CellInterpreter.Interrupted(() => interrupts.get, interrupts.get)
    val (after, result) =
      executed(current.get, code, storeHistory, messageOpt, interrupted)
    current.set(after)
    result

  /** The cell run in the session of the configuration `C`: the session after it
    * and the result.
    */
  private def executed[C <: NativeSpecializer & Singleton](
      state: Session[C],
      code: String,
      storeHistory: Boolean,
      messageOpt: Option[Message[Execute.Request]],
      interrupted: CellInterpreter.Interrupted
  ): (Session[C], ExecuteResult) =
    given C = state.entry.specializer
    given StorageAccess = CellInterpreter.storageAccess
    val id = messageOpt
      .flatMap(CellInterpreter.cellId)
      .getOrElse(s"execution ${state.count + 1}")
    // An exemption from the rule against catching, since a read error here
    // is the cell's error and not the kernel's: a cell that does not read, or that reads a file of the tree
    // that is no lambdalattice text, is answered with an error reply, so that
    // Jupyter's stop_on_error drops the queued cells, and the kernel and its
    // notebook stay. Only the front end's read error is caught; anything else
    // ends the kernel.
    val read: Either[LambdalatticeMalformed, NotebookCell] =
      try Right(NotebookCell.read(id, code, state.notebook.location))
      catch case malformed: LambdalatticeMalformed => Left(malformed)
    read match
      case Left(malformed) =>
        val offset = malformed.problem match
          case _: com.yang_bo.gezi.frontend.LambdalatticeProblem.Syntax =>
            s", its offset counted in code points from the start of the text the kernel reads, the cell after ${NotebookCell.openingLength(state.notebook.location)} code points of the kernel's own"
          case _ => ""
        (
          state,
          CellInterpreter.error(
            "LambdalatticeMalformed",
            s"the cell does not read: ${malformed.problem}$offset"
          )
        )
      case Right(cell) =>
        val notebook = state.notebook.added(cell)
        val tracesBefore = traces.fold(Vector.empty[Path])(_.traces())
        // An interrupt (Jupyter's interrupt_request, which the kernel spec
        // asks for as a message) stops the entry at its next check of the
        // signal, as the end of the cell's seconds does.
        val stop = CellInterpreter.EitherStop(
          CellInterpreter.ShowingDeadline.after(CellInterpreter.cellSeconds),
          interrupted
        )
        // The files of the tree may change between two cells, so each cell is
        // run under an expansion source of its own: nothing the entry kept
        // from an earlier cell answers this one from an older content
        // (`Entry.run`).
        val source = ExpansionSource.fresh()
        notebook.written()
        val ran: Either[LambdalatticeMalformed, (Entry[C], Vector[String])] =
          try Right(outputs(notebook, cell, state.entry, source, stop))
          catch case malformed: LambdalatticeMalformed => Left(malformed)
        ran match
          case Left(malformed) =>
            (
              state,
              CellInterpreter.error(
                "LambdalatticeMalformed",
                s"a text read while the cell ran does not read: ${malformed.problem}"
              )
            )
          case Right((after, lines)) if interrupted.stopRequested =>
            (
              Session(
                notebook,
                after,
                if storeHistory then state.count + 1 else state.count
              ),
              CellInterpreter.error(
                "Interrupted",
                ("the cell was interrupted while its outputs were read, which is no semantic conclusion; the cell is in the notebook" +: lines)
                  .mkString("\n")
              )
            )
          case Right((after, lines)) =>
            val text = lines.mkString("\n")
            (
              Session(
                notebook,
                after,
                if storeHistory then state.count + 1 else state.count
              ),
              ExecuteResult.Success(
                traces.fold(DisplayData.text(text))(written =>
                  val pages = written.pagesWritten(
                    written.traces().filterNot(tracesBefore.contains)
                  )
                  DisplayData()
                    .add("text/plain", text)
                    .add("text/html", written.html(text, pages))
                )
              )
            )

  def currentLine(): Int = current.get.count

  /** Whether the text is a whole cell, which a console asks before it sends the
    * text (Jupyter's `is_complete_request`): complete when it reads after the
    * notebook's prefix; incomplete when it does not read because it ends too
    * soon (`NotebookCell.endsTooSoon`), which a console answers by reading
    * another line; invalid otherwise, which a console sends so that the cell is
    * answered with its error. The same exemption as `execute`'s for the front
    * end's read errors.
    */
  override def isComplete(code: String): Option[IsCompleteResult] =
    val location = current.get.notebook.location
    val problem =
      try
        val _ = NotebookCell.read("is_complete", code, location)
        None
      catch case malformed: LambdalatticeMalformed => Some(malformed.problem)
    Some(problem match
      case None => IsCompleteResult.Complete
      case Some(found) if NotebookCell.endsTooSoon(found, code, location) =>
        IsCompleteResult.Incomplete
      case Some(_) => IsCompleteResult.Invalid)

  /** The lines the cell outputs, one for each answer of each of its keys, and
    * the entry after the runs. A value member is the Output of a cell the entry
    * runs, and shows its display (`CellInterpreter.shown`); an io member is a
    * Moore machine state the entry runs with the JVM service
    * (`Entry.interacted`), and shows each answer as the entry reads it.
    */
  private def outputs[C <: NativeSpecializer & Singleton](
      notebook: Notebook[C],
      cell: NotebookCell,
      entry: Entry[C],
      source: ExpansionSource,
      stop: StopSignal
  )(using C, StorageAccess): (Entry[C], Vector[String]) =
    cell.outputs.foldLeft((entry, Vector.empty[String])) {
      case ((before, lines), key) =>
        val member = notebook.member(key)
        if key.isIo then
          before.interacted(member, JvmService, source, stop) match
            case None =>
              (
                before,
                lines :+ OutputLine
                  .Remark("this entry's executor runs no FFI program")
                  .written(key.shown)
              )
            case Some(run) =>
              val (afterAnswers, answered) =
                run.answers.foldLeft((run.entry, Vector.empty[OutputLine])) {
                  case ((current, shown), answer) =>
                    val (next, display) =
                      current.displayed(answer, source, stop)
                    (next, shown ++ CellInterpreter.displayed(display))
                }
              val shown = if run.finished then answered
              else answered :+ OutputLine.Remark(CellInterpreter.notFinished)
              (
                afterAnswers,
                lines ++ (if shown.isEmpty then
                            Vector(OutputLine.Remark("no answer"))
                          else shown).map(_.written(key.shown))
              )
        else
          val (after, shown) =
            CellInterpreter.shown(before, member, source, stop)
          (after, lines ++ shown.map(_.written(key.shown)))
    }

/** A line of a key's output: a term the key's member equals, written after `=`,
  * or a remark, written after `:`.
  */
enum OutputLine:
  case Equal(term: String)
  case Remark(text: String)

  /** The line under the key path as the cell writes it. */
  def written(key: String): String = this match
    case Equal(term)  => s"$key = $term"
    case Remark(text) => s"$key: $text"

object CellInterpreter:

  /** The kernel's interpreter of the notebook at the location, its tree of URIs
    * the one whose visible subtree is `visible`, its cells run by the entry.
    */
  def started(
      visible: Path,
      location: NotebookLocation,
      entry: Entry[?],
      traces: Option[CellTraces]
  ): CellInterpreter =
    CellInterpreter(session(visible, location, entry), traces)

  /** The capability to read a storage's view, which the kernel needs to write a
    * display: the adapter's own.
    */
  private[kernel] val storageAccess: StorageAccess = StorageAccess.granted()

  /** The first session of the entry's configuration, opened from `Entry[?]` by
    * capture conversion.
    */
  private def session[C <: NativeSpecializer & Singleton](
      visible: Path,
      location: NotebookLocation,
      entry: Entry[C]
  ): Session[C] =
    // The kernel's own file of the cells, gone when the JVM exits; deleteOnExit runs in reverse order, the file first.
    val directory = java.nio.file.Files.createTempDirectory("gezi-kernel-cells")
    directory.toFile.deleteOnExit()
    val cellsFile = directory.resolve(s"cells${DirectoryTree.fileExtension}")
    cellsFile.toFile.deleteOnExit()
    val notebook = Notebook[C](
      location,
      DirectoryTree.rootOf[C](visible)(using entry.specializer),
      Vector.empty,
      Some(cellsFile)
    )
    Session(notebook, entry, 0)

  /** The Jupyter cell id an `execute_request` carries in its metadata, as
    * JupyterLab and VS Code send it (`cellId`); none from a front end that
    * sends none, such as `jupyter console`, whose cells are then each a new
    * cell.
    */
  def cellId(message: Message[Execute.Request]): Option[String] =
    cellIdPattern
      .findFirstMatchIn(
        new String(
          message.metadata.value,
          java.nio.charset.StandardCharsets.UTF_8
        )
      )
      .map(_.group(1))

  /** The member `cellId` of the metadata's JSON object, a string with no
    * escape: a cell id is nbformat's, of the characters `[a-zA-Z0-9-_]`
    * (nbformat 4.5's schema).
    */
  private val cellIdPattern = "\"cellId\"\\s*:\\s*\"([a-zA-Z0-9_-]+)\"".r

  /** The lines of the value as the entry reads it, the Output of the cell
    * `λs. λk. k s V` (`Cells.cell`): its display, or that the entry did not
    * finish; and the entry after the run, the one before it when the run did
    * not finish. The entry stops at its next check of the stop (`Entry.run`).
    * The entry reads it under the expansion source given.
    */
  def shown[C <: NativeSpecializer & Singleton](
      entry: Entry[C],
      value: Configured[C],
      source: ExpansionSource,
      stop: StopSignal
  )(using
      C,
      StorageAccess
  ): (Entry[C], Vector[OutputLine]) =
    if stop.stopRequested then (entry, Vector(OutputLine.Remark(notFinished)))
    else
      entry.run(
        Cells.cell[Configured[C]](DeBruijnTerm.Constant[Configured[C]](value)),
        source,
        stop
      ) match
        case Interaction.Finished(_, _, after) if stop.stopRequested =>
          (after, Vector(OutputLine.Remark(notFinished)))
        case Interaction.Finished(display, _, after) =>
          (after, displayed(display))

  /** The lines of an entry's display, which shows the Scott ADT values only:
    * each member of the values as the Scott ADT reading writes it, a term the
    * Output is ⊑_O; that there is none (a value that is a function has none,
    * though it has a normal form); or, for a display that is the term left
    * unevaluated, that the entry did not evaluate it, which
    * `com.yang_bo.gezi.contest.entry.generic.GenericEntry` displays when a round of its
    * reading stops at its limit. No placeholder stands for a member that is no
    * Scott ADT value. Each member is written by the Scott ADT reading
    * (`ReadableText.scottADTText`, the member with its filters back,
    * `ScottADTChoices.withFilters`), in the order of the texts, so that a set
    * of values has one display.
    */
  def displayed[C <: NativeSpecializer & Singleton](
      display: OutputDisplay[C]
  )(using C, StorageAccess): Vector[OutputLine] = display match
    case OutputDisplay.Values(choices) =>
      val members = ScottADTChoices.members(choices)
      if members.isEmpty then Vector(OutputLine.Remark("no Scott ADT value"))
      else
        members
          .map(member =>
            com.yang_bo.gezi.frontend.ReadableText
              .scottADTText(ScottADTChoices.withFilters(member))
          )
          .sorted
          .map(OutputLine.Equal(_))
    case OutputDisplay.Remainder(_) =>
      Vector(
        OutputLine.Remark(
          "not evaluated: the entry stopped at a limit of its reading, which is no semantic conclusion"
        )
      )
    case OutputDisplay.Mixed(choices, _) =>
      displayed(OutputDisplay.Values(choices))

  /** The seconds the entry may spend on a cell, its reading and showing of
    * every key and the calls of its io members. A value's normal forms can be
    * many more than a person reads. A run that has not finished when they run
    * out shows so, which is no semantic conclusion.
    */
  val cellSeconds: Long = 10

  /** The line of a run the stop ended before it finished. */
  val notFinished: String =
    s"not finished: the entry was stopped by the end of the cell's $cellSeconds s or by an interrupt, which is no semantic conclusion"

  /** The stop requested once the clock passes the deadline, in the nanoseconds
    * of `System.nanoTime`.
    */
  final case class ShowingDeadline(deadlineNanos: Long) extends StopSignal:
    def stopRequested: Boolean = System.nanoTime - deadlineNanos >= 0

  object ShowingDeadline:
    def after(seconds: Long): ShowingDeadline = ShowingDeadline(
      System.nanoTime + seconds * 1000000000L
    )

  /** The stop requested once an interrupt arrives after the cell started: the
    * count of interrupts has passed the count the cell started at.
    */
  final case class Interrupted(interruptsNow: () => Long, startedAt: Long)
      extends StopSignal:
    def stopRequested: Boolean = interruptsNow() != startedAt

  /** The stop requested when either signal requests it. */
  final case class EitherStop(first: StopSignal, second: StopSignal)
      extends StopSignal:
    def stopRequested: Boolean = first.stopRequested || second.stopRequested

  /** An error whose message is also the one line of its traceback, which is
    * what a notebook shows of an error. almond 0.15.0 writes the iopub `error`
    * message without the key `traceback` when the stack trace is empty, as
    * `ExecuteResult.Error(message)` leaves it, and nbformat's `output_from_msg`
    * then throws `KeyError: 'traceback'`, so that the server-side execution of
    * JupyterLab (jupyter_server_nbmodel) shows nothing in the notebook
    * (measured 2026-11-10: the content was `ename` and `evalue` alone).
    */
  def error(name: String, message: String): ExecuteResult.Error =
    ExecuteResult.Error(name, message, List(message))
