package gezi.contest.judge

import java.io.File
import java.io.InputStream
import java.io.OutputStream
import java.lang.ProcessBuilder.Redirect
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.time.Duration
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Defaults
import gezi.contest.entry.EntryData
import gezi.contest.entry.OutputDisplay
import gezi.contest.entry.Report
import gezi.contest.runner.PipeLines
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Spine
import gezi.hotspot.LifecycleEvent
import gezi.knowledgereading.KnowledgeReading
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Value
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** How the judge read a point, from what the display of its cell's Output asserts
  * (`Display.asserted`), by the contest's rules for scoring an evaluation and
  * for reading an output: an output
  * confirms its normal form members F as members of the point's reference R
  * and nothing else; F ⊄ R is a false positive (false); otherwise the point
  * earns (|F| + c) / (|R| + 1) of its weight (`Share`), c = 1 exactly when
  * F = R and the output has no remainder. A judgment point `N ∥ T` is read
  * the same way with R = {N} for a member and R = ∅ for a trap. The share 1
  * is `success` (`proved` on a member's judgment, `refuted` on a trap's), a
  * share between 0 and 1 `incomplete`, the share 0 `no_answer` (`unknown`
  * on a judgment). Either kind: the JVM was stopped (the point's budget ran
  * out, a crash, an exit, an OOM kill), or it wrote a line that is not the
  * point's answer (`Supervisor.answerOutcome`), with the share 0.
  */
enum Outcome(val written: String):
  case Success extends Outcome("success")
  case False extends Outcome("false")
  case Incomplete extends Outcome("incomplete")
  case NoAnswer extends Outcome("no_answer")
  case Proved extends Outcome("proved")
  case Unknown extends Outcome("unknown")
  case Refuted extends Outcome("refuted")
  case Stopped extends Outcome("stopped")

/** The outcome of an answer to the point's question. */
object Outcome:

  /** The outcome and the share of the display of the point's cell's
    * Output.
    */
  def judged(question: Question, display: OutputDisplay): (Outcome, Share) =
    val asserted = Display.asserted(display)
    // The reference's normal forms as instructions, each converted once, to
    // compare with the display's members, which are instructions.
    val reference = question match
      case Question.Evaluation(normalForms)     => normalForms.map(Defunctionalization.thunkInstruction)
      case Question.Judgment(candidate, member) => if member then Set(candidate) else Set.empty[Instruction]
    if !asserted.normalForms.subsetOf(reference) then (False, Share.none)
    else
      val complete = asserted.normalForms == reference && !asserted.remainder
      val share = Share(asserted.normalForms.size + (if complete then 1 else 0), reference.size + 1)
      val outcome =
        if share.whole then
          question match
            case Question.Evaluation(_)       => Success
            case Question.Judgment(_, member) => if member then Proved else Refuted
        else if share.earned == 0 then
          question match
            case Question.Evaluation(_)     => NoAnswer
            case Question.Judgment(_, _) => Unknown
        else Incomplete
      (outcome, share)

/** The part of a point's weight an answer earns, `earned` of `of`, written
  * `earned/of` in the table's column `share` (the contest's rule for scoring an evaluation).
  */
final case class Share(earned: Int, of: Int):
  require(of > 0 && earned >= 0 && earned <= of, s"a share is a part of a whole: $earned/$of")

  /** The whole weight. */
  def whole: Boolean = earned == of

  def written: String = s"$earned/$of"

/** Shares. */
object Share:

  /** Nothing earned: a false answer, a stopped point, a setup reading. */
  val none: Share = Share(0, 1)

  /** The share the column's text writes, or none for another text. */
  def read(text: String): Option[Share] = text.split('/').toVector match
    case Vector(earned, of) =>
      for
        earnedCount <- earned.toIntOption
        ofCount <- of.toIntOption
        if ofCount > 0 && earnedCount >= 0 && earnedCount <= ofCount
      yield Share(earnedCount, ofCount)
    case _ => None

/** What the display of a cell's Output asserts, by the contest's rule for
  * reading an output: its top-level choice split
  * into members, the normal form members confirmed as members of the set;
  * whether a member that is no normal form, a remainder, stands beside them,
  * which keeps the output from claiming the whole set (the rule for scoring
  * an evaluation). The members are the display's instructions: two closed
  * βη normal forms are one term exactly when their front end instructions
  * are one interned instruction.
  */
final case class Asserted(normalForms: Set[Instruction], remainder: Boolean)

/** Reading a display, on its instruction and never on a tree: the display
  * comes from an untrusted process, and a line of the exchange format of n
  * bindings, each value applying the one before to itself, stands for a
  * tree of 2^n nodes.
  * Each walk visits each distinct instruction once.
  */
object Display:

  /** What the display asserts: no normal form and no remainder for the
    * display of no normal form; for a term, its members that are normal
    * forms, and whether another member stands beside them.
    */
  def asserted(display: OutputDisplay): Asserted = display match
    case OutputDisplay.NoNormalForm => Asserted(Set.empty, false)
    case OutputDisplay.Shown(shown) =>
      val (normalForms, remainder) = members(shown).partition(normalForm)
      Asserted(normalForms.toSet, remainder.nonEmpty)

  /** The members of the display's top-level choice, split along the `+`
    * spine with a left side that is itself a choice split as well, since
    * answers form a set, each distinct member once, in order; a display that
    * is not a choice is its own one member.
    */
  def members(display: Instruction): Vector[Instruction] =
    @tailrec
    def walked(pending: List[Instruction], visited: Set[Instruction], found: Vector[Instruction]): Vector[Instruction] =
      pending match
        case Nil                                           => found
        case current :: rest if visited.contains(current) => walked(rest, visited, found)
        case (current @ Instruction.Choice(left, right)) :: rest =>
          walked(left :: right :: rest, visited + current, found)
        case current :: rest => walked(rest, visited + current, found :+ current)
    walked(List(display), Set.empty, Vector.empty)

  /** Whether the instruction is a closed pure beta eta normal form: its
    * readback (`Defunctionalization.instructionTerm`) of variables,
    * abstractions and applications only, with no beta redex and no eta
    * redex, decided on the instruction. A closed application, choice,
    * parallel or opaque instruction is none: the head of a closed
    * application is closed, so it is an abstraction or no normal form. A
    * thunk is one when its code is, its slots read as the binders of its
    * holes and as its fillings, each filling a normal form, and its chain's
    * last binder, applied as the code's last argument, is read elsewhere in
    * the code. A closed term is all the pipe carries (`ExchangeText.term`).
    */
  def normalForm(instruction: Instruction): Boolean = closedNormalForms(instruction)(instruction)

  /** What a slot reads while a code is checked: the binder of a hole, by
    * its level, or a closed instruction, a filling.
    */
  private enum SlotRead:
    case Binder(level: Int)
    case Closed(instruction: Instruction)

  /** Whether each closed instruction under the root that the root's
    * readback writes in its own right (the root, and the fillings of
    * thunks) is a normal form, each decided after the fillings it reads.
    */
  private def closedNormalForms(root: Instruction): Map[Instruction, Boolean] =
    @tailrec
    def walked(pending: List[(Instruction, Boolean)], known: Map[Instruction, Boolean]): Map[Instruction, Boolean] =
      pending match
        case Nil                                          => known
        case (current, _) :: rest if known.contains(current) => walked(rest, known)
        case (current @ Instruction.Thunk(_, _, fillings), false) :: rest =>
          walked(fillings.toList.map((_, false)) ++ ((current, true) :: rest), known)
        case (current, _) :: rest => walked(rest, known.updated(current, closedNormalForm(current, known)))
    walked(List((root, false)), Map.empty)

  /** Whether the closed instruction is a normal form, its fillings' answers
    * known.
    */
  private def closedNormalForm(instruction: Instruction, known: Map[Instruction, Boolean]): Boolean = instruction match
    case Instruction.Thunk(code, holes, fillings) =>
      val reads = Defunctionalization.slotValues(
        holes,
        holes.indices.toVector.map(SlotRead.Binder(_)),
        fillings.map(SlotRead.Closed(_))
      )
      !etaRedex(code, holes) && codeNormalForm(code, reads, holes.size, known).result
    case _ => false

  /** Whether the code is a normal form under the reads of its slots, the
    * binders around it numbered below `level`.
    */
  private def codeNormalForm(code: Code, reads: Vector[SlotRead], level: Int, known: Map[Instruction, Boolean]): TailRec[Boolean] =
    code match
      case Code.Slot(slot) =>
        done(reads(slot) match
          case SlotRead.Binder(_)           => true
          case SlotRead.Closed(instruction) => known.getOrElse(instruction, false))
      case Code.Apply(_, _) =>
        val (head, arguments) = Spine.of(code)
        head match
          case Code.Slot(slot) =>
            reads(slot) match
              case SlotRead.Binder(_) => allNormalForms(arguments.toList, reads, level, known)
              // A closed head is an abstraction, a beta redex, or no normal form.
              case SlotRead.Closed(_) => done(false)
          // An abstraction, a beta redex; or a choice or a parallel.
          case _ => done(false)
      case Code.Thunk(inner, holes, fillings) =>
        val innerReads = Defunctionalization.slotValues(
          holes,
          holes.indices.toVector.map(position => SlotRead.Binder(level + position)),
          fillings.map {
            case Code.Slot(slot) => reads(slot)
            case other           => throw IllegalStateException(s"an inner thunk's filling is a slot of its body, not $other")
          }
        )
        if etaRedex(inner, holes) then done(false) else tailcall(codeNormalForm(inner, innerReads, level + holes.size, known))
      case _ => done(false)

  /** Whether every argument is a normal form. */
  private def allNormalForms(arguments: List[Code], reads: Vector[SlotRead], level: Int, known: Map[Instruction, Boolean]): TailRec[Boolean] =
    arguments match
      case Nil => done(true)
      case argument :: rest =>
        tailcall(codeNormalForm(argument, reads, level, known)).flatMap(normal =>
          if normal then tailcall(allNormalForms(rest, reads, level, known)) else done(false)
        )

  /** Whether the chain whose body is the code and whose holes are given is an
    * eta redex: its last binder read only as the body's last argument.
    */
  private def etaRedex(body: Code, holes: Vector[Hole]): Boolean = (holes.lastOption, body) match
    case (Some(Hole.Bound(slot)), Code.Apply(function, Code.Slot(last))) if last == slot => !reads(List(function), slot)
    case _                                                                                => false

  /** Whether the codes read the slot: an inner thunk reads its body's slots
    * through its fillings.
    */
  @tailrec
  private def reads(pending: List[Code], slot: Int): Boolean = pending match
    case Nil                                  => false
    case Code.Slot(read) :: rest              => if read == slot then true else reads(rest, slot)
    case Code.Apply(left, right) :: rest      => reads(left :: right :: rest, slot)
    case Code.Choice(left, right) :: rest     => reads(left :: right :: rest, slot)
    case Code.Parallel(left, right) :: rest   => reads(left :: right :: rest, slot)
    case Code.Thunk(_, _, fillings) :: rest   => reads(fillings.toList ++ rest, slot)
    case _ :: rest                            => reads(rest, slot)

/** A row of the judge's table: the point (`setup` for a setup reading),
  * the reader, the point's family and kind (`-` for a setup reading), the
  * outcome (`ready` for a setup reading), the point's own wall time, the
  * family's wall time so far when the point ended (the setup's own time for
  * a setup reading), the core set the JVM was bound to (`any` when unbound),
  * whether the point's budget ran out (`FamilyBudgets.pointBudget`), and
  * the phases the entry reported on the point's answer line (`Entry.phases`; none for a setup reading or a
  * stopped point, except one whose call returned within the cancel's grace,
  * which keeps the reports of the line it returned, its answer dropped), and
  * what the cancel at the point's budget did
  * (`Cancel`; `none` unless the point was being read when its budget ran
  * out). The phases are self-reported and never scored.
  */
final case class Row(
    point: String,
    reader: String,
    family: String,
    kind: String,
    outcome: String,
    share: Share,
    wallSeconds: Double,
    familyWallSeconds: Double,
    cores: String,
    budgetExhausted: Boolean,
    phases: Vector[Report],
    cancel: Cancel = Cancel.NotSent
):
  def written: String =
    Vector(
      point,
      reader,
      family,
      kind,
      outcome,
      share.written,
      f"$wallSeconds%.6f",
      f"$familyWallSeconds%.6f",
      cores,
      budgetExhausted.toString,
      PipeLines.phasesField(phases),
      cancel.written
    ).mkString("\t")

/** What the cancel at a point's budget did to the point being read,
  * the table's column
  * `cancel`: none was sent (`none`); the entry's call returned within the
  * grace, so the JVM was kept (`returned`); the cancel was sent and the JVM
  * killed (`killed`); the point's budget did not run out, and the JVM
  * ended by itself while the point was read, with the exit status the operating system gave
  * (`died:<status>`, 128 plus the signal's number for a signal, 137 for the
  * kernel's OOM killer's SIGKILL).
  */
enum Cancel(val written: String):
  case NotSent extends Cancel("none")
  case Returned extends Cancel("returned")
  case Killed extends Cancel("killed")
  case Died(exitStatus: Int) extends Cancel(s"died:$exitStatus")

/** The cancel written in the table. */
object Cancel:

  /** The cancel the column's text names, or none for another text. */
  def read(text: String): Option[Cancel] =
    Vector(NotSent, Returned, Killed).find(_.written == text).orElse(
      Option.when(text.startsWith("died:"))(text.stripPrefix("died:")).flatMap(_.toIntOption).map(Died(_))
    )

/** A reader the supervisor runs in a JVM of its own: its name in the table,
  * the classpath of its JVM and what the JVM runs.
  */
final case class Reader(name: String, classpath: String, launched: Launched)

/** What a reader's JVM runs: an entry, the main `contestEntryRunner` of
  * `gezi.contest.runner` given the entry's directory and whether the
  * execution of programs is denied (`Supervisor.command`), or a reference
  * reader, the judge's `judgeReferenceRunner` given the reader's name
  * (`tabling(weak_head)`). An entry's
  * JVM runs on the entry's classpath and the runner's, a reference reader's
  * on the judge's.
  */
enum Launched:
  case EntryLaunched(entryDirectory: Path)
  case ReferenceLaunched(readerName: String)

  /** The class whose `main` the JVM runs. */
  def mainClass: String = this match
    case EntryLaunched(_)     => "gezi.contest.runner.contestEntryRunner"
    case ReferenceLaunched(_) => "gezi.contest.judge.judgeReferenceRunner"

/** The family budget's rule: a family's budget is `multiple` times the family's anchor time,
  * its published reference time (`BudgetAnchor.Published`), at least
  * `floorSeconds` and at most `capSeconds`. A reader with no anchor time to
  * go by (the reference readers) gets the cap.
  */
final case class FamilyBudgets(multiple: Double, floorSeconds: Double, capSeconds: Double):
  def budget(anchorSeconds: Option[Double]): Double =
    anchorSeconds.fold(capSeconds)(seconds => (multiple * seconds).max(floorSeconds).min(capSeconds))

/** How a family's budget is shared among its points. */
object FamilyBudgets:

  /** The budget of the point at `index` (from 0) of a family of
    * `pointCount` points, given the family's wall seconds before the point
    * (the reference is the native solution, and a budget is in absolute
    * seconds): the family's
    * budget over `pointCount`, plus what the earlier points left unused,
    * that is the seconds until the family's wall time reaches
    * `(index + 1) * familyBudget / pointCount`, and zero when it already
    * has. The last point's budget lasts until the family's wall time reaches
    * the family's budget, so the family's points together take no more than it.
    */
  def pointBudget(familyBudget: Double, pointCount: Int, index: Int, familySecondsBefore: Double): Double =
    require(pointCount > 0, s"not a count of points: $pointCount")
    require(index >= 0 && index < pointCount, s"no point $index of $pointCount")
    val boundary = if index + 1 == pointCount then familyBudget else (index + 1) * familyBudget / pointCount
    (boundary - familySecondsBefore).max(0.0)

/** What the families' budgets go by: the published reference times of a
  * file (`FamilyReferences`), the only anchor.
  * No
  * entry is read first in a pass to set the budgets.
  */
enum BudgetAnchor:
  case Published(referenceSeconds: Map[String, Double])

/** The published reference times (`--family-references`): a TSV, one line
  * a family, `<family>\t<seconds>`, lines starting with `#` ignored. The
  * times are published with the points; a pass reads no reference
  * entry. How the times are measured is the contest rules'.
  */
object FamilyReferences:

  /** The reference seconds of every family of `families`. Throws
    * `IllegalArgumentException` for a line of another shape, a family given
    * twice, or a family of `families` the file does not give.
    */
  def read(path: Path, families: Vector[String]): Map[String, Double] =
    val entries = Files.readString(path, StandardCharsets.UTF_8).split('\n').toVector
      .filter(line => line.nonEmpty && !line.startsWith("#"))
      .map(line =>
        line.split('\t').toVector match
          case Vector(family, seconds) if seconds.toDoubleOption.exists(_ > 0) => family -> seconds.toDouble
          case other => throw IllegalArgumentException(s"the family references $path have a line of another shape: $other")
      )
    val repeated = entries.groupBy(_._1).collect { case (family, lines) if lines.size > 1 => family }.toVector.sorted
    if repeated.nonEmpty then throw IllegalArgumentException(s"the family references $path give ${repeated.mkString(", ")} more than once")
    val missing = families.filterNot(entries.map(_._1).toSet)
    if missing.nonEmpty then throw IllegalArgumentException(s"the family references $path give no time for ${missing.mkString(", ")}")
    entries.toMap

/** The supervisor's limits and placement: the family budgets, the
  * wall-clock limit of a setup and the grace an entry's call has to return
  * after the cancel at a point's budget, in seconds; the systemd user slice the
  * reader's JVM is started in (`systemd-run --user --scope --slice=<slice>`),
  * the cores it is bound to (`taskset -c`) and its niceness (`nice -n`), each
  * when given; the directory the JVMs' standard errors are written to; the
  * heap of an entry's JVM (`-Xmx`), a size the
  * rules set for the round; the number of carrier threads of an entry's
  * virtual-thread scheduler (`-Djdk.virtualThreadScheduler.parallelism`),
  * when the rules set it, so that every entry forks onto the same cores; and
  * the sandbox an entry's JVM runs in
  * (`Sandbox`); and where an entry writes its articles
  * (`ArticleDestination`: `Discarded` in the scored pass, the directory of
  * the article re-read); and where an entry's JVM writes the flight
  * recording of each cell, when the pass records (`--flight-recordings`,
  * off in every scored pass): the directory given, in a directory of the
  * reader's name. A reference reader's JVM keeps the small limit of 256 MB and
  * runs outside the sandbox. No memory limit is set on the scope (no
  * `MemoryHigh`: with swap off, a process over it stalls instead of being
  * killed); the slice's share bounds it, and an OOM kill (exit 137) or an
  * exhausted heap reads as stopped.
  */
final case class Limits(
    budgets: FamilyBudgets,
    setupSeconds: Double,
    cancelGraceSeconds: Double,
    slice: Option[String],
    cores: Option[String],
    niceness: Option[Int],
    logDirectory: Path,
    entryHeap: String,
    entryParallelism: Option[Int],
    sandbox: Sandbox,
    articles: ArticleDestination,
    flightRecordings: Option[Path]
):
  require(entryHeap.matches("[1-9][0-9]*[kKmMgG]?"), s"not a JVM heap size: $entryHeap")
  require(entryParallelism.forall(_ >= 1), s"not a number of carrier threads: $entryParallelism")
  require(cancelGraceSeconds >= 0, s"not a grace in seconds: $cancelGraceSeconds")

  /** The core set written beside every reading. */
  def coreSet: String = cores.getOrElse("any")

/** A running JVM of a reader: the process, its pipe in both directions, and
  * the bytes read past the last line (as ISO-8859-1 characters, one a
  * byte).
  */
final case class Session(process: Process, answers: InputStream, points: OutputStream, pending: String)

/** A reader's pass: its rows, and the answer of each evaluation point it
  * answered, by the point's name (the article re-read compares them).
  */
final case class ReaderRead(rows: Vector[Row], answers: Map[String, Option[Set[Instruction]]])

/** A pass: the rows of every reader, and, by the reader's name, the answers
  * of the evaluation points it answered (none for a reused reader) and its
  * budget for each family.
  */
final case class PassRead(
    rows: Vector[Row],
    answers: Map[String, Map[String, Option[Set[Instruction]]]],
    budgets: Map[String, Map[String, Double]]
)

/** What waiting for a line gave: the line, the JVM's end, or the deadline
  * passed, with the session holding the bytes read so far of a line not yet
  * ended, which the cancel's grace goes on reading (`Supervisor.pointRead`).
  */
enum Awaited:
  case Line(line: String, session: Session)
  case Ended
  case TimedOut(session: Session)

/** A setup that did not reach its ready line: the reader, why, and the
  * standard error of its JVM.
  */
final case class SetupFailed(reader: String, reason: String, standardError: String)
    extends RuntimeException(s"the setup of $reader $reason; its standard error:\n$standardError")

/** The supervisor of a pass:
  * for each reader, one JVM (`-Xmx256m`, the serial collector, in the slice,
  * on the cores and at the niceness given, and, for an entry, in the
  * sandbox, `Sandbox`) reads the families in the seed's
  * order, a family's points one after another, through the runner
  * (`gezi.contest.runner.EntryRunner`, started as `Launched` says); the
  * supervisor writes each point to its pipe, reads the answer line, and
  * measures from outside, with `System.nanoTime`, the
  * setup reading (from starting the JVM to its ready line) and each point's
  * wall time (from writing the point to reading its answer). It writes the
  * lifecycle lines of the entry's cache service (`gezi.hotspot.LifecycleEvent`), each
  * answered by the runner's `lifecycle_done`: `round_started` once in a
  * reader's pass, to its first JVM after its setup; `family_started` with
  * the first point a JVM reads of a family, in the point's write and inside
  * its wall time; `family_finished` after the family's last point to the
  * JVM still running, and `round_finished` at the end of the pass, both
  * outside any point's wall time, the next point's clock started only after
  * their `lifecycle_done` (`eventTaken`). A JVM started again within a pass
  * hears no `round_started`. The runner announces the points' events
  * itself.
  *
  * The wall-clock budget is set per family (`FamilyBudgets`): an entry's
  * budget for a family is a multiple of the family's anchor time
  * (`BudgetAnchor`), its published reference time. It is shared among the
  * family's points (`FamilyBudgets.pointBudget`):
  * of a family's n
  * points, the one at index i (from 0) has the family's budget over n plus
  * what the earlier points left unused, so that it may run until the
  * family's wall time reaches (i + 1) times the budget over n, and the
  * family's points together take no more than its budget. When a point's
  * budget runs out, the supervisor records the point stopped, its
  * `budget_exhausted` true, and writes the line `cancel`
  * (`PipeLines.cancelLine`) to the JVM: when the entry's call returns within
  * the grace (`Limits.cancelGraceSeconds`, not charged to the family), the
  * JVM is kept and reads the family's next point; otherwise the supervisor
  * kills it and starts a new JVM (a new setup reading) for the next point.
  * The
  * family's next points are read each with its own budget; a point left a
  * budget of zero is recorded stopped, its budget run out, and is not
  * written to the JVM. A crash, an exit, an OOM
  * kill, or a line on the pipe that is not the point's answer (the JVM's own
  * message on an `OutOfMemoryError` is one; `answerOutcome`) stops the point
  * being read: the supervisor kills the JVM if it is still alive, writes the
  * line to the file `<reader>-<launch>.unanswered` of the log directory, and
  * a new JVM continues from the family's next point, so every point is read
  * once and a JVM killed on its first point leaves that point stopped.
  * Correctness is per point (`Outcome`); the
  * supervisor computes no score. The judge is not a benchmark: it reads each
  * point once, by its wall time, with no warm-up.
  *
  * The supervisor reads the pipe synchronously, with no thread: it polls the
  * bytes available every `pollInterval`, so a wall time is late by at most
  * that interval and the polling's own cost. The JVM's standard error goes
  * to a file of the log directory, so that it never fills a pipe.
  */
object Supervisor:

  /** The interval between two polls of the pipe: 100 microseconds. */
  val pollInterval: Duration = Duration.ofNanos(100000)

  /** The rows of each reader on the families, the readers in order: for
    * each reader its setup rows and one row for each point, in the order
    * read. An entry's budget for a family goes by the anchor's time for it,
    * the published reference; a family the anchor gives no time, and every
    * family of a reference reader, gets the cap. A reader whose rows
    * `reused` holds (an earlier table's, `TableFile.reused`) is not read
    * again: its rows are those. Throws `SetupFailed` when a setup does not
    * reach its ready line within the setup limit.
    */
  def pass(
      anchor: BudgetAnchor,
      readers: Vector[Reader],
      families: Vector[(String, Vector[Point])],
      limits: Limits,
      reused: Vector[Row] = Vector.empty
  ): Vector[Row] = passRead(anchor, readers, families, limits, reused).rows

  /** The pass of `pass`, with what the article re-read needs of it
    * (`PassRead`): each reader's evaluation answers and family budgets. A
    * reused reader has its rows and no answers.
    */
  def passRead(
      anchor: BudgetAnchor,
      readers: Vector[Reader],
      families: Vector[(String, Vector[Point])],
      limits: Limits,
      reused: Vector[Row]
  ): PassRead =
    val withLines = families.map((family, points) => (family, points.map(point => (point, PipeLines.cellLine(point.name, cell(point)) + "\n"))))
    def readOf(reader: Reader, budget: String => Double): ReaderRead =
      reused.filter(_.reader == reader.name) match
        case Vector() => readerPass(reader, withLines, budget, limits)
        case found    => ReaderRead(found, Map.empty)
    def budgetsOf(budget: String => Double): Map[String, Double] = families.map((family, _) => family -> budget(family)).toMap
    val capped: String => Double = _ => limits.budgets.budget(None)
    val anchorSeconds = anchor match
      case BudgetAnchor.Published(referenceSeconds) => referenceSeconds
    val all = readers.map(reader =>
      val budget: String => Double = reader.launched match
        case Launched.ReferenceLaunched(_) => capped
        case Launched.EntryLaunched(_)     => family => limits.budgets.budget(anchorSeconds.get(family))
      (reader.name, readOf(reader, budget), budgetsOf(budget))
    )
    PassRead(
      all.flatMap((_, read, _) => read.rows),
      all.map((name, read, _) => name -> read.answers).toMap,
      all.map((name, _, budgets) => name -> budgets).toMap
    )

  /** What a reader's pass carries from one point to the next: the running
    * JVM, if any, the rows so far, the JVMs launched, whether the line
    * `round_started` was written in the pass, and the answer of each
    * evaluation point answered so far, by the point's name.
    */
  private final case class Carried(
      session: Option[Session],
      rows: Vector[Row],
      launches: Int,
      roundStarted: Boolean,
      answers: Map[String, Option[Set[Instruction]]]
  )

  /** What a family's reading carries from one point to the next: the pass's
    * state, the family's wall time so far, and whether the running JVM was
    * told the family started (the lifecycle line `family_started`,
    * `PipeLines.lifecycleLine`).
    */
  private final case class InFamily(carried: Carried, familySeconds: Double, announced: Boolean)

  private def readerPass(
      reader: Reader,
      families: Vector[(String, Vector[(Point, String)])],
      budget: String => Double,
      limits: Limits
  ): ReaderRead =
    val last = families.foldLeft(Carried(None, Vector.empty, 0, false, Map.empty)) { case (carried, (family, points)) =>
      val familyBudget = budget(family)
      val read = points.zipWithIndex.foldLeft(InFamily(carried.copy(rows = Vector.empty), 0.0, false)) { case (state, ((point, line), index)) =>
        val pointBudget = FamilyBudgets.pointBudget(familyBudget, points.size, index, state.familySeconds)
        if pointBudget > 0.0 then pointRead(reader, family, point, line, pointBudget, limits, state)
        else
          val row = Row(point.name, reader.name, family, kind(point), Outcome.Stopped.written, Share.none, 0.0, state.familySeconds, limits.coreSet, true, Vector.empty)
          state.copy(carried = state.carried.copy(rows = state.carried.rows :+ row))
      }
      // The JVM that was told the family started is told it finished,
      // outside any point's wall time; a JVM that does not take the event
      // is stopped, and the next family starts a new one.
      val afterFamily =
        if read.announced then read.carried.session.flatMap(eventTaken(_, LifecycleEvent.FamilyFinished, reader, read.carried.launches, limits))
        else read.carried.session
      read.carried.copy(session = afterFamily, rows = carried.rows ++ read.carried.rows)
    }
    last.session.flatMap(eventTaken(_, LifecycleEvent.RoundFinished, reader, last.launches, limits)).foreach(stopped)
    ReaderRead(last.rows, last.answers)

  /** The session after its JVM was told the event and answered
    * `lifecycle_done`, outside any point's wall time, within the setup
    * limit; or, when the JVM ends, writes another line (logged as
    * unanswered) or passes the limit, nothing, the JVM stopped.
    */
  private def eventTaken(session: Session, event: LifecycleEvent, reader: Reader, launches: Int, limits: Limits): Option[Session] =
    val start = System.nanoTime
    val delivered = session.process.isAlive && pointWritten(session.points, PipeLines.lifecycleLine(event) + "\n")
    val awaited = if delivered then awaitedLine(session, start + nanoseconds(limits.setupSeconds)) else Awaited.Ended
    awaited match
      case Awaited.Line(PipeLines.lifecycleDone, after) => Some(after)
      case Awaited.Line(other, after) =>
        stopped(after)
        Files.writeString(logFile(limits, reader, launches, "unanswered"), other + "\n", StandardCharsets.UTF_8)
        None
      case Awaited.Ended | Awaited.TimedOut(_) =>
        stopped(session)
        None

  /** The cell of the point on the pipe: `λs.λk. k s p` for an evaluation of the program p,
    * `λs.λk. k s (N ∥ p)` for a judgment of the candidate N; never its
    * reference or its expected answer, and nothing that tells the two kinds
    * apart but the term itself. The program and the candidate are closed,
    * so they are the same terms under the cell's two binders, and the cell
    * is converted with them as constants, never read back into a tree.
    */
  def cell(point: Point): Instruction =
    Defunctionalization.thunkInstruction(Cells.cell(DeBruijnTerm.Constant(point.question match
      case Question.Evaluation(_)          => point.program
      case Question.Judgment(candidate, _) => Instruction.Parallel(candidate, point.program))))

  private def kind(point: Point): String = point.question match
    case Question.Evaluation(_)  => "evaluation"
    case Question.Judgment(_, _) => "judgment"

  /** The point read in the family's state: the JVM started if none runs,
    * the point written, its answer awaited until the point's budget
    * (`FamilyBudgets.pointBudget`) runs out.
    */
  private def pointRead(
      reader: Reader,
      family: String,
      point: Point,
      line: String,
      pointBudget: Double,
      limits: Limits,
      state: InFamily
  ): InFamily =
    val carried = state.carried
    val (running, setupRows, launches) = carried.session match
      case Some(running) => (Some(running), Vector.empty, carried.launches)
      case None =>
        val (started, setup) = startedSession(reader, limits, carried.launches + 1)
        // The pass's first JVM is told the round started, after its setup
        // and outside the point's wall time; a JVM started again is not.
        val told =
          if carried.roundStarted then Some(started)
          else eventTaken(started, LifecycleEvent.RoundStarted, reader, carried.launches + 1, limits)
        (told, Vector(setup), carried.launches + 1)
    // A JVM not yet told the family started, the family's first or one
    // started after a stop, is told before the point, in the same write,
    // and its `lifecycle_done` is read inside the point's wall time.
    val announcing = carried.session.isEmpty || !state.announced
    val announcement = if announcing then PipeLines.lifecycleLine(LifecycleEvent.FamilyStarted) + "\n" else ""
    val start = System.nanoTime
    val awaited = running match
      case Some(session) if session.process.isAlive && pointWritten(session.points, announcement + line) =>
        val deadline = start + nanoseconds(pointBudget)
        awaitedLine(session, deadline) match
          case Awaited.Line(PipeLines.lifecycleDone, after) if announcing => awaitedLine(after, deadline)
          case other                                                      => other
      case _ => Awaited.Ended
    val wallSeconds = (System.nanoTime - start) / 1e9
    val familySeconds = state.familySeconds + wallSeconds
    def row(outcome: Outcome, share: Share, phases: Vector[Report]) =
      Row(point.name, reader.name, family, kind(point), outcome.written, share, wallSeconds, familySeconds, limits.coreSet, false, phases)
    def exhausted(phases: Vector[Report], cancel: Cancel) =
      row(Outcome.Stopped, Share.none, phases).copy(budgetExhausted = true, cancel = cancel)
    // Every outcome carries `roundStarted = true`: once a JVM was started in
    // the pass, the round was announced to it, or it did not take the
    // event and was stopped, and a JVM started again is not told.
    awaited match
      case Awaited.Line(answerLine, after) =>
        answerOutcome(point, answerLine) match
          case Some((outcome, share, phases)) =>
            val answers = evaluationAnswer(point, answerLine).fold(carried.answers)(answer => carried.answers.updated(point.name, answer))
            InFamily(Carried(Some(after), carried.rows ++ setupRows :+ row(outcome, share, phases), launches, roundStarted = true, answers), familySeconds, true)
          case None =>
            stopped(after)
            Files.writeString(logFile(limits, reader, launches, "unanswered"), answerLine + "\n", StandardCharsets.UTF_8)
            InFamily(Carried(None, carried.rows ++ setupRows :+ row(Outcome.Stopped, Share.none, Vector.empty), launches, roundStarted = true, carried.answers), familySeconds, false)
      case Awaited.Ended =>
        // The JVM's pipe ended before the budget: a JVM that exits within
        // the wait ended by itself (an OOM kill, a crash, `System.exit`),
        // and its exit status is written in the row and on the supervisor's
        // standard error; one still alive is stopped, as before.
        val died = running.flatMap(session =>
          Option.when(session.process.waitFor(java.time.Duration.ofSeconds(deathWaitSeconds)))(session.process.exitValue)
        )
        running.foreach(stopped)
        died.foreach(status =>
          System.err.println(s"${reader.name}: the JVM of launch $launches ended by itself on ${point.name} of $family, exit status $status")
        )
        val ended = row(Outcome.Stopped, Share.none, Vector.empty).copy(cancel = died.fold(Cancel.NotSent)(Cancel.Died(_)))
        InFamily(Carried(None, carried.rows ++ setupRows :+ ended, launches, roundStarted = true, carried.answers), familySeconds, false)
      case Awaited.TimedOut(waiting) =>
        // The point's budget ran out with the point being read: the entry's
        // call is cancelled and has the grace to return, outside the point's and the family's wall time. An
        // answer line within the grace keeps the JVM, still told the family
        // started, so it reads the family's next point, or hears
        // `family_finished` after the family's last; the answer itself is
        // dropped, the point stopped. Anything else in the grace stops the
        // JVM, and the family's next point starts a new one. A
        // returned line's reports (its phases and counts, never its display)
        // are kept on the stopped row, so that what a cancelled point spent,
        // its rounds' instances among them, is read (the outcome stays
        // stopped, and the wall time and the budget are charged as before).
        val cancelled = waiting.process.isAlive && pointWritten(waiting.points, PipeLines.cancelLine + "\n")
        val graceDeadline = System.nanoTime + nanoseconds(limits.cancelGraceSeconds)
        val graced =
          if !cancelled then Awaited.Ended
          else
            awaitedLine(waiting, graceDeadline) match
              case Awaited.Line(PipeLines.lifecycleDone, after) if announcing => awaitedLine(after, graceDeadline)
              case other                                                      => other
        val cancel = if cancelled then Cancel.Killed else Cancel.NotSent
        def killed = exhausted(Vector.empty, cancel)
        graced match
          case Awaited.Line(line, after) =>
            answerOutcome(point, line) match
              case Some((_, _, reports)) =>
                val returned = exhausted(reports, Cancel.Returned)
                InFamily(Carried(Some(after), carried.rows ++ setupRows :+ returned, launches, roundStarted = true, carried.answers), familySeconds, true)
              case None =>
                stopped(after)
                Files.writeString(logFile(limits, reader, launches, "unanswered"), line + "\n", StandardCharsets.UTF_8)
                InFamily(Carried(None, carried.rows ++ setupRows :+ killed, launches, roundStarted = true, carried.answers), familySeconds, false)
          case Awaited.Ended | Awaited.TimedOut(_) =>
            stopped(waiting)
            InFamily(Carried(None, carried.rows ++ setupRows :+ killed, launches, roundStarted = true, carried.answers), familySeconds, false)

  /** Whether the point's line reached the reader's JVM: false when the JVM's
    * end of the pipe is closed, so that the write throws an IOException
    * ("Broken pipe"), as when the JVM ends after the liveness check and
    * before or during the write. The reader is then no longer answering, and
    * the point reads stopped, as for a JVM that ended before the write.
    *
    * EXCEPTION to offensive programming, which recovers from no error: the
    * judge's one exception handler, catching the IOException of this write
    * alone, so that a write to an entry's JVM that has died records the
    * point as stopped and the pass goes on instead of ending.
    */
  private[judge] def pointWritten(points: OutputStream, line: String): Boolean =
    try
      points.write(line.getBytes(StandardCharsets.UTF_8))
      points.flush()
      true
    catch case _: java.io.IOException => false

  /** The outcome of the line read for the point, with the phases the line
    * reports: an answer line (`PipeLines.answerRead`) of the point's name is
    * judged by what its display asserts (`Outcome.judged`);
    * any other line, such as the
    * message `-XX:+ExitOnOutOfMemoryError` makes the JVM write on its
    * standard output, has none: the reader is no longer answering. The line
    * comes from the reader's JVM, an untrusted process, so reading it into an
    * outcome is reading an expected input, not recovering from an error.
    */
  def answerOutcome(point: Point, line: String): Option[(Outcome, Share, Vector[Report])] = PipeLines.answerRead(line) match
    case PipeLines.AnswerRead.Answer(name, phases, display) if name == point.name =>
      val (outcome, share) = Outcome.judged(point.question, display)
      Some((outcome, share, phases))
    case _ => None

  /** The article re-read of a point the scored pass read:
    * a new JVM of
    * the reader, loaded with the article directory as its destination
    * (`ArticleDestination.Written`), reads the point's cell alone, cold,
    * within the family's budget times the allowance, the whole of it the
    * point's budget, since the cell is read as a family of one point; the
    * sandbox binds the
    * article directory writable, and the JVMs' standard errors go to the
    * log directory given, so that the scored pass's logs are kept. How the
    * re-read ended (`Reread`): the point stopped with the budget run out,
    * stopped otherwise, or answered.
    */
  def reread(
      reader: Reader,
      family: String,
      points: Vector[Point],
      target: Point,
      articleDirectory: Path,
      familyBudget: Double,
      limits: Limits
  ): Reread =
    // FIXME: the allowance (`--article-allowance`, default 2) was set when https://github.com/Atry/private-overlay/issues/2049
    // the re-read read the whole family, warm; it now reads one cell cold and is to be measured
    // again.
    val lines = Vector((target, PipeLines.cellLine(target.name, cell(target)) + "\n"))
    val read = readerPass(
      reader,
      Vector((family, lines)),
      _ => familyBudget,
      limits.copy(sandbox = limits.sandbox.writable(articleDirectory), articles = ArticleDestination.Written(articleDirectory))
    )
    val targetRow = read.rows.find(row => row.point == target.name && row.family == family).getOrElse(
      throw IllegalStateException(s"the re-read of $family has no row of ${target.name}")
    )
    if targetRow.outcome == Outcome.Stopped.written then
      if targetRow.budgetExhausted then Reread.Exhausted else Reread.Stopped
    else
      Reread.Answered(read.answers.getOrElse(target.name, throw IllegalStateException(s"the re-read answered ${target.name} with no evaluation's answer")))

  /** The normal forms an evaluation point's answer line asserts, none
    * asserted being `None` (the article re-read compares them); nothing for
    * a judgment point or another line.
    */
  private def evaluationAnswer(point: Point, line: String): Option[Option[Set[Instruction]]] =
    (point.question, PipeLines.answerRead(line)) match
      case (Question.Evaluation(_), PipeLines.AnswerRead.Answer(_, _, display)) =>
        val asserted = Display.asserted(display)
        Some(Option.unless(asserted.normalForms.isEmpty && asserted.remainder)(asserted.normalForms))
      case _ => None

  /** The heap of the reader's JVM: the round's entry heap for an entry, the
    * small limit of 256 MB for a reference reader.
    */
  def heap(reader: Reader, limits: Limits): String = reader.launched match
    case Launched.EntryLaunched(_)     => limits.entryHeap
    case Launched.ReferenceLaunched(_) => "256m"

  /** The option that sets the carrier threads of an entry's virtual-thread
    * scheduler, when the round sets them; a reference reader starts no
    * thread and gets none.
    */
  def parallelismOptions(limits: Limits): Vector[String] =
    limits.entryParallelism.toVector.map(carriers => s"-Djdk.virtualThreadScheduler.parallelism=$carriers")

  /** The command that starts a JVM of the reader: in the slice, on the
    * cores, at the niceness, then, for an entry, in the sandbox
    * (`Sandbox.bubblewrapWords`), where the JVM may call native code
    * (`--enable-native-access=ALL-UNNAMED`) so that the runner installs the
    * execution filter without a warning, and the runner is told whether the
    * execution of programs is denied.
    *
    * FIXME: `ALL-UNNAMED` opens native access to the entry's classes as well https://github.com/Atry/private-overlay/issues/1998
    * as the runner's, since all of them are in the unnamed module (before
    * this flag the JDK's default, `--illegal-native-access=warn`, allowed it
    * with a warning). Native code stays inside the namespaces and the
    * execution filter, but it can `fork` a process that executes nothing,
    * which escapes the convention that entries start no thread. Candidate
    * fix, with a JPMS boundary between the runner and the entry (not yet done):
    * the runner a named module, `--enable-native-access=<that module>` and
    * `--illegal-native-access=deny`.
    */
  /** The runner's argument for the article destination
    * (`contestEntryRunner`): `discarded`, the directory, or `traces:` and the
    * directory.
    */
  private def articlesArgument(articles: ArticleDestination): String = articles match
    case ArticleDestination.Discarded                    => "discarded"
    case ArticleDestination.Written(directory)           => directory.toString
    case ArticleDestination.WrittenWithTraces(directory) => s"traces:$directory"

  /** The directory of the reader's flight recordings, when the pass records
    * and the reader is an entry: the reader's name, as in `logFile`, under
    * the directory of `--flight-recordings`.
    */
  def recordingDirectory(reader: Reader, limits: Limits): Option[Path] = reader.launched match
    case Launched.EntryLaunched(_)     => limits.flightRecordings.map(_.resolve(fileSafe(reader.name)))
    case Launched.ReferenceLaunched(_) => None

  /** The Java options of the reader's flight recordings: the recorder's
    * repository in the recordings' directory, which the sandbox binds
    * writable, instead of the sandbox's small `/tmp`.
    */
  private def recordingOptions(recordings: Option[Path]): Vector[String] =
    recordings.toVector.map(directory => s"-XX:FlightRecorderOptions=repository=${directory.resolve("repository")}")

  /** The runner's argument for the flight recordings: `none`, or the
    * directory.
    */
  private def recordingsArgument(recordings: Option[Path]): String = recordings.fold("none")(_.toString)

  def command(reader: Reader, limits: Limits): Vector[String] =
    val java = Paths.get(System.getProperty("java.home"), "bin", "java").toString
    val recordings = recordingDirectory(reader, limits)
    val (sandboxWords, javaOptions, arguments) = (reader.launched, limits.sandbox) match
      case (Launched.EntryLaunched(entryDirectory), Sandbox.Bubblewrap(readablePaths, writablePaths)) =>
        (
          Sandbox.bubblewrapWords(readablePaths, reader.classpath, entryDirectory, writablePaths ++ recordings),
          ("--enable-native-access=ALL-UNNAMED" +: parallelismOptions(limits)) ++ recordingOptions(recordings),
          Vector(entryDirectory.toString, "denied", articlesArgument(limits.articles), recordingsArgument(recordings))
        )
      case (Launched.EntryLaunched(entryDirectory), Sandbox.Unconfined) =>
        (
          Vector.empty,
          parallelismOptions(limits) ++ recordingOptions(recordings),
          Vector(entryDirectory.toString, "allowed", articlesArgument(limits.articles), recordingsArgument(recordings))
        )
      case (Launched.ReferenceLaunched(readerName), _) => (Vector.empty, Vector.empty, Vector(readerName))
    limits.slice.toVector.flatMap(slice => Vector("systemd-run", "--user", "--scope", "--quiet", s"--slice=$slice")) ++
      limits.cores.toVector.flatMap(cores => Vector("taskset", "-c", cores)) ++
      limits.niceness.toVector.flatMap(niceness => Vector("nice", "-n", niceness.toString)) ++
      sandboxWords ++
      Vector(java, s"-Xmx${heap(reader, limits)}", "-XX:+UseSerialGC", "-XX:+ExitOnOutOfMemoryError") ++
      javaOptions ++
      Vector("-cp", reader.classpath, reader.launched.mainClass) ++
      arguments

  /** A new JVM of the reader started and its setup read: the session and
    * the setup row. Throws `SetupFailed` when the JVM ends, writes another
    * line or passes the setup limit before its ready line.
    */
  private def startedSession(reader: Reader, limits: Limits, launch: Int): (Session, Row) =
    val errors = logFile(limits, reader, launch, "stderr")
    // FIXME: the log file is outside the sandbox and has no cap: an entry https://github.com/Atry/private-overlay/issues/1999
    // that floods its standard error fills the disk until its family's wall
    // time ends. Candidate fix: `prlimit --fsize=<bytes>` in the command
    // chain, so that the entry's writes past the cap end it with SIGXFSZ;
    // the cap needs a measured size of real logs first.
    // The sandbox binds only a directory that exists.
    recordingDirectory(reader, limits).foreach(directory => Files.createDirectories(directory.resolve("repository")))
    val start = System.nanoTime
    val process = ProcessBuilder(command(reader, limits).asJava).redirectError(Redirect.to(errors.toFile)).start()
    val session = Session(process, process.getInputStream, process.getOutputStream, "")
    awaitedLine(session, start + nanoseconds(limits.setupSeconds)) match
      case Awaited.Line("ready", after) =>
        val seconds = (System.nanoTime - start) / 1e9
        (after, Row("setup", reader.name, "-", "-", "ready", Share.none, seconds, seconds, limits.coreSet, false, Vector.empty))
      case Awaited.Line(other, after) =>
        stopped(after)
        throw SetupFailed(reader.name, s"wrote ${other.take(80)} before its ready line", Files.readString(errors))
      case Awaited.Ended =>
        throw SetupFailed(reader.name, s"ended with status ${process.waitFor()}", Files.readString(errors))
      case Awaited.TimedOut(_) =>
        stopped(session)
        throw SetupFailed(reader.name, s"passed the setup limit of ${limits.setupSeconds} s", Files.readString(errors))

  /** The file of the log directory for the reader's JVM of the launch: its
    * standard error (`stderr`), or the line it wrote that was not an answer
    * (`unanswered`).
    */
  private def logFile(limits: Limits, reader: Reader, launch: Int, extension: String): Path =
    limits.logDirectory.resolve(s"${fileSafe(reader.name)}-$launch.$extension")

  /** The reader's name with every character other than a letter, a digit
    * and `_` written `-`, the part of a file name it gives.
    */
  private def fileSafe(name: String): String =
    name.map(character => if character.isLetterOrDigit || character == '_' then character else '-')

  /** The next line of the session, decoded as UTF-8, or the JVM's end, or
    * the deadline (of `System.nanoTime`) passed. A line already in
    * `pending`, read in the chunk of the line before it, is the next line,
    * before the pipe is polled.
    */
  @tailrec
  private[judge] def awaitedLine(session: Session, deadline: Long): Awaited =
    session.pending.indexOf('\n') match
      case -1 =>
        val available = session.answers.available()
        if available > 0 then
          val chunk = String(session.answers.readNBytes(available), StandardCharsets.ISO_8859_1)
          // FIXME: a line without its newline grows `pending` in the https://github.com/Atry/private-overlay/issues/1999
          // supervisor's heap without bound until the deadline: an entry that
          // writes faster than its wall time ends can exhaust the supervisor's
          // -Xmx and end the pass. Candidate fix: a line longer than a cap reads
          // as stopped (as an unanswered line does); the cap needs the measured
          // size of the largest answer line first.
          awaitedLine(session.copy(pending = session.pending + chunk), deadline)
        else if !session.process.isAlive then
          if session.answers.available() > 0 then awaitedLine(session, deadline) else Awaited.Ended
        else if System.nanoTime >= deadline then Awaited.TimedOut(session)
        else
          Thread.sleep(pollInterval)
          awaitedLine(session, deadline)
      case end =>
        val bytes = session.pending.substring(0, end).getBytes(StandardCharsets.ISO_8859_1)
        Awaited.Line(String(bytes, StandardCharsets.UTF_8), session.copy(pending = session.pending.substring(end + 1)))

  /** The session's JVM killed and waited for. */
  /** How long a JVM whose pipe ended is waited for to exit before it is
    * read as alive and stopped: the pipe closes as the process exits, so an
    * exit is seen within milliseconds; a second leaves room on a loaded
    * machine and is spent only on a point already stopped.
    */
  private val deathWaitSeconds = 1L

  private def stopped(session: Session): Unit =
    session.process.destroyForcibly()
    session.process.waitFor()

  private def nanoseconds(seconds: Double): Long = (seconds * 1e9).toLong

  /** The column header of the table. */
  val header: String = "point\treader\tfamily\tkind\toutcome\tshare\twall_seconds\tfamily_wall_seconds\tcores\tbudget_exhausted\tphases\tcancel"

  /** The table: comment lines with the seed and the provenance
    * (`TableProvenance.lines`), the header and the rows, one a line,
    * tab-separated. The seed's hash is published before the
    * deadline (`sha256sum`), outside the judge.
    */
  def table(seed: Long, provenance: TableProvenance, rows: Vector[Row]): String =
    ((s"# seed $seed" +: provenance.lines) ++ (header +: rows.map(_.written))).mkString("", "\n", "\n")

/** Where a table's rows come from: the SHA-256 of the points file read, the
  * SHA-256 of the programs file beside it (`PointsFile.programsFileName`),
  * or `TableFile.noPrograms` when the directory has none, the Gezi
  * commit of the build that read it (`-dirty` when its tree differed from
  * the commit), and, when the run reused an earlier table's rows
  * (`--reuse-table`), that table's path and SHA-256, and the path and
  * SHA-256 of the published reference times the budgets went by
  * (`--family-references`), which a table written before the option was
  * required may lack. A reused table is refused unless its points, programs
  * and build are the run's (`TableFile.reused`), so that no stale row
  * stands in a run's table.
  */
final case class TableProvenance(
    pointsDigest: String,
    programsDigest: String,
    build: String,
    reused: Option[(String, String)],
    familyReferences: Option[(String, String)]
):
  def lines: Vector[String] =
    Vector(s"# points $pointsDigest", s"# programs $programsDigest", s"# build $build") ++
      reused.toVector.map((path, digest) => s"# reused $path $digest") ++
      familyReferences.toVector.map((path, digest) => s"# family-references $path $digest")

/** An earlier table read back: its seed, provenance and rows. */
final case class ReadTable(seed: Long, provenance: TableProvenance, rows: Vector[Row])

/** Reading tables back, and the facts their provenance compares. */
object TableFile:

  /** What the line `# programs` records when the points directory holds no
    * programs file (a directory of evaluation points the writer of an
    * earlier layout made, or one assembled by hand without it). A SHA-256
    * is 64 hexadecimal digits, so it is never this word.
    */
  val noPrograms: String = "none"

  /** The table at the path. Throws `IllegalArgumentException` for a file
    * without the seed, points, programs or build line, or with a row of
    * another shape.
    */
  def read(path: Path): ReadTable =
    val lines = Files.readString(path, StandardCharsets.UTF_8).split('\n').toVector.filter(_.nonEmpty)
    def comment(name: String): Option[String] =
      lines.collectFirst { case line if line.startsWith(s"# $name ") => line.drop(name.length + 3) }
    def required(name: String): String =
      comment(name).getOrElse(throw IllegalArgumentException(s"the table $path has no line # $name"))
    def pathAndDigest(name: String): Option[(String, String)] = comment(name).map(value =>
      value.split(' ').toVector match
        case Vector(givenPath, digest) => (givenPath, digest)
        case other                     => throw IllegalArgumentException(s"the table $path has a line # $name of another shape: $other")
    )
    val rows = lines.filterNot(line => line.startsWith("#") || line == Supervisor.header).map(line =>
      line.split('\t').toVector match
        case Vector(point, reader, family, kind, outcome, shareText, wall, familyWall, cores, exhausted, phasesText, cancelText) =>
          val share = Share
            .read(shareText)
            .getOrElse(throw IllegalArgumentException(s"the table $path has a row whose share is not read: $shareText"))
          val phases = PipeLines
            .phasesRead(phasesText)
            .getOrElse(throw IllegalArgumentException(s"the table $path has a row whose phases are not read: $phasesText"))
          val cancel = Cancel
            .read(cancelText)
            .getOrElse(throw IllegalArgumentException(s"the table $path has a row whose cancel is not read: $cancelText"))
          Row(point, reader, family, kind, outcome, share, wall.toDouble, familyWall.toDouble, cores, exhausted.toBoolean, phases, cancel)
        case other => throw IllegalArgumentException(s"the table $path has a row of another shape: $other")
    )
    ReadTable(
      required("seed").toLong,
      TableProvenance(
        required("points"),
        required("programs"),
        required("build"),
        pathAndDigest("reused"),
        pathAndDigest("family-references")
      ),
      rows
    )

  /** The SHA-256 of the file, in hexadecimal, as `sha256sum` prints it. */
  def digest(path: Path): String =
    val process = ProcessBuilder("sha256sum", path.toString).redirectErrorStream(true).start()
    val printed = String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8)
    if process.waitFor() != 0 then throw IllegalStateException(s"sha256sum failed on $path: $printed")
    printed.split(' ').headOption.filter(_.length == 64).getOrElse(throw IllegalStateException(s"sha256sum printed $printed"))

  /** The commit of the build at the root, with `-dirty` when its tracked
    * files differ from the commit.
    */
  def build(buildRoot: Path): String =
    def git(arguments: String*): String =
      val process = ProcessBuilder(("git" +: "-C" +: buildRoot.toString +: arguments.toVector)*).redirectErrorStream(true).start()
      val printed = String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8).trim
      if process.waitFor() != 0 then throw IllegalStateException(s"git ${arguments.mkString(" ")} failed: $printed")
      printed
    val commit = git("rev-parse", "HEAD")
    if git("status", "--porcelain", "--untracked-files=no").isEmpty then commit else s"$commit-dirty"

  /** The SHA-256 of the programs file in the points directory, or
    * `noPrograms` when it has none.
    */
  def programsDigest(pointsDirectory: Path): String =
    val programs = pointsDirectory.resolve(PointsFile.programsFileName)
    if Files.exists(programs) then digest(programs) else noPrograms

  /** The rows of the earlier table to reuse, refused (`IllegalArgumentException`)
    * unless it was read on the same points file and programs file, with the
    * same seed, by the same build, as the run about to start.
    */
  def reused(earlier: ReadTable, seed: Long, pointsDigest: String, programsDigest: String, build: String): Vector[Row] =
    if earlier.provenance.pointsDigest != pointsDigest then
      throw IllegalArgumentException(s"the reused table read points ${earlier.provenance.pointsDigest}, not $pointsDigest")
    if earlier.provenance.programsDigest != programsDigest then
      throw IllegalArgumentException(s"the reused table read programs ${earlier.provenance.programsDigest}, not $programsDigest")
    if earlier.provenance.build != build then
      throw IllegalArgumentException(s"the reused table was read by build ${earlier.provenance.build}, not $build")
    if earlier.seed != seed then throw IllegalArgumentException(s"the reused table has seed ${earlier.seed}, not $seed")
    earlier.rows

/** The supervisor's command line, options of the form `--name value`:
  *
  *   - `--entry <name>`: the entry `contest-entries-<name>/` of the build. Its
  *     JVM's classpath (`entryReaderClasspath`) is the runner's, which the
  *     build passes as the property `gezi.judge.runnerClasspath` (the
  *     module `contest-runner` and what it depends on), followed by the entry
  *     project's, which the build passes as the property
  *     `gezi.judge.entryClasspath.<name>`; neither holds
  *     `contest-corpora` or `contest-judge`. The reference
  *     readers' JVMs run on the supervisor's own classpath;
  *   - `--points <directory>`: the directory of the round's `points.tsv`
  *     and `programs.tsv` (`PointsFile`), hidden or public, given only to
  *     the supervisor;
  *   - `--seed <number>`: the seed, a 64-bit integer, which draws the order
  *     of the families and of each family's points (`SeededOrder`); the
  *     table records it. For tests and public runs only;
  *   - `--seed-file <path>`: the seed, read from the file's first line, in
  *     place of `--seed`, for a round (`seed`); exactly one of the two is
  *     given;
  *   - `--references <names>`: reference readers read on the same points
  *     before the entry, comma-separated, of which there is one,
  *     `tabling(weak_head)`, each family within the cap;
  *   - `--budget-multiple`, `--budget-floor <seconds>`, `--budget-cap
  *     <seconds>`: the family budget's rule (`FamilyBudgets`), by default 20
  *     times the family's published reference time, at least 60 s and at
  *     most 600 s;
  *   - `--setup-limit <seconds>`: the wall-clock limit of a setup;
  *   - `--cancel-grace <seconds>`: how long an entry's call has to return
  *     after the cancel at its point's budget before the JVM is killed, by
  *     default 2; the grace is not charged to the family;
  *   - `--slice <name>`: the systemd user slice, required, `none` for no
  *     slice; a round gives `contest-judge.slice`;
  *   - `--cores <list>`: the cores of `taskset -c` for the reader's JVM,
  *     required, `any` for no binding; a round gives `8,9` (the judge has
  *     CPUs 8 to 11; the entry being read runs alone on 8 and 9, and the
  *     supervisor itself is started on 10 and 11, `taskset -c 10,11`);
  *   - `--nice <number>`: the niceness of the reader's JVM, none by default;
  *   - `--entry-heap <size>`: the heap (`-Xmx`) of every entry's JVM, as
  *     the rules set it for the round (e.g. `3g`);
  *     by default `256m`, the debugging limit. Reference readers keep 256m;
  *   - `--entry-parallelism <number>`: the carrier threads of every entry's
  *     virtual-thread scheduler (`-Djdk.virtualThreadScheduler.parallelism`),
  *     as the rules set it for the round (e.g. 2, one physical core per
  *     entry); by default not set, the JDK's own default. Reference readers
  *     never get it;
  *   - `--sandbox <mechanism>`: the sandbox of every entry's JVM
  *     (`Sandbox`): `bubblewrap` by default, `none` to
  *     run without it, for tests that cannot use it (`sandbox`);
  *   - `--flight-recordings <directory>`: a practice pass's Java Flight
  *     Recorder recordings, one a cell of every entry's JVM, written to
  *     `<directory>/<reader>/<point>.jfr` (`FlightRecordings` of
  *     contest-runner); by default none, and never in a scored pass, since
  *     writing a recording is counted in the next cell's time;
  *   - `--output <file>`: the table, a TSV; the JVMs' standard errors, and
  *     the lines they wrote that were not answers, go to its directory;
  *   - `--reuse-table <file>`: an earlier table of the same points file,
  *     programs file, seed and build (`TableFile.reused`; refused
  *     otherwise). Each reader
  *     whose rows it holds, the reference readers among them, is taken from
  *     it and not read again.
  *     Entries are read in parallel by one supervisor per entry, each with
  *     its own `--entry`, `--cores`, `--slice` and `--output` and the same
  *     `--reuse-table`, so that a pass takes less time: each entry in its own slice on its own cores.
  *   - `--family-references <file>`: the published reference time of each
  *     family (`FamilyReferences`), which sets an entry's budget for it,
  *     required: the families' budgets go by the published reference times
  *     only,
  *     and a pass without the option throws `IllegalArgumentException`
  *     saying so before it reads anything. Refused when a family of the
  *     points file is missing from it. The table records the file's path and
  *     SHA-256;
  *
  *   - `--article-seed <number>`: the article check after the pass,
  *     for the entry of
  *     `--entry`: every evaluation point it answered falsely and one answered
  *     evaluation point of each family, drawn from this seed
  *     (`ArticleRereading.selected`), is re-read in a new JVM with its
  *     articles recorded (`Supervisor.reread`) and checked (`ArticleCheck`);
  *     the results go to `articles.tsv` beside the table, each point's
  *     articles, manifest (`ArticleManifest`) and logs to
  *     `articles/<point>-<n>/` there. Without it no article is checked.
  *     Refused when the entry's rows are reused;
  *   - `--article-allowance <number>`: the re-read's budget, the family's
  *     budget times this, by default 2;
  *   - `--trace-player <directory>`: the player's directory (the sbt task
  *     `trace-player/demonstrationPage` makes it, `trace-player/` under its
  *     result), copied beside `articles/index.html`, the page that lists the
  *     trace pages of the checked points (`TracePages`), and linked from
  *     each point's article directory, so that the pages play from
  *     `file://`. Without it the page is written and the pages look for the
  *     player beside them;
  *   - `--article-knowledge <path>`: an explicit override of the knowledge
  *     the judge compiles to encode a point's IR in its manifest: the
  *     lambdalattice file, relative to the build root, whose member
  *     `knowledge` is compiled (`articleLibrary`), and whose path the
  *     manifest records. By default the knowledge is the re-read entry's
  *     own, the knowledge of its `contest-entries-<name>/entry.lambdalattice`
  *     as the generic entry compiles it (`entryKnowledgeLibrary`), and the
  *     manifest records that file's path.
  *
  * `--slice` and `--cores` have no default, so that a command that leaves
  * them out never lands on the judge's slice and cores. A pass missing
  * either throws before it reads anything (`placement`); `none` and `any`
  * are the explicit way to turn them off. A round gives `--slice
  * contest-judge.slice --cores 8,9`; the tests give `--slice none --cores
  * any`, since a test
  * environment need not have the slice, and since the judge's cores are
  * kept free for a round.
  */
object SupervisorCommand:

  /** The options of the arguments. Throws `IllegalArgumentException` for an
    * argument that is not an option followed by its value.
    */
  def options(arguments: Vector[String]): Map[String, String] =
    arguments.grouped(2).toVector.map {
      case Vector(name, value) if name.startsWith("--") => name.drop(2) -> value
      case other                                        => throw IllegalArgumentException(s"not an option and its value: $other")
    }.toMap

  /** The seed the options give, if any: `--seed <number>`, or `--seed-file
    * <path>`, the number on the file's first line. A seed passed as a
    * number is on the command line, where `ps` and the sbt server's global
    * log (`sbt runMain`) show it; a round's seed is passed by its file, which
    * keeps it off the command line. Throws `IllegalArgumentException` when both are
    * given, or when the file's first line is not a 64-bit integer; the
    * message never holds the file's text.
    */
  def seed(options: Map[String, String]): Option[Long] = (options.get("seed"), options.get("seed-file")) match
    case (Some(_), Some(_))   => throw IllegalArgumentException("give the option --seed or --seed-file, not both")
    case (Some(number), None) => Some(number.toLong)
    case (None, Some(path))   =>
      Some(
        Files.readString(Paths.get(path), StandardCharsets.UTF_8).split('\n').headOption.flatMap(_.trim.toLongOption).getOrElse(
          throw IllegalArgumentException(s"the first line of the seed file $path is not a 64-bit integer")
        )
      )
    case (None, None) => None

  /** The classpath of an entry's JVM: the runner's, the property
    * `gezi.judge.runnerClasspath`, followed by the entry project's,
    * each element once. The runner's comes first, so that an entry's
    * classes cannot stand in for the runner's or the framework's.
    */
  def entryReaderClasspath(entryProjectClasspath: String): String =
    val runnerClasspath = sys.props.getOrElse(
      "gezi.judge.runnerClasspath",
      throw IllegalArgumentException("the build passes no classpath of the runner")
    )
    (runnerClasspath.split(File.pathSeparator).toVector ++ entryProjectClasspath.split(File.pathSeparator).toVector)
      .filter(_.nonEmpty)
      .distinct
      .mkString(File.pathSeparator)

  /** The slice and the cores the options give: `--slice <name>`, `None` for
    * `none`, and `--cores <list>`, `None` for `any`. Throws
    * `IllegalArgumentException`, naming both options and their round
    * values, when either is missing: neither has a default.
    */
  def placement(options: Map[String, String]): (Option[String], Option[String]) =
    (options.get("slice"), options.get("cores")) match
      case (Some(slice), Some(cores)) => (Some(slice).filter(_ != "none"), Some(cores).filter(_ != "any"))
      case _ =>
        throw IllegalArgumentException(
          "the options --slice and --cores are both required: a round gives --slice contest-judge.slice --cores 8,9, and --slice none --cores any turn them off"
        )

  /** The sandbox the options give: `--sandbox bubblewrap`, the default when
    * the option is missing, is the bubblewrap sandbox of the JDK this JVM
    * runs on in the build at `buildRoot` (`Sandbox.bubblewrap`); `--sandbox
    * none` is none. Throws `IllegalArgumentException` for another value.
    */
  def sandbox(options: Map[String, String], buildRoot: Path): Sandbox = options.getOrElse("sandbox", "bubblewrap") match
    case "bubblewrap" => Sandbox.bubblewrap(Paths.get(System.getProperty("java.home")), buildRoot)
    case "none"       => Sandbox.Unconfined
    case other        => throw IllegalArgumentException(s"the option --sandbox is bubblewrap or none, not $other")

  /** The pass the options describe, its table written to the output file;
    * the rows. Throws `IllegalArgumentException` for a missing `--slice` or
    * `--cores` (`placement`) or a missing `--family-references`
    * (`familyReferencesOption`) before it reads anything.
    */
  def run(options: Map[String, String]): Vector[Row] =
    def required(name: String): String =
      options.getOrElse(name, throw IllegalArgumentException(s"the option --$name is required"))
    val (slice, cores) = placement(options)
    val familyReferences = Paths.get(familyReferencesOption(options)).toAbsolutePath
    // Absolute: a sandboxed JVM's working directory is the entry's directory,
    // where a relative path of the entry's directory would not resolve.
    val buildRoot = Paths.get(options.getOrElse("build-root", sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalArgumentException("the option --build-root or the property gezi.buildRoot is required")
    ))).toAbsolutePath
    val ownClasspath = System.getProperty("java.class.path")
    def entryReader(player: String): Reader =
      val classpath = sys.props.getOrElse(
        s"gezi.judge.entryClasspath.$player",
        throw IllegalArgumentException(s"the build passes no classpath of the entry $player")
      )
      Reader(player, entryReaderClasspath(classpath), Launched.EntryLaunched(buildRoot.resolve(s"contest-entries-$player")))
    val player = required("entry")
    val seed = SupervisorCommand.seed(options).getOrElse(throw IllegalArgumentException("the option --seed or --seed-file is required"))
    val families = PointsFile.ordered(PointsFile.read(Paths.get(required("points"))), seed)
    val output = Paths.get(required("output")).toAbsolutePath
    Files.createDirectories(output.getParent)
    val limits = Limits(
      FamilyBudgets(
        options.getOrElse("budget-multiple", "20").toDouble,
        options.getOrElse("budget-floor", "60").toDouble,
        options.getOrElse("budget-cap", "600").toDouble
      ),
      required("setup-limit").toDouble,
      options.getOrElse("cancel-grace", "2").toDouble,
      slice,
      cores,
      options.get("nice").map(_.toInt),
      output.getParent,
      options.getOrElse("entry-heap", "256m"),
      options.get("entry-parallelism").map(_.toInt),
      sandbox(options, buildRoot),
      ArticleDestination.Discarded,
      options.get("flight-recordings").map(path => Paths.get(path).toAbsolutePath)
    )
    val references = options.get("references").toVector.flatMap(_.split(',').toVector).filter(_.nonEmpty)
    val readers =
      references.map(name => Reader(name, ownClasspath, Launched.ReferenceLaunched(name))) :+ entryReader(player)
    val pointsDigest = TableFile.digest(Paths.get(required("points")).resolve(PointsFile.fileName))
    val programsDigest = TableFile.programsDigest(Paths.get(required("points")))
    val build = TableFile.build(buildRoot)
    val reusedTable = options.get("reuse-table").map(path => Paths.get(path).toAbsolutePath)
    val reused =
      reusedTable.toVector.flatMap(path => TableFile.reused(TableFile.read(path), seed, pointsDigest, programsDigest, build))
    val anchor = BudgetAnchor.Published(FamilyReferences.read(familyReferences, families.map(_._1)))
    val provenance = TableProvenance(
      pointsDigest,
      programsDigest,
      build,
      reusedTable.map(path => (path.toString, TableFile.digest(path))),
      Some((familyReferences.toString, TableFile.digest(familyReferences)))
    )
    val read = Supervisor.passRead(anchor, readers, families, limits, reused)
    Files.writeString(output, Supervisor.table(seed, provenance, read.rows))
    options.get("article-seed").map(_.toLong).foreach { articleSeed =>
      val (knowledgeFile, library) = options.get("article-knowledge") match
        case Some(file) => (file, articleLibrary(buildRoot, file))
        case None =>
          (s"contest-entries-$player/$entryDataFileName", entryKnowledgeLibrary(buildRoot.resolve(s"contest-entries-$player")))
      val lines = ArticleRereading.table(
        entryReader(player),
        families,
        read,
        articleSeed,
        options.getOrElse("article-allowance", "2").toDouble,
        output.getParent.resolve("articles"),
        ManifestProvenance(build, knowledgeFile, library.index),
        limits,
        options.get("trace-player").map(Paths.get(_))
      )
      ArticleRereading.written(output.getParent.resolve("articles.tsv"), lines)
    }
    read.rows

  /** The path of `--family-references`, which every pass needs: the
    * families' budgets go by the published reference times only, and no
    * entry is read first to set them.
    * Throws
    * `IllegalArgumentException` saying so when the option is not given.
    */
  def familyReferencesOption(options: Map[String, String]): String =
    options.getOrElse(
      "family-references",
      throw IllegalArgumentException(
        "the option --family-references is required: the families' budgets go by the published reference times only, and no entry is read to set them"
      )
    )

  /** The file of an entry's directory that writes an entry as data, whose
    * knowledge the article re-read encodes a point against by default.
    */
  val entryDataFileName: String = "entry.lambdalattice"

  /** The library of the knowledge of the entry written as data in the
    * directory, compiled with no backend: its `entry.lambdalattice` read as
    * the generic entry reads it (`EntryData.read`, off the tree whose visible
    * subtree is the directory's parent, through `StandardLibrary.entryTerm`),
    * and its knowledge, the choice of its backend's and its rounds' records
    * (`EntryData.knowledge`), which the generic entry compiles into its
    * library, compiled under the same reading state. Throws `EntryDataError`
    * for a directory with no `entry.lambdalattice`, an entry written in
    * Scala, whose knowledge `--article-knowledge` names instead.
    */
  def entryKnowledgeLibrary(entryDirectory: Path): StandardLibrary =
    val (data, afterEntry) = EntryData.read(entryDirectory, Defaults.entryDataState)
    StandardLibrary.compiled(data.knowledge, Vector.empty, afterEntry)._1

  /** The library of the knowledge of the file at the path relative to the
    * build root, the first field of the Scott tuple its tuple holds
    * (`λs. s knowledge enabled`, the program families' fixtures), compiled with
    * no backend: the file read in its tree's scope, off the tree whose visible
    * subtree is the build root (`StandardLibrary.entryTerm`), so that its
    * imports go through the tree, then its field read off the group its tuple
    * holds (`StandardLibrary.entryGroup`, `KnowledgeReading.fields`), all under
    * one compilation's reading state.
    */
  def articleLibrary(buildRoot: Path, knowledgeFile: String): StandardLibrary =
    val (group, afterEntry) = StandardLibrary.entryGroup(
      StandardLibrary.entryTerm(buildRoot, buildRoot.resolve(knowledgeFile), KnowledgeReading.compilationState)
    )
    val (fields, afterFields) = KnowledgeReading.run(KnowledgeReading.fields(group, 2), StandardLibrary.memberReadingLimit, afterEntry)
    val knowledge = fields.headOption.map(KnowledgeReading.term(_, Set.empty)).getOrElse(throw IllegalStateException("a tuple of two fields has none"))
    StandardLibrary.compiled(knowledge, Vector.empty, afterFields)._1

/** The supervisor's main: the options of `SupervisorCommand`. */
@main def judgeSupervisor(arguments: String*): Unit =
  SupervisorCommand.run(SupervisorCommand.options(arguments.toVector))
