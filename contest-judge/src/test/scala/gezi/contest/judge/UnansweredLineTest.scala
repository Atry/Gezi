package gezi.contest.judge

import hedgehog.Gen
import gezi.ir.Configured
import gezi.ir.NoFacts
import hedgehog.Range
import java.io.FileDescriptor
import java.io.FileOutputStream
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.Interaction
import gezi.frontend.DeBruijnTerm
import gezi.generatedinputs.SeededSnapshots
import gezi.hotspot.Cache
import gezi.saturation.StopSignal
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*
import scala.util.Using
import snapshot4s.generated.snapshotConfig

/** The probe entry of `UnansweredLineTest`. On an evaluation point it does
  * what the file `behaviour` of its directory says: `exhaust` holds ever
  * more memory until the JVM, which runs with `-XX:+ExitOnOutOfMemoryError`,
  * writes its message on the pipe and ends; `stray` writes a line of its own
  * on the pipe (the process's original standard output, which the runner
  * keeps from `System.out`) and answers none. A judgment point (a cell
  * whose Output is a parallel) it answers unknown, the Output displayed
  * unreduced. The runner writes each lifecycle event it hands the cache
  * provider to the JVM's standard error, which the supervisor keeps in a
  * file for each JVM, as a line `lifecycle <event>`.
  */
final class PipeProbe extends EntryProvider:

  def initial(entryDirectory: Path, cache: Cache, articles: ArticleDestination): Entry[?] =
    Files.readString(entryDirectory.resolve("behaviour")) match
      case "exhaust" => PipeProbe.Exhausting(cache)
      case "stray"   => PipeProbe.Straying(cache)
      case other     => throw IllegalArgumentException(s"no behaviour $other")

/** The probe's two behaviours, each holding the judge's cache service. */
object PipeProbe:

  /** The entry that exhausts its heap on an evaluation point. */
  final case class Exhausting(cache: Cache) extends Entry[NoFacts.type]:
    def run(cell: gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[NoFacts.type] =
      if judgment(cell) then unanswered(cell, this) else exhausted(Nil)

  /** The entry that writes a stray line on the pipe on an evaluation point. */
  final case class Straying(cache: Cache) extends Entry[NoFacts.type]:
    def run(cell: gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[NoFacts.type] =
      if !judgment(cell) then
        val pipe = FileOutputStream(FileDescriptor.out)
        pipe.write("a stray line\n".getBytes(StandardCharsets.UTF_8))
        pipe.flush()
      unanswered(cell, this)

  /** Whether the cell's Output is a parallel, as a judgment point's is. */
  private def judgment(cell: DeBruijnTerm): Boolean =
    Cells.output(cell, Cells.initialState) match
      case DeBruijnTerm.Parallel(_, _) => true
      case _                           => false

  /** The cell finished with its Output displayed unreduced, asserting
    * nothing.
    */
  private def unanswered(cell: DeBruijnTerm, entry: Entry[NoFacts.type]): Interaction[NoFacts.type] =
    Interaction.Finished(Cells.unreducedOutput(cell, Cells.initialState), Vector.empty, entry)

  /** Never returns: each step holds one more vector of a million cells. */
  @tailrec
  private def exhausted(held: List[Vector[Long]]): Nothing = exhausted(Vector.fill(1 << 20)(0L) :: held)

/** A reader that stops answering in the middle of a family is read as
  * stopped, and the judge goes on: its purpose is to catch a supervisor that takes a line that is not an
  * answer, such as the message the JVM writes on its standard output when it
  * ends on an `OutOfMemoryError`, for an answer, or that dies on it instead
  * of recording the point stopped and reading the next point in a new JVM.
  *
  * The probe entry `PipeProbe` stops answering on every evaluation point,
  * by exhausting its heap or by writing a stray line, and answers every
  * judgment point. Each sample is a behaviour and a family of points of
  * generated kinds; the snapshot records the rows: every evaluation point
  * stopped, every judgment point after it read by a new JVM (a setup row)
  * and answered unknown; then, for each JVM, the lifecycle events its runner
  * handed the cache provider. These are there to catch a supervisor that tells a JVM started
  * again within the pass that the round started (only the pass's first JVM
  * hears `RoundStarted`), or that loses `FamilyFinished` and `RoundFinished`
  * on the JVM still running at the end. Every JVM runs in the sandbox
  * (`Sandbox`), as an entry's does.
  */
class UnansweredLineTest extends gezi.generatedinputs.FailFastSuite with SeededSnapshots:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of UnansweredLineTest, "a reader that writes no answer line reads stopped, and a new JVM reads on", takes 32.356 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it starts real JVMs of a reader and a new reader (end to end).
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(50, "s")

  /** A behaviour and the kinds of a family's points, `true` an evaluation. */
  private val samples: Gen[(String, List[Boolean])] =
    for
      behaviour <- Gen.element1("exhaust", "stray")
      kinds <- Gen.element1(true, false).list(Range.constant(2, 4))
    yield (behaviour, kinds)

  private val program = DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** The program's instruction, which a point holds. */
  private val programInstruction: Configured[NoFacts.type] = gezi.frontend.Defunctionalization.thunkInstruction(program)(using gezi.ir.NoFacts)

  /** The rows of the pass, a point and its outcome a line, then each line
    * the supervisor read that was not an answer, by the file it wrote it to,
    * then the lifecycle events each JVM's runner handed the cache provider,
    * in order, by its
    * standard error's file.
    *
    * A JVM that did not hear `RoundFinished` was stopped, and from a stopped
    * JVM a trailing `PointFinished` is dropped: the supervisor kills the JVM
    * as soon as it reads the stray line, while the runner, once the entry
    * has written that line and returned, hands `PointFinished` on, so
    * whether the event reaches the file depends on which of the two comes
    * first (measured 2026-11-02: on probe-2 of sample 1, one work tree
    * recorded it twice in two runs and another, with the same supervisor and
    * probe, did not, twice).
    */
  private def read(behaviour: String, kinds: List[Boolean]): String =
    val classes = ProbeEntries.classes(classOf[PipeProbe])
    val entryDirectory = Files.createTempDirectory("judge-unanswered")
    Files.writeString(entryDirectory.resolve("behaviour"), behaviour)
    val points = kinds.toVector.zipWithIndex.map((evaluation, position) =>
      val question = if evaluation then Question.Evaluation(Set(program)) else Question.Judgment(programInstruction, true)
      Point(s"point_$position", "test", "test", BigDecimal(1), gezi.frontend.ExchangeText.line(programInstruction), question)
    )
    val reader = Reader("probe", SupervisorCommand.entryReaderClasspath(classes.toString), Launched.EntryLaunched(entryDirectory))
    val limits = Limits(FamilyBudgets(20, 60, 60), 60, 2, None, None, None, entryDirectory, "256m", None, TestSandbox.bubblewrap, ArticleDestination.Discarded, None)
    // The family's published reference time; the floor is the cap, so its
    // budget is the cap.
    val rows = Supervisor.pass(BudgetAnchor.Published(Map("test" -> 3.0)), Vector(reader), Vector(("test", points)), limits)
    val files = Using.resource(Files.list(entryDirectory))(_.toList.asScala.toVector).map(_.getFileName.toString).sorted
    val unanswered = files
      .filter(_.endsWith(".unanswered"))
      .map(name => s"$name: ${Files.readString(entryDirectory.resolve(name)).stripLineEnd}")
    val events = files
      .filter(_.endsWith(".stderr"))
      .map(name =>
        val taken = Files.readAllLines(entryDirectory.resolve(name)).asScala.toVector.filter(_.startsWith("lifecycle ")).map(_.stripPrefix("lifecycle "))
        val recorded =
          if !taken.lastOption.contains("RoundFinished") && taken.lastOption.contains("PointFinished") then taken.init
          else taken
        s"$name: ${recorded.mkString(" ")}"
      )
    (rows.map(row => s"${row.point} ${row.outcome}") ++ unanswered ++ events).mkString("\n")

  test("a reader that writes no answer line reads stopped, and a new JVM reads on") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    assertSeededSnapshot(samples, 20261031L, 3, "judge/unanswered_lines.txt")(
      (behaviour, kinds) => s"$behaviour: ${kinds.map(if _ then "evaluation" else "judgment").mkString(" ")}",
      identity[String]
    )(read)
  }
