package com.yang_bo.gezi.contest.judge

import hedgehog.Gen
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import hedgehog.Range
import java.nio.file.Files
import java.nio.file.Path
import com.yang_bo.gezi.contest.entry.ArticleDestination
import com.yang_bo.gezi.contest.entry.Cells
import com.yang_bo.gezi.contest.entry.Count
import com.yang_bo.gezi.contest.entry.Entry
import com.yang_bo.gezi.contest.entry.EntryProvider
import com.yang_bo.gezi.contest.entry.Interaction
import com.yang_bo.gezi.contest.runner.PipeLines
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.generatedinputs.SeededSnapshots
import com.yang_bo.gezi.hotspot.Cache
import com.yang_bo.gezi.saturation.StopSignal
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*
import scala.util.Using
import snapshot4s.generated.snapshotConfig

/** The probe entry of `CancelTest`. What it does on a point is what the file
  * `behaviour` of its directory says: `honour` spins on its first call until
  * the call's stop signal asks for a stop, then answers none (the Output
  * displayed unreduced, asserting nothing), and answers so at once on every
  * later call; `ignore` spins forever on every call, never reading the signal;
  * `die` has its own JVM killed with SIGKILL on every call, as the kernel's OOM
  * killer kills it.
  */
final class CancelProbe extends EntryProvider:

  def initial(
      entryDirectory: Path,
      cache: Cache,
      articles: ArticleDestination
  ): Entry[?] =
    Files.readString(entryDirectory.resolve("behaviour")) match
      case "honour" => CancelProbe.Honouring(cache, called = false)
      case "ignore" => CancelProbe.Ignoring(cache)
      case "die"    => CancelProbe.Dying(cache)
      case other    => throw IllegalArgumentException(s"no behaviour $other")

/** The probe's two behaviours, each holding the judge's cache service. */
object CancelProbe:

  /** The entry that honours the cancel on its first call, and whether that call
    * was made.
    */
  final case class Honouring(cache: Cache, called: Boolean)
      extends Entry[NoFacts.type]:
    def run(
        cell: com.yang_bo.gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]],
        source: com.yang_bo.gezi.hotspot.ExpansionSource,
        stop: StopSignal
    ): Interaction[NoFacts.type] =
      if !called then spunUntil(stop)
      Interaction.Finished(
        Cells.unreducedOutput(cell, Cells.initialState),
        Vector(Count("probe_calls_before", if called then 1L else 0L)),
        copy(called = true)
      )

  /** The entry that spins forever on every call, the signal ignored. */
  final case class Ignoring(cache: Cache) extends Entry[NoFacts.type]:
    def run(
        cell: com.yang_bo.gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]],
        source: com.yang_bo.gezi.hotspot.ExpansionSource,
        stop: StopSignal
    ): Interaction[NoFacts.type] = spun(0L)

  /** The entry whose JVM is killed with SIGKILL on every call. */
  final case class Dying(cache: Cache) extends Entry[NoFacts.type]:
    def run(
        cell: com.yang_bo.gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]],
        source: com.yang_bo.gezi.hotspot.ExpansionSource,
        stop: StopSignal
    ): Interaction[NoFacts.type] = killed()

  /** Has `kill -9` kill this JVM, and waits for the signal. */
  private def killed(): Nothing =
    ProcessBuilder("kill", "-9", ProcessHandle.current.pid.toString)
      .start()
      .waitFor()
    spun(0L)

  /** Returns once the signal asks for a stop. */
  @tailrec
  private def spunUntil(stop: StopSignal): Unit =
    if !stop.stopRequested then
      Thread.onSpinWait()
      spunUntil(stop)

  @tailrec
  private def spun(count: Long): Nothing = spun(count + 1)

/** The cancel at a point's budget: its purpose is to catch a supervisor that
  * kills a JVM whose call returned within the grace, that loses the family's
  * `family_finished` on the JVM it kept, that keeps a JVM whose call did not
  * return, or that charges the grace to the family.
  *
  * Each sample is a behaviour of the probe entry `CancelProbe` and the kinds of
  * two points, each a family of its own (one family in the test of one family
  * below), read with a family budget of `capSeconds` and a grace of
  * `graceSeconds`, outside the sandbox. The snapshot records each row's point,
  * outcome, whether its point's budget ran out, and its cancel, then the
  * lifecycle events each JVM's runner handed the cache provider: an entry that
  * honours the cancel keeps its one JVM, its first point stopped with the
  * cancel `returned` and its second point answered; one that ignores it is
  * killed on each point, each stopped with the cancel `killed` after a setup of
  * its own. Each row's reports are recorded too: the stopped point whose call
  * returned keeps the count its line reported (`probe_calls_before`), with no
  * answer, and a killed point keeps none. Every sample also checks that the
  * first point's wall time is the budget's and not the grace's: below its
  * budget plus half a second.
  */
class CancelTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with SeededSnapshots:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CancelTest, "a call that returns within the cancel's grace keeps its JVM; one that does not is killed", takes 9.670 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it starts real JVMs and kills one at the cancel (end to end).
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  private val capSeconds = 1.0

  /** The family budget of the died case, far beyond the probe's own kill. The
    * `die` probe kills its JVM by forking and executing `kill -9` from inside
    * the point's call (`CancelProbe.killed`), so the point ends by whichever
    * comes first: the signal, recorded `died:137`, or the family budget,
    * recorded as the supervisor's own kill. Under the cancel cases' 1 s budget
    * the order depended on the fork's latency: in a full `test` on 2 CPUs with
    * a GC-bound sbt server (main d7a60af59, 2026-11-15) the budget ran out
    * first and both points read `stopped true killed`, while the case passed
    * alone. The case's subject is the cause of the end, not its time.
    */
  private val diedCapSeconds = 30.0

  private val graceSeconds = 2.0

  /** A behaviour and the kinds of the two families' points, `true` an
    * evaluation.
    */
  private val samples: Gen[(String, List[Boolean])] =
    for
      behaviour <- Gen.element1("honour", "ignore")
      kinds <- Gen.element1(true, false).list(Range.singleton(2))
    yield (behaviour, kinds)

  private val program = DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** The program's instruction, which a point holds. */
  private val programInstruction: Configured[NoFacts.type] =
    com.yang_bo.gezi.frontend.Defunctionalization.thunkInstruction(program)(using
      com.yang_bo.gezi.ir.NoFacts
    )

  /** The rows of the pass, each with its point, outcome, budget flag and
    * cancel, then the lifecycle events of each JVM, by its standard error's
    * file. The table, with the wall times, is written to `table.tsv` of the log
    * directory. Each family has a budget of `cap` seconds, each point in a
    * family of its own or, when `oneFamily`, all in one family, and the first
    * point's wall time must stay below its budget, `cap` over the points of its
    * family, plus half a second.
    */
  private def read(
      behaviour: String,
      kinds: List[Boolean],
      cap: Double,
      oneFamily: Boolean
  ): String =
    val classes = ProbeEntries.classes(classOf[CancelProbe])
    val entryDirectory = Files.createTempDirectory("judge-cancel")
    Files.writeString(entryDirectory.resolve("behaviour"), behaviour)
    def familyName(position: Int) =
      if oneFamily then "family_0" else s"family_$position"
    val points = kinds.toVector.zipWithIndex.map((evaluation, position) =>
      val question = if evaluation then Question.Evaluation(Set(program))
      else Question.Judgment(programInstruction, true)
      Point(
        s"point_$position",
        "test",
        familyName(position),
        BigDecimal(1),
        com.yang_bo.gezi.frontend.ExchangeText.line(programInstruction),
        question
      )
    )
    val families = points.groupBy(_.family).toVector.sortBy(_._1)
    val firstBudget = cap / families.headOption.fold(1)(_._2.size)
    val reader = Reader(
      "probe",
      SupervisorCommand.entryReaderClasspath(classes.toString),
      Launched.EntryLaunched(entryDirectory)
    )
    val limits =
      Limits(
        FamilyBudgets(20, cap, cap),
        60,
        graceSeconds,
        None,
        None,
        None,
        entryDirectory,
        "256m",
        None,
        Sandbox.Unconfined,
        ArticleDestination.Discarded,
        None
      )
    // Each family's published reference time is the cap over the multiple,
    // so that its budget is the cap.
    val anchor = BudgetAnchor.Published(
      families.map((family, _) => family -> cap / 20).toMap
    )
    val rows = Supervisor.pass(anchor, Vector(reader), families, limits)
    Files.writeString(
      entryDirectory.resolve("table.tsv"),
      (Supervisor.header +: rows.map(_.written)).mkString("", "\n", "\n")
    )
    val firstPoint = rows
      .find(_.point == "point_0")
      .getOrElse(throw AssertionError(s"no row of point_0 in $rows"))
    assert(
      firstPoint.wallSeconds < firstBudget + 0.5,
      s"the grace or more than its budget was charged to the first point: ${firstPoint.written}"
    )
    val files = Using
      .resource(Files.list(entryDirectory))(_.toList.asScala.toVector)
      .map(_.getFileName.toString)
      .sorted
    val events = files
      .filter(_.endsWith(".stderr"))
      .map(name =>
        val taken = Files
          .readAllLines(entryDirectory.resolve(name))
          .asScala
          .toVector
          .filter(_.startsWith("lifecycle "))
          .map(_.stripPrefix("lifecycle "))
        s"$name: ${taken.mkString(" ")}"
      )
    (rows.map(row =>
      s"${row.point} ${row.outcome} ${row.budgetExhausted} ${row.cancel.written} ${PipeLines.phasesField(row.phases)}"
    ) ++ events).mkString("\n")

  test(
    "a call that returns within the cancel's grace keeps its JVM; one that does not is killed"
  ) {
    assertSeededSnapshot(samples, 20261102L, 2, "judge/cancel.txt")(
      (behaviour, kinds) =>
        s"$behaviour: ${kinds.map(if _ then "evaluation" else "judgment").mkString(" ")}",
      identity[String]
    )(read(_, _, capSeconds, oneFamily = false))
  }

  /** Its purpose is to catch a supervisor that stops a family's remaining
    * points once one point is cancelled, or that gives the first point more
    * than its share: the two points are one family's, its budget `capSeconds`,
    * so the first point is cancelled at half of it, and the second is read with
    * its own budget, the rest of the family's: answered on the JVM the
    * honouring entry kept, cancelled in turn, after a setup of its own, for the
    * entry that ignores the cancel.
    */
  test(
    "a point cancelled at its budget leaves the family's next point its own budget"
  ) {
    assertSeededSnapshot(samples, 20261102L, 2, "judge/cancel-one-family.txt")(
      (behaviour, kinds) =>
        s"$behaviour: ${kinds.map(if _ then "evaluation" else "judgment").mkString(" ")}",
      identity[String]
    )(read(_, _, capSeconds, oneFamily = true))
  }

  /** Its purpose is to catch a supervisor that records a JVM ended by itself
    * (the kernel's OOM killer, say) as an ordinary stop: each point of the
    * probe that kills its own JVM must read stopped with the cancel `died:137`,
    * its budget not run out, after a setup of its own.
    */
  test(
    "a JVM killed by a signal during the reading of a point is recorded as died, with its exit status"
  ) {
    assertSeededSnapshot(
      Gen.element1(true, false).list(Range.singleton(2)),
      20261102L,
      1,
      "judge/died.txt"
    )(
      kinds =>
        s"die: ${kinds.map(if _ then "evaluation" else "judgment").mkString(" ")}",
      identity[String]
    )(read("die", _, diedCapSeconds, oneFamily = false))
  }
