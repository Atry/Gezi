package gezi.contest.judge

import java.io.BufferedReader
import java.io.InputStreamReader
import java.lang.ProcessBuilder.Redirect
import java.net.InetAddress
import java.net.ServerSocket
import java.net.Socket
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Cells
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.Interaction
import gezi.frontend.DeBruijnTerm
import gezi.hotspot.Cache
import gezi.saturation.StopSignal
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The probe entry of `SandboxTest`. Its setup does what the file `attempt`
  * of its directory says, a word and its operands separated by spaces:
  * `read <file>` reads the file; `write <file>` writes it; `connect <port>`
  * opens a TCP connection to the port of 127.0.0.1; `execute <program>
  * <arguments>...` starts the program and waits for it; `spin` does nothing,
  * and its entry then spins forever on every cell. An attempt that
  * fails throws, which ends the JVM before its ready line, the exception in
  * its standard error; one that succeeds leaves the setup ready. It answers
  * no cell.
  */
final class SandboxProbe extends EntryProvider:

  def initial(entryDirectory: Path, caches: Cache, articles: ArticleDestination): Entry =
    Files.readString(entryDirectory.resolve("attempt")).trim.split(' ').toVector match
      case Vector("read", file) =>
        Files.readString(Paths.get(file))
        SandboxProbe.Unanswering(caches)
      case Vector("write", file) =>
        Files.writeString(Paths.get(file), "written")
        SandboxProbe.Unanswering(caches)
      case Vector("connect", port) =>
        Using.resource(Socket(InetAddress.getLoopbackAddress, port.toInt))(_ => ())
        SandboxProbe.Unanswering(caches)
      case "execute" +: program =>
        ProcessBuilder(program.asJava).start().waitFor()
        SandboxProbe.Unanswering(caches)
      case Vector("spin") => SandboxProbe.Spinning(caches)
      case other          => throw IllegalArgumentException(s"no attempt $other")

/** The probe's entries, each holding the judge's cache service. */
object SandboxProbe:

  /** The entry that answers no cell: it displays the Output unreduced. */
  final case class Unanswering(cache: Cache) extends Entry:
    def run(cell: DeBruijnTerm, source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction =
      Interaction.Finished(Cells.unreducedOutput(cell, Cells.initialState), Vector.empty, this)

  /** The entry that spins forever on every cell. */
  final case class Spinning(cache: Cache) extends Entry:
    def run(cell: DeBruijnTerm, source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction = spun(0L)

  @tailrec
  private def spun(count: Long): Nothing = spun(count + 1)

/** An entry's JVM in the sandbox cannot read outside what it needs, write outside its private `/tmp`,
  * reach the network or start a process, and a kill on a family's budget
  * still ends it. Its purpose is to catch a sandbox that binds too much (a
  * parent of the judge's private directory, of another entry's directory,
  * or of the build's sources), that leaves the network or `execve` open, or
  * that outlives the supervisor's kill, so that a JVM still runs, and reads,
  * after its reading was recorded.
  *
  * The probe entry `SandboxProbe` makes one attempt per setup, in the
  * sandbox (`Sandbox.Bubblewrap`, the supervisor's default) and, as the
  * control that shows each attempt works, outside it (`Sandbox.Unconfined`,
  * `--sandbox none`): reading a file of a directory beside the entry's,
  * standing in for the judge's private directory and another entry's;
  * reading the build's `build.sbt`, which is on no classpath; writing into
  * the entry's directory; connecting to a port this test listens on at
  * 127.0.0.1; starting `true`; and starting the JDK's own `java`, a program
  * the sandbox binds (`true` is on no directory it binds). Both starts fail
  * on the execution filter's EPERM: `ProcessBuilder` first executes the
  * JDK's `jspawnhelper`, which the sandbox binds too. Each attempt fails in
  * the sandbox with its exception in the JVM's standard error, and succeeds
  * outside it. Reading the standard library, which every entry compiles,
  * succeeds in the sandbox.
  */
class SandboxTest extends gezi.generatedinputs.FailFastSuite:
  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of SandboxTest, "outside the sandbox every attempt succeeds", takes 12.044 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it runs the judge sandbox, a real JVM per attempt (end to end).
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  private val buildRoot: Path = Paths.get(sys.props("gezi.buildRoot"))

  private val point =
    Point("identity", "test", "test", BigDecimal(1), gezi.frontend.Defunctionalization.thunkInstruction(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))), Question.Evaluation(Set.empty))

  /** A directory for one setup: `entry`, the probe entry's directory with
    * its file `attempt`; `private/points.tsv`, beside it; `logs`, the
    * supervisor's log directory.
    */
  private def directories(attempt: Path => String): (Path, Path) =
    val root = Files.createTempDirectory("judge-sandbox")
    val entryDirectory = Files.createDirectories(root.resolve("entry"))
    Files.createDirectories(root.resolve("private"))
    Files.writeString(root.resolve("private").resolve("points.tsv"), "hidden\n")
    Files.createDirectories(root.resolve("logs"))
    Files.writeString(entryDirectory.resolve("attempt"), attempt(root))
    (root, entryDirectory)

  private def reader(entryDirectory: Path): Reader =
    Reader("probe", SupervisorCommand.entryReaderClasspath(ProbeEntries.classes(classOf[SandboxProbe]).toString), Launched.EntryLaunched(entryDirectory))

  /** The published reference time of the family `test`; the floor of
    * `limits` is its cap, so the family's budget is the cap.
    */
  private val anchor = BudgetAnchor.Published(Map("test" -> 3.0))

  private def limits(root: Path, sandbox: Sandbox, capSeconds: Double): Limits =
    Limits(FamilyBudgets(20, capSeconds, capSeconds), 60, 2, None, None, None, root.resolve("logs"), "256m", None, sandbox, ArticleDestination.Discarded, None)

  private def attempted(attempt: Path => String, sandbox: Sandbox): Vector[Row] =
    val (root, entryDirectory) = directories(attempt)
    Supervisor.pass(anchor, Vector(reader(entryDirectory)), Vector(("test", Vector(point))), limits(root, sandbox, 60))

  /** Each attempt, its name and the text its exception shows in the
    * sandboxed JVM's standard error.
    */
  private def attempts(port: Int): Vector[(String, Path => String, String)] =
    val java = Paths.get(System.getProperty("java.home"), "bin", "java")
    Vector(
      ("read a file beside the entry's directory", root => s"read ${root.resolve("private").resolve("points.tsv")}", "java.nio.file.NoSuchFileException"),
      ("read the build's build.sbt", _ => s"read ${buildRoot.resolve("build.sbt")}", "java.nio.file.NoSuchFileException"),
      ("write into the entry's directory", root => s"write ${root.resolve("entry").resolve("written")}", "Read-only file system"),
      ("connect to 127.0.0.1", _ => s"connect $port", "java.net.ConnectException: Connection refused"),
      ("start true", _ => "execute true", "Operation not permitted"),
      ("start the JDK's java", _ => s"execute $java -version", "Operation not permitted")
    )

  private def listening[A](body: Int => A): A =
    Using.resource(ServerSocket(0, 50, InetAddress.getLoopbackAddress))(server => body(server.getLocalPort))

  test("outside the sandbox every attempt succeeds") {
    listening(port =>
      attempts(port).foreach((name, attempt, _) =>
        assertEquals(attempted(attempt, Sandbox.Unconfined).map(row => (row.point, row.outcome)), Vector(("setup", "ready"), ("identity", "no_answer")), name)
      )
    )
  }

  test("in the sandbox every attempt fails") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    listening(port =>
      attempts(port).foreach((name, attempt, shown) =>
        val failure = intercept[SetupFailed](attempted(attempt, TestSandbox.bubblewrap))
        assert(failure.standardError.contains(shown), s"$name: ${failure.standardError}")
      )
    )
  }

  test("in the sandbox the standard library is readable") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    val library = buildRoot.resolve("corpora").resolve("compiler").resolve("binary_prolog_backend.lambdalattice")
    assertEquals(
      attempted(_ => s"read $library", TestSandbox.bubblewrap).map(row => (row.point, row.outcome)),
      Vector(("setup", "ready"), ("identity", "no_answer"))
    )
  }

  test("a family's budget running out kills the sandboxed JVM") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    val (root, entryDirectory) = directories(_ => "spin")
    val rows = Supervisor.pass(anchor, Vector(reader(entryDirectory)), Vector(("test", Vector(point))), limits(root, TestSandbox.bubblewrap, 1))
    assertEquals(rows.map(row => (row.point, row.outcome, row.budgetExhausted)), Vector(("setup", "ready", false), ("identity", "stopped", true)))
    assert(vanished(entryDirectory.toString, System.nanoTime + 10000000000L), s"a process of $entryDirectory still runs")
  }

  test("killing the sandbox's process, as the supervisor does, ends the JVM it started") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    val (root, entryDirectory) = directories(_ => "spin")
    val process = ProcessBuilder(Supervisor.command(reader(entryDirectory), limits(root, TestSandbox.bubblewrap, 1)).asJava)
      .redirectError(Redirect.to(root.resolve("logs").resolve("probe.stderr").toFile))
      .start()
    val ready = BufferedReader(InputStreamReader(process.getInputStream, StandardCharsets.UTF_8)).readLine()
    assertEquals(ready, "ready")
    val sandboxed = running(entryDirectory.toString)
    process.destroyForcibly()
    process.waitFor()
    assert(sandboxed.exists(_.contains("gezi.contest.runner.contestEntryRunner")), s"no JVM of $entryDirectory found running: $sandboxed")
    assert(vanished(entryDirectory.toString, System.nanoTime + 10000000000L), s"a process of $entryDirectory still runs")
  }

  /** The command lines of the running processes that mention the marker. */
  private def running(marker: String): Vector[String] =
    ProcessHandle.allProcesses().toList.asScala.toVector.flatMap(process => wholeCommandLine(process.pid)).filter(_.contains(marker))

  /** The whole command line of the process, its arguments joined by spaces,
    * read from `/proc/<pid>/cmdline`. `ProcessHandle.Info.commandLine()`
    * reads only the first 4096 bytes of that file and returns the line cut
    * there (JDK 25, measured 2026-11-03), and an entry's JVM writes the entry
    * directory after its `-cp`, whose length grows with the build root's
    * path. None when the process ended between the listing and the read, a
    * race every scan of running processes has.
    */
  private def wholeCommandLine(pid: Long): Option[String] =
    try Some(String(Files.readAllBytes(Paths.get("/proc", pid.toString, "cmdline")), StandardCharsets.UTF_8).replace('\u0000', ' '))
    catch case _: java.nio.file.NoSuchFileException => None

  /** Whether no running process mentions the marker before the deadline (of
    * `System.nanoTime`), looking every 50 milliseconds.
    */
  @tailrec
  private def vanished(marker: String, deadline: Long): Boolean =
    if running(marker).isEmpty then true
    else if System.nanoTime >= deadline then false
    else
      Thread.sleep(50)
      vanished(marker, deadline)
