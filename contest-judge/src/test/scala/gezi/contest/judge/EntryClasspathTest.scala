package gezi.contest.judge

import java.nio.file.Files
import gezi.ir.Configured
import gezi.ir.NoFacts
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

/** The probe entry of `EntryClasspathTest`: its own provider, and its
  * entry in its companion, so that its class files are the whole entry. Its
  * setup loads, with `Class.forName`, each class named on a line of the file
  * `probed-class` of its directory; a class not on the JVM's classpath
  * throws `ClassNotFoundException`, which ends the JVM before its ready
  * line. It answers no cell.
  */
final class ClassProbe extends EntryProvider:

  def initial(entryDirectory: Path, cache: Cache, articles: ArticleDestination): Entry[?] =
    Files.readAllLines(entryDirectory.resolve("probed-class")).forEach(name => { Class.forName(name); () })
    ClassProbe.Unanswering(cache)

/** The probe's entry. */
object ClassProbe:

  /** The entry that answers no cell (it displays the Output unreduced),
    * holding the judge's cache service.
    */
  final case class Unanswering(cache: Cache) extends Entry[NoFacts.type]:

    def run(cell: gezi.frontend.DeBruijnTermOf[Configured[NoFacts.type]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[NoFacts.type] =
      Interaction.Finished(Cells.unreducedOutput(cell, Cells.initialState), Vector.empty, this)

/** An entry's JVM cannot load the problem corpora or the judge:
  * its purpose is to catch a
  * supervisor or a build that puts `contest-corpora` or `contest-judge` on an
  * entry's classpath, where an entry could reach the problem generators and
  * the judge's reference readers directly or by reflection.
  *
  * The supervisor starts the probe entry `ClassProbe` on the classpath it
  * builds for every entry (`SupervisorCommand.entryReaderClasspath`): the
  * runner's, then the entry's, here a directory holding the probe's class
  * file and its services file alone. The probe's `Class.forName` loads a
  * class of `contest-entry` and `contest-runner` (the setup is ready, so the probe
  * works) and fails on a class of `contest-corpora` and of `contest-judge` (the
  * setup fails with `ClassNotFoundException`). The framework's fixture
  * entry's classpath (`contest-entries-fixture`), as the supervisor builds
  * it, holds no directory of either project. And the probe loads, on that
  * classpath, the class of every framework native's static block method.
  * Every JVM runs in the sandbox (`Sandbox`), as an entry's does.
  */
class EntryClasspathTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of EntryClasspathTest, "the probe loads the classes of entry and entry-runner", takes 6.133 s; the bound is 1.5 times that rounded up to 5 s.
  // Reason: it starts a JVM to probe the entry classpath.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")


  private val buildRoot: Path = Paths.get(sys.props("gezi.buildRoot"))

  private val point =
    Point("identity", "test", "test", BigDecimal(1), gezi.frontend.ExchangeText.line(gezi.frontend.Defunctionalization.thunkInstruction(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))(using gezi.ir.NoFacts)), Question.Evaluation(Set.empty))

  private def probed(probedClass: String): Vector[Row] =
    val classes = ProbeEntries.classes(classOf[ClassProbe])
    val entryDirectory = Files.createTempDirectory("judge-classpath")
    Files.writeString(entryDirectory.resolve("probed-class"), probedClass)
    val reader = Reader("probe", SupervisorCommand.entryReaderClasspath(classes.toString), Launched.EntryLaunched(entryDirectory))
    val limits = Limits(FamilyBudgets(20, 60, 60), 60, 2, None, None, None, entryDirectory, "256m", None, TestSandbox.bubblewrap, ArticleDestination.Discarded, None)
    // The family's published reference time; the floor is the cap, so its
    // budget is the cap.
    Supervisor.pass(BudgetAnchor.Published(Map("test" -> 3.0)), Vector(reader), Vector(("test", Vector(point))), limits)

  test("the probe loads the classes of entry and entry-runner") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    Vector(classOf[Interaction].getName, classOf[gezi.contest.runner.PipeLines.Received].getName).foreach(probedClass =>
      assertEquals(probed(probedClass).map(row => (row.point, row.outcome)), Vector(("setup", "ready"), ("identity", "no_answer")))
    )
  }

  test("an entry's JVM loads the class of every framework native's static block method") {
    // The classes a group or narrow block resolves its natives' methods in
    // (`gezi.jit.StaticBlockMethod`), on the classpath the supervisor builds
    // for an entry's JVM: a class missing there would make a block's
    // compilation throw in the judged run only.
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    val classes = gezi.jit.NativeBackend.standard.natives.values.toVector
      .collect { case native if native.implementation.isInstanceOf[gezi.jit.StaticBlockMethod] =>
        native.implementation.asInstanceOf[gezi.jit.StaticBlockMethod].className
      }
      .distinct
      .sorted
    assert(classes.nonEmpty, "the framework has natives with static block methods")
    assertEquals(probed(classes.mkString("\n")).map(row => (row.point, row.outcome)), Vector(("setup", "ready"), ("identity", "no_answer")))
  }

  test("an entry's JVM cannot load a class of problem-corpora or of judge") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    Vector(classOf[gezi.contest.corpora.reductions.ReductionGroup].getName, classOf[Row].getName).foreach(probedClass =>
      val failure = intercept[SetupFailed](probed(probedClass))
      assert(failure.standardError.contains(s"java.lang.ClassNotFoundException: $probedClass"), failure.standardError)
    )
  }

  test("the fixture entry's classpath holds no directory of problem-corpora or judge") {
    val classpath = SupervisorCommand.entryReaderClasspath(sys.props("gezi.judge.entryClasspath.fixture"))
    val forbidden = Vector("problem-corpora", "judge").map(buildRoot.resolve(_))
    val found = classpath.split(java.io.File.pathSeparator).toVector.map(Paths.get(_)).filter(element => forbidden.exists(element.startsWith))
    assertEquals(found, Vector.empty)
  }
