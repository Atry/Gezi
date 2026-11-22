package gezi.contest.judge

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import scala.jdk.CollectionConverters.*

/** `--reuse-table` end to end, on a points file the writer puts the
  * first small problem of a corpus family in: a first run reads the
  * framework's fixture entry (`contest-entries-fixture`) and writes its
  * table; a second run given that table reads no entry JVM (its log
  * directory gets no standard error of the entry) and gives the same entry
  * rows; and two supervisors run at once, each reading tabling(weak_head) into its
  * own output, both finish with the reused entry rows. Its purpose is to
  * catch a reuse that reads the entry again, rows that differ from the
  * reused ones, and a path two concurrent supervisors collide on.
  */
class ReuseTableTest extends gezi.generatedinputs.FailFastSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of ReuseTableTest, then reading the deleted baseline entry, takes 37.962 s; the bound is 1.5 times that rounded up to 5 s. On the fixture entry, 2026-11-17 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load about 10: 10.2 s.
  // Reason: it runs two supervisors with real JVMs at once.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(60, "s")

  private val seed = 20261101L

  private val entry = "fixture"

  private def options(points: Path, output: Path, extra: (String, String)*): Map[String, String] =
    Map(
      "entry" -> entry,
      "points" -> points.toString,
      "family-references" -> PublishedReferences.written(points.getParent, Vector(ProbedFamilies.meanings.family)).toString,
      "seed" -> seed.toString,
      "setup-limit" -> "300",
      "budget-cap" -> "300",
      "slice" -> "none",
      "cores" -> "any",
      "sandbox" -> "none",
      "output" -> output.toString
    ) ++ extra

  private def standardErrors(directory: Path, reader: String): Vector[Path] =
    Files.list(directory).toList.asScala.toVector.filter(path =>
      path.getFileName.toString.startsWith(s"$reader-") && path.getFileName.toString.endsWith(".stderr")
    )

  test("a reused table reads no entry, and two supervisors run at once") {
    val directory = Files.createTempDirectory("reuse-table")
    // The family's first problem that tabling(weak_head) reads within the writer's
    // budget (`ProbedFamilies`): one point is enough to catch a reuse that
    // reads the entry again or rows that differ, and a larger one would
    // only slow the test.
    val sources = ProbedFamilies.meanings.writtenSources.take(1)
    val points = directory.resolve("points")
    assertEquals(PointsFile.written(points, sources, ProbedFamilies.writerBudget), Vector.empty)

    val first = directory.resolve("first").resolve("table.tsv")
    val firstRows = SupervisorCommand.run(options(points, first))
    assert(firstRows.exists(_.reader == entry))
    // The rows as the table wrote them, wall times to six decimals: the rows
    // a reuse reads back.
    val entryRows = TableFile.read(first).rows.filter(_.reader == entry)

    val second = directory.resolve("second").resolve("table.tsv")
    val secondRows = SupervisorCommand.run(options(points, second, "reuse-table" -> first.toString))
    assertEquals(secondRows.filter(_.reader == entry), entryRows)
    assertEquals(standardErrors(second.getParent, entry), Vector.empty)

    val concurrent = Vector("third", "fourth").map(name => directory.resolve(name).resolve("table.tsv"))
    val processes = concurrent.map(output =>
      val arguments = options(points, output, "reuse-table" -> first.toString, "references" -> "tabling(weak_head)")
        .toVector.flatMap((name, value) => Vector(s"--$name", value))
      val properties = sys.props.toVector.collect {
        case (name, value) if name.startsWith("gezi.") => s"-D$name=$value"
      }
      Files.createDirectories(output.getParent)
      ProcessBuilder(
        (Vector(Paths.get(System.getProperty("java.home"), "bin", "java").toString, "-Xmx256m") ++ properties ++
          Vector("-cp", System.getProperty("java.class.path"), "gezi.contest.judge.judgeSupervisor") ++ arguments).asJava
      ).redirectErrorStream(true).redirectOutput(output.getParent.resolve("supervisor.log").toFile).start()
    )
    val exits = processes.map(_.waitFor())
    assertEquals(exits, Vector(0, 0), concurrent.map(output => Files.readString(output.getParent.resolve("supervisor.log"))).mkString("\n"))
    concurrent.foreach(output =>
      val table = TableFile.read(output)
      assertEquals(table.rows.filter(_.reader == entry), entryRows)
      assert(table.rows.exists(_.reader == "tabling(weak_head)"))
      assertEquals(table.provenance.reused.map(_._1), Some(first.toString))
    )
  }
