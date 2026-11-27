package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import gezi.rewritetrace.TracePageText
import snapshot4s.generated.snapshotConfig
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The article check end to end: the supervisor reads the framework's fixture
  * entry (`contest-entries-fixture`), in the sandbox, on an evaluation point of
  * a small corpus family, then, from the article seed, re-reads one answered
  * point of each family in a new JVM, the point sent `articled` and the article
  * directory bound writable, and stores the articles the entry wrote
  * (`ArticleCheck`) with a manifest of each point (`ArticleManifest`), the
  * point's IR encoded against the entry's own knowledge
  * (`SupervisorCommand.entryKnowledgeLibrary`). The rows of `articles.tsv` are
  * a seeded snapshot, whatever their outcomes: the check is diagnostic, and an
  * outcome other than "文章已存" is a reading, not a failure. Its purpose is to
  * catch a broken link of the chain from the pipe line `articled` through
  * `Entry.articled`, the generic entry's articles and the writable binding to
  * the stored articles, and any change in how many articles the entry writes.
  *
  * A second test: the manifests of the checked points, their build replaced by
  * a placeholder, are a snapshot. Its purpose is to catch a point stored
  * without its manifest, a manifest whose articles are not the point's in
  * order, and any change of the writer's encoding of a point's IR, which a
  * verifier compares with the first article's left side.
  *
  * The point is generated as `SupervisorTest`'s are (`ProbedFamilies`): the
  * family's problems that tabling(weak_head) reads within the writer's budget,
  * ordered by the seed, the first. One point of one family is enough for both
  * purposes: each catches a defect in the chain or the manifest of any one
  * articled point, and each point re-read costs a JVM that compiles the entry's
  * library.
  */
class ArticleCheckTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of ArticleCheckTest, then reading the deleted baseline entry, takes 81.230 s; the bound is 1.5 times that rounded up to 5 s. On the fixture entry, 2026-11-17 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load about 10: 15.3 s.
  // Reason: it runs the judge end to end over real JVMs.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(125, "s")

  private val seed = 20261102L

  private val articleSeed = 7L

  /** The directory of the pass: the points, the table, `articles.tsv`, the
    * articles and their manifests.
    */
  private lazy val checked: Path =
    val directory = Files.createTempDirectory("article-check")
    val probed = ProbedFamilies.meanings
    val sources = probed.sourcesOf(probed.ordered(seed).take(1))
    val pointsDirectory = directory.resolve("points")
    assertEquals(
      PointsFile.written(pointsDirectory, sources, ProbedFamilies.writerBudget),
      Vector.empty
    )
    SupervisorCommand.run(
      Map(
        "entry" -> "fixture",
        "points" -> pointsDirectory.toString,
        "family-references" -> PublishedReferences
          .written(directory, Vector(probed.family))
          .toString,
        "seed" -> seed.toString,
        "setup-limit" -> "300",
        "budget-cap" -> "300",
        "slice" -> "none",
        "cores" -> "any",
        "article-seed" -> articleSeed.toString,
        "trace-player" -> player(directory).toString,
        "output" -> directory.resolve("table.tsv").toString
      )
    )
    directory

  /** A player's directory as the judge is given one: its script and the style
    * sheets a page links (`TracePageText.playerStyleSheets`), whose contents
    * the judge copies and never reads.
    */
  private def player(directory: Path): Path =
    val made = directory.resolve("player")
    (TracePageText.playerScript +: TracePageText.playerStyleSheets).foreach(
      path =>
        val file =
          made.resolve(path.stripPrefix(TracePageText.playerDirectory + "/"))
        Files.createDirectories(file.getParent)
        Files.writeString(file, s"/* $path */\n", StandardCharsets.UTF_8)
    )
    made

  test("the fixture entry's articles of the selected points are stored") {
    assume(
      TestSandbox.unavailable.isEmpty,
      TestSandbox.unavailable.getOrElse("")
    )
    val directory = checked
    assertFileSnapshot(
      Files
        .readString(directory.resolve("articles.tsv"), StandardCharsets.UTF_8),
      "judge/article_check.tsv"
    )
  }

  test(
    "each checked point's manifest names its point, its IR and its articles"
  ) {
    assume(
      TestSandbox.unavailable.isEmpty,
      TestSandbox.unavailable.getOrElse("")
    )
    val directory = checked
    val pointDirectories = Using
      .resource(Files.list(directory.resolve("articles")))(_.toScala(Vector))
      .filter(path =>
        Files.isDirectory(
          path
        ) && path.getFileName.toString != TracePageText.playerDirectory
      )
      .sorted
    // The build is the commit the test runs on, so the snapshot holds a
    // placeholder for it.
    val manifests = pointDirectories.map(pointDirectory =>
      Files
        .readString(
          pointDirectory.resolve(ArticleManifest.fileName),
          StandardCharsets.UTF_8
        )
        .split('\n')
        .toVector
        .map(line =>
          if line.startsWith("build\t") then "build\t<the judge's build>"
          else line
        )
        .mkString("", "\n", "\n")
    )
    assertFileSnapshot(manifests.mkString("\n"), "judge/article_manifests.txt")
  }

  /** The page that lists the trace pages (`TracePages`): every trace page of a
    * checked point is listed, every link of the page leads to a file, and every
    * listed page finds the player's script where it looks for it, beside
    * itself, through the link to the one copy. Its purpose is to catch a page
    * left out of the list, a link written relative to another directory than
    * the list's, and a page whose player does not resolve.
    */
  test(
    "the list of trace pages links every point's pages, each of which finds the player"
  ) {
    assume(
      TestSandbox.unavailable.isEmpty,
      TestSandbox.unavailable.getOrElse("")
    )
    val articles = checked.resolve("articles")
    val index = Files.readString(
      articles.resolve(TracePages.indexName),
      StandardCharsets.UTF_8
    )
    val linked =
      "href=\"([^\"]+)\"".r.findAllMatchIn(index).map(_.group(1)).toVector
    val pages = Using
      .resource(Files.walk(articles))(_.toScala(Vector))
      .filter(path =>
        path.getFileName.toString.endsWith(".trace.html") && !path.toString
          .contains(TracePageText.playerDirectory + "/")
      )
      .map(page => articles.relativize(page).toString)
      .sorted
    assert(pages.nonEmpty, s"no trace page under $articles")
    assertEquals(linked.filter(_.endsWith(".trace.html")).sorted, pages)
    assertEquals(
      linked.filterNot(link => Files.isRegularFile(articles.resolve(link))),
      Vector.empty[String]
    )
    assertEquals(
      pages.filterNot(page =>
        Files.isRegularFile(
          articles.resolve(page).resolveSibling(TracePageText.playerScript)
        )
      ),
      Vector.empty[String]
    )
  }
