package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.rewritetrace.TracePageText
import gezi.strategies.TraceFiles
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The page that lists the player's pages of the article check, at the top of
  * its directory, beside one page per point that lists its rounds: the generic
  * entry writes the trace of each article, its start and its page beside it
  * (`TraceFiles.textWrittenAt`, `round-<n>.trace.html`), and this page links to
  * every one, grouped by point. A page looks for the player at
  * `TracePageText.playerDirectory` beside it; given the player's directory (the
  * one the sbt task `trace-player/demonstrationPage` makes), one copy of it
  * goes to the top, beside this page, and each point's article directory gets a
  * relative symbolic link to that copy, so that every page opened from
  * `file://` plays.
  */
object TracePages:

  /** The name of the page under the article root. */
  val indexName: String = "index.html"

  /** The player's pages of the articles of a point's article directory, in the
    * articles' order (`ArticleCheck.articleFiles`).
    */
  def pages(articleDirectory: Path): Vector[Path] =
    ArticleCheck
      .articleFiles(articleDirectory)
      .map(article => TraceFiles.pageFile(TraceFiles.traceFile(article)))
      .filter(Files.isRegularFile(_))

  /** Writes the page under the article root, listing the pages of each point's
    * article directory (`<point directory>/article`), the points in the order
    * given and only those with a page; and, with the player's directory, its
    * copy beside the page and a link to the copy in each such article
    * directory. Throws `IllegalArgumentException` for a player's directory with
    * no `main.js`, and, from `Files`, when the copy or a link exists already:
    * every article check writes into a fresh root.
    */
  def written(
      articleRoot: Path,
      points: Vector[(String, Path)],
      player: Option[Path]
  ): Unit =
    val listed = points
      .map((name, directory) => (name, directory.resolve("article")))
      .map((name, articleDirectory) =>
        (name, articleDirectory, pages(articleDirectory))
      )
      .filter(_._3.nonEmpty)
    val groups = listed.map((name, _, found) =>
      (name, found.map(page => articleRoot.relativize(page).toString))
    )
    Files.writeString(
      articleRoot.resolve(indexName),
      TracePageText.indexPage("Traces of the article check", groups),
      StandardCharsets.UTF_8
    )
    player.foreach(source =>
      require(
        Files.isRegularFile(source.resolve("main.js")),
        s"the player's directory $source holds no main.js"
      )
      copied(source, articleRoot.resolve(TracePageText.playerDirectory))
      listed.foreach((_, articleDirectory, _) =>
        Files.createSymbolicLink(
          articleDirectory.resolve(TracePageText.playerDirectory),
          Paths.get("..", "..", TracePageText.playerDirectory)
        )
      )
    )

  /** Copies the directory, its files and directories, to the target, which does
    * not exist yet.
    */
  private def copied(source: Path, target: Path): Unit =
    Using
      .resource(Files.walk(source))(_.toScala(Vector))
      .foreach(path =>
        val destination = target.resolve(source.relativize(path).toString)
        if Files.isDirectory(path) then Files.createDirectories(destination)
        else Files.copy(path, destination)
      )
