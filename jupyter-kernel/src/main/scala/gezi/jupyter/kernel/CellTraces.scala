package gezi.jupyter.kernel

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.Base64
import gezi.rewritetrace.TracePageText
import gezi.strategies.TraceFiles
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The traces a kernel shows in its cells' outputs, each in the trace player
  * inside the cell's output, when the kernel is started with
  * `--trace-directory`. The entry writes, under
  * `ArticleDestination.WrittenWithTraces`, the trace of every point it
  * extracts, `trace-<k>.lambdalattice` with its start, into a directory of this
  * kernel's own under the trace directory, made at the kernel's start, so that
  * a restarted kernel, whose traces count from 1 again, writes over no page an
  * older output shows (JupyterLab starts a kernel of its own when it opens a
  * notebook). After each cell, the kernel writes beside each trace the cell
  * wrote a page with the player in it (`notebookPage`,
  * `TracePageText.selfContainedPage`), and the cell's output shows each such
  * page in an iframe whose `src` is the page's path relative to the kernel's
  * working directory, the notebook's own when Jupyter starts the kernel:
  * JupyterLab (4.4.1) resolves the `src` of every element of an HTML output
  * against the notebook's directory to the server's URL of the file.
  *
  * The page holds its player rather than linking it because Jupyter Server
  * serves a file's HTML under the policy `sandbox allow-scripts`: the page's
  * origin is opaque, its requests carry no credentials, and a linked player was
  * answered by the login's redirect (measured 2026-11-19: the four requests of
  * a page's player each `302`, the page blank in the notebook). A page of 4.8
  * MB on disk for each trace is the cost; the notebook holds only the frame.
  * The frame is an iframe and not a widget of ipywidgets, which would need a
  * JupyterLab extension built with npm, and each page in its own frame keeps
  * the player's state in its own URL hash, which `history.replaceState` writes
  * in the sandbox as on any page (measured the same day).
  */
final case class CellTraces(
    directory: Path,
    workingDirectory: Path,
    player: CellTraces.Player
):

  /** The traces of the directory, by their number. */
  def traces(): Vector[Path] =
    Using
      .resource(Files.list(directory))(_.toScala(Vector))
      .flatMap(path =>
        CellTraces.traceNumber(path.getFileName.toString).map(_ -> path)
      )
      .sortBy(_._1)
      .map(_._2)

  /** Writes the page with the player of each trace, beside it
    * (`CellTraces.notebookPage`); the pages, in the traces' order.
    */
  def pagesWritten(written: Vector[Path]): Vector[Path] =
    written.map(trace =>
      val page = CellTraces.notebookPage(trace)
      Files.writeString(
        page,
        TracePageText.selfContainedPage(
          page.getFileName.toString,
          Files.readString(TraceFiles.startFile(trace), StandardCharsets.UTF_8),
          Files.readString(trace, StandardCharsets.UTF_8),
          player.script,
          player.styleSheets
        ),
        StandardCharsets.UTF_8
      )
      page
    )

  /** The HTML of a cell's output: its text, then a frame for each page, by its
    * path relative to the working directory.
    */
  def html(outputText: String, pages: Vector[Path]): String =
    CellTraces.html(
      outputText,
      pages.map(page =>
        workingDirectory
          .relativize(page.toAbsolutePath.normalize)
          .toString
          .replace('\\', '/')
      )
    )

object CellTraces:

  /** The player a page holds: its script and its style sheets, in the order a
    * page links them (`TracePageText.playerStyleSheets`), each file a style
    * sheet loads in it as a `data:` URL.
    */
  final case class Player(script: String, styleSheets: Vector[String])

  /** The resource directory of the player's files on the kernel's classpath, as
    * the kernel's build puts them (`jupyter-kernel/build.sbt`), at their paths
    * under `TracePageText.playerDirectory`.
    */
  val playerResources: String = "gezi/jupyter/kernel/trace-player"

  /** The player read from the classpath. Throws `IllegalStateException` for a
    * file of it, or a file a style sheet loads, that is not there.
    */
  def player(): Player =
    def path(linked: String): String =
      linked.stripPrefix(TracePageText.playerDirectory + "/")
    Player(
      String(
        resource(path(TracePageText.playerScript)),
        StandardCharsets.UTF_8
      ),
      TracePageText.playerStyleSheets.map(linked =>
        withDataUrls(
          path(linked),
          String(resource(path(linked)), StandardCharsets.UTF_8)
        )
      )
    )

  /** The style sheet at the path with every `url(...)` of a file, a path
    * relative to the sheet with any query or fragment dropped, replaced by a
    * `data:` URL of the file's bytes; a `data:` URL is kept.
    */
  def withDataUrls(sheetPath: String, sheet: String): String =
    """url\("?([^")?#]+)[^)]*\)""".r.replaceAllIn(
      sheet,
      found =>
        val target = found.group(1)
        if target.startsWith("data:") then
          scala.util.matching.Regex.quoteReplacement(found.matched)
        else
          val file = Paths
            .get(sheetPath)
            .resolveSibling(target)
            .normalize
            .toString
            .replace('\\', '/')
          val mediaType = file match
            case s"$_.woff2" => "font/woff2"
            case s"$_.woff"  => "font/woff"
            case other       =>
              throw IllegalStateException(
                s"the style sheet $sheetPath loads $other, of no known media type"
              )
          scala.util.matching.Regex.quoteReplacement(
            s"""url("data:$mediaType;base64,${Base64.getEncoder.encodeToString(
                resource(file)
              )}")"""
          )
    )

  /** The bytes of a file of the player on the classpath. */
  private def resource(path: String): Array[Byte] =
    val stream = Option(
      getClass.getClassLoader.getResourceAsStream(s"$playerResources/$path")
    )
      .getOrElse(
        throw IllegalStateException(
          s"the player's $path is not on the kernel's classpath under $playerResources"
        )
      )
    Using.resource(stream)(_.readAllBytes())

  /** The traces of a kernel started now, under the trace directory, made if
    * absent: a fresh directory for this kernel, and the player read once.
    */
  def started(traceDirectory: Path, workingDirectory: Path): CellTraces =
    Files.createDirectories(traceDirectory)
    CellTraces(
      Files.createTempDirectory(traceDirectory, "kernel-"),
      workingDirectory.toAbsolutePath.normalize,
      player()
    )

  /** The number of a trace the entry writes, `trace-<k>.lambdalattice`. */
  def traceNumber(name: String): Option[Int] = name match
    case s"trace-$number.lambdalattice" => number.toIntOption
    case _                              => None

  /** The page with the player of a trace file, beside it:
    * `trace-<k>.notebook.html`.
    */
  def notebookPage(trace: Path): Path =
    trace.resolveSibling(
      trace.getFileName.toString.stripSuffix(
        ".lambdalattice"
      ) + ".notebook.html"
    )

  /** The HTML of an output: the text in a `pre`, escaped, then a frame for each
    * page at its path. A path that holds a character HTML would read as markup
    * in an attribute is rejected by `IllegalArgumentException`.
    */
  def html(outputText: String, pages: Vector[String]): String =
    pages.foreach(page =>
      require(
        !page.exists("<>&\"".contains(_)),
        s"the page's path '$page' holds a character HTML reads as markup"
      )
    )
    val escaped = outputText.flatMap {
      case '<'   => "&lt;"
      case '>'   => "&gt;"
      case '&'   => "&amp;"
      case other => other.toString
    }
    (s"<pre>$escaped</pre>" +: pages.map(page =>
      s"""<iframe src="$page" title="$page" style="width: 100%; height: 36rem; border: 1px solid #dee2e6"></iframe>"""
    )).mkString("\n")
