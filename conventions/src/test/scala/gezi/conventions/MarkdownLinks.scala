package gezi.conventions

import java.net.URLDecoder
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.util.Locale
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*
import scala.util.Using
import scala.util.matching.Regex

/** The relative links of Gezi's Markdown files, read as GitHub renders them,
  * and the check that each one resolves inside Gezi: the file it names exists,
  * and the heading its anchor names exists when the file is Markdown. The
  * approach is that of `gezi.standardlibrary.ProofCitations`, which checks the
  * links of the library's proofs; this module depends on no other module of the
  * build, so it reads Markdown with functions of its own.
  *
  * A link is an inline link `[text](destination)` or an image
  * `![text](destination)`, its destination optionally followed by a title,
  * outside code: fenced code blocks, indented code blocks and code spans; a
  * bracket escaped as `\[` opens no link, so `D\[Z](x)` is text. A link whose
  * destination starts with `http:`, `https:` or `mailto:` is not checked.
  * Reference links (`[text][label]` with `[label]: destination`) are not read,
  * and neither are HTML tags.
  */
object MarkdownLinks:

  /** A link of a Markdown file: the line it stands on, counted from 1, and its
    * destination as written.
    */
  final case class Link(line: Int, destination: String)

  /** A link that does not resolve: the Markdown file, relative to the root that
    * was checked, the link, and why it does not resolve.
    */
  final case class BrokenLink(file: String, link: Link, reason: String)

  /** The anchor GitHub gives a heading's text (github-slugger, before
    * numbering): its inline links replaced by their text, in lower case, with
    * every character dropped that is no letter, mark, digit, connector
    * punctuation (such as `_`), space or hyphen, and each space written as a
    * hyphen. `` `zero_universe` `` gives `zero_universe`, and
    * `Building and testing` gives `building-and-testing`.
    */
  def anchor(heading: String): String =
    inlineLinkPattern
      .replaceAllIn(heading, found => Regex.quoteReplacement(found.group(2)))
      .toLowerCase(Locale.ROOT)
      .replaceAll("""[^\p{L}\p{M}\p{N}\p{Pc} \-]""", "")
      .replace(' ', '-')

  /** The anchors of the headings of a Markdown text, in order: the ATX headings
    * (one to six `#` and a space) outside code blocks. An anchor already given
    * is numbered as github-slugger numbers it: the second heading `A` gets
    * `a-1`, the third `a-2`, and a number that would repeat an anchor already
    * given counts on.
    */
  def headingAnchors(markdown: String): Vector[String] =
    val (_, anchors) = proseLines(markdown).foldLeft(
      (Map.empty[String, Int], Vector.empty[String])
    ) { case ((occurrences, done), (_, line)) =>
      line match
        case headingPattern(text) =>
          val base = anchor(text)
          val (numbered, counted) = numberedAnchor(base, occurrences)
          (counted.updated(numbered, 0), done :+ numbered)
        case _ => (occurrences, done)
    }
    anchors

  @tailrec
  private def numberedAnchor(
      base: String,
      occurrences: Map[String, Int]
  ): (String, Map[String, Int]) =
    occurrences.get(base) match
      case None        => (base, occurrences)
      case Some(count) =>
        val next = count + 1
        val candidate = s"$base-$next"
        val counted = occurrences.updated(base, next)
        if counted.contains(candidate) then numberedAnchor(base, counted)
        else (candidate, counted)

  /** The links of a Markdown text, in order, outside code (see the object's
    * documentation).
    */
  def links(markdown: String): Vector[Link] =
    proseLines(markdown).flatMap((lineNumber, line) =>
      linkPattern
        .findAllMatchIn(
          codeSpanPattern
            .replaceAllIn(line, found => " " * found.matched.length)
        )
        .toVector
        .map(found => Link(lineNumber, found.group(1)))
    )

  /** The destinations not checked: absolute URLs of these schemes. */
  def unchecked(destination: String): Boolean =
    Vector("http:", "https:", "mailto:").exists(destination.startsWith)

  /** The links of the Markdown file that do not resolve: a destination that
    * leaves the root or names no file or directory of it, resolved from the
    * file's directory, and an anchor into a Markdown file that is the anchor of
    * none of its headings (`headingAnchors`). A destination that is only an
    * anchor names the file itself. The destination's path and anchor are
    * percent-decoded first.
    */
  def brokenLinks(root: Path, file: Path): Vector[BrokenLink] =
    val normalizedRoot = root.toAbsolutePath.normalize
    val relativeFile =
      normalizedRoot.relativize(file.toAbsolutePath.normalize).toString
    links(Files.readString(file, StandardCharsets.UTF_8))
      .filterNot(link => unchecked(link.destination))
      .flatMap(link =>
        brokenReason(
          normalizedRoot,
          file.toAbsolutePath.normalize,
          link.destination
        )
          .map(reason => BrokenLink(relativeFile, link, reason))
      )

  private def brokenReason(
      root: Path,
      file: Path,
      destination: String
  ): Option[String] =
    val (writtenPath, writtenAnchor) = destination.indexOf('#') match
      case -1       => (destination, None)
      case position =>
        (
          destination.substring(0, position),
          Some(destination.substring(position + 1))
        )
    val path = percentDecoded(writtenPath)
    val target =
      if path.isEmpty then file else file.getParent.resolve(path).normalize
    if path.startsWith("/") then
      Some(
        s"the path $path is absolute; a link of gezi is relative to its file"
      )
    else if !target.startsWith(root) then
      Some(
        s"the path $path leaves gezi; a standalone checkout of gezi does not have it"
      )
    else if !Files.exists(target) then
      Some(s"the path $path names no file of gezi")
    else
      writtenAnchor
        .map(percentDecoded)
        .filter(_ =>
          target.toString.endsWith(".md") && Files.isRegularFile(target)
        )
        .filterNot(anchorWritten =>
          headingAnchors(Files.readString(target, StandardCharsets.UTF_8))
            .contains(anchorWritten)
        )
        .map(anchorWritten =>
          s"${root.relativize(target)} has no heading of the anchor $anchorWritten"
        )

  private def percentDecoded(text: String): String =
    if text.contains('%') then
      URLDecoder.decode(text.replace("+", "%2B"), StandardCharsets.UTF_8)
    else text

  /** The Markdown files under the root, sorted, in directories other than build
    * outputs (`target`), hidden directories (`.git`, Lean's `.lake`) and
    * `node_modules`.
    */
  def markdownFiles(root: Path): Vector[Path] =
    Using.resource(Files.list(root))(entries =>
      entries.toList.asScala.toVector
        .sortBy(_.getFileName.toString)
        .flatMap(entry =>
          val name = entry.getFileName.toString
          if Files.isDirectory(entry) then
            if name == "target" || name == "node_modules" || name
                .startsWith(".")
            then Vector.empty
            else markdownFiles(entry)
          else if name.endsWith(".md") then Vector(entry)
          else Vector.empty
        )
    )

  private val headingPattern: Regex =
    """ {0,3}#{1,6}[ \t]+(.+?)(?:[ \t]+#+)?[ \t]*""".r

  private val linkPattern: Regex =
    """(?<!\\)!?\[[^\]]*\]\(([^)\s]+)(?:\s+"[^"]*")?\)""".r

  private val inlineLinkPattern: Regex = """(!?)\[([^\]]*)\]\([^)]*\)""".r

  private val codeSpanPattern: Regex = """(`+).+?\1""".r

  private val listItemPattern: Regex = """\s*(?:[-*+]|\d+[.)])(?:\s.*)?""".r

  private val fencePattern: Regex = """\s*(`{3,}|~{3,}).*""".r

  /** Where a line stands: inside a fenced code block opened by the fence,
    * inside an indented code block, inside a list, and whether the line before
    * was blank.
    */
  private final case class BlockState(
      fence: Option[String],
      indentedCode: Boolean,
      list: Boolean,
      previousBlank: Boolean
  )

  /** The lines of the text outside code blocks, each with its number counted
    * from 1. A fenced code block opens at a line of three or more backticks or
    * tildes, however indented (an item of a list may hold one), and closes at a
    * line of at least as many of the same character. An indented code block is
    * a line indented by four spaces or a tab that follows a blank line or
    * another such line, outside a list: in a list, an indented line continues
    * an item. A list starts at a list item line and ends at a line that is not
    * indented and follows a blank line.
    */
  private def proseLines(markdown: String): Vector[(Int, String)] =
    val start = BlockState(
      fence = None,
      indentedCode = false,
      list = false,
      previousBlank = true
    )
    val (_, prose) = markdown
      .split("\n", -1)
      .toVector
      .zipWithIndex
      .foldLeft((start, Vector.empty[(Int, String)])) {
        case ((state, done), (line, index)) =>
          val blank = line.isBlank
          state.fence match
            case Some(fence) =>
              val closes =
                line.trim.startsWith(fence) && line.trim.forall(_ == fence.head)
              (
                state.copy(
                  fence = if closes then None else state.fence,
                  previousBlank = blank
                ),
                done
              )
            case None =>
              line match
                case fencePattern(fence) =>
                  (
                    state.copy(
                      fence = Some(fence),
                      indentedCode = false,
                      previousBlank = false
                    ),
                    done
                  )
                case _ =>
                  val indented =
                    line.startsWith("    ") || line.startsWith("\t")
                  val listItem = listItemPattern.matches(line)
                  val list =
                    if listItem then true
                    else if !blank && !indented && state.previousBlank then
                      false
                    else state.list
                  val indentedCode =
                    indented && !list && (state.indentedCode || state.previousBlank) ||
                      blank && state.indentedCode
                  val next = BlockState(None, indentedCode, list, blank)
                  if indentedCode || blank then (next, done)
                  else (next, done :+ (index + 1, line))
      }
    prose
