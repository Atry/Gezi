package com.yang_bo.gezi.standardlibrary

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
import java.util.Locale

/** The check that the Markdown link of every `md` proof of a library resolves
  * in the repository (`citationsChecked`), and the anchors of Markdown headings
  * it resolves against. The knowledge reader does not call it: the contest
  * compiles the library in a sandbox where only the JDK and the knowledge roots
  * are readable, and the reader knows the knowledge roots, not the repository.
  * A library test calls it on every knowledge file and fixture, and
  * `LeanStatements`, which has the repository's root, on the lemmas it exports.
  * A `munit` proof is checked by the suite it names when that runs, and a `tex`
  * proof is not checked.
  */
object ProofCitations:

  /** The parts of a Markdown link `[text](path)` or `[text](path#anchor)`. */
  final case class MarkdownLink(
      text: String,
      path: String,
      anchor: Option[String]
  )

  private val linkPattern = """\[([^\]]+)\]\(([^)#\s]+)(?:#([^)\s]+))?\)""".r

  private val headingPattern = """#{1,6}[ \t]+(.+?)(?:[ \t]+#+)?[ \t]*""".r

  /** The parts of the text when it is exactly one Markdown link; none
    * otherwise.
    */
  def markdownLink(link: String): Option[MarkdownLink] = link match
    case linkPattern(text, path, anchor) =>
      Some(MarkdownLink(text, path, Option(anchor)))
    case _ => None

  /** The anchor GitHub gives a heading of the text: in lower case, with every
    * character dropped that is no letter, mark, digit, connector punctuation
    * (such as `_`), space or hyphen, and each space written as a hyphen.
    * `` `zero_universe` `` gives `zero_universe` and `16.13 折叠沿类型的右脊汇合（28）`
    * gives `1613-折叠沿类型的右脊汇合28`.
    */
  def anchor(heading: String): String =
    heading
      .toLowerCase(Locale.ROOT)
      .replaceAll("""[^\p{L}\p{M}\p{N}\p{Pc} \-]""", "")
      .replace(' ', '-')

  /** The headings of a Markdown text, each with its anchor, in order: the ATX
    * headings (one to six `#` and a space), outside fenced code blocks. A
    * repeated anchor is followed by `-1`, `-2`, … , as GitHub numbers it.
    */
  def headings(markdown: String): Vector[(String, String)] =
    val (_, found) = markdown
      .split("\n", -1)
      .toVector
      .foldLeft((false, Vector.empty[String])) { case ((fenced, done), line) =>
        if line.trim.startsWith("```") || line.trim.startsWith("~~~") then
          (!fenced, done)
        else if fenced then (fenced, done)
        else
          line match
            case headingPattern(text) => (fenced, done :+ text)
            case _                    => (fenced, done)
      }
    val (_, anchored) =
      found.foldLeft((Map.empty[String, Int], Vector.empty[(String, String)])) {
        case ((seen, done), text) =>
          val base = anchor(text)
          val numbered = seen.get(base).fold(base)(count => s"$base-$count")
          (
            seen.updated(base, seen.getOrElse(base, 0) + 1),
            done :+ (text -> numbered)
          )
      }
    anchored

  /** Checks the Markdown link of every `md` proof, by lemma name, against the
    * repository's root: the link is one Markdown link, its path names a file
    * inside the repository, and its anchor, when it has one, is the anchor of a
    * heading of that file (`headings`). Throws `StandardLibraryMalformed` with
    * `BrokenCitation` for the first lemma, in the order of the names, whose
    * link does not resolve.
    */
  def citationsChecked(
      proofs: Map[String, LemmaProof],
      repository: Path
  ): Unit =
    val root = repository.toAbsolutePath.normalize
    proofs.toVector.sortBy(_._1).foreach {
      case (lemma, LemmaProof.Markdown(link)) => linkChecked(lemma, link, root)
      case _                                  => ()
    }

  private def linkChecked(lemma: String, link: String, root: Path): Unit =
    def broken(reason: String): Nothing =
      throw StandardLibraryMalformed(
        MalformedReason.BrokenCitation(lemma, link, reason)
      )
    val MarkdownLink(_, path, anchorFound) = markdownLink(link).getOrElse(
      broken("it is no Markdown link [text](path#anchor)")
    )
    val file = root.resolve(path).normalize
    if !file.startsWith(root) || path.startsWith("/") then
      broken(s"the path $path is outside the repository")
    if !Files.isRegularFile(file) then
      broken(s"the path $path names no file of the repository")
    anchorFound.foreach(anchorWritten =>
      if !headings(Files.readString(file, StandardCharsets.UTF_8))
          .exists(_._2 == anchorWritten)
      then broken(s"$path has no heading of the anchor $anchorWritten")
    )
