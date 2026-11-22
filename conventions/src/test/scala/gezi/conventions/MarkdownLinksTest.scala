package gezi.conventions

import gezi.generatedinputs.SeededSnapshots
import hedgehog.Gen
import hedgehog.Range
import snapshot4s.generated.snapshotConfig

/** The rule that every relative link of Gezi's Markdown files resolves inside
  * Gezi, the anchor of a link into a Markdown file included
  * (`MarkdownLinks.brokenLinks`), so that a renamed file, a moved or reworded
  * section and a link out of Gezi, which a standalone checkout of Gezi lacks,
  * fail here and not in a reader's browser.
  */
class MarkdownLinksTest extends gezi.generatedinputs.FailFastSuite with SeededSnapshots:

  /** The broken links known and not yet fixed, each its file relative to
    * Gezi's root and its destination as written. A link here is not reported;
    * an entry that no longer matches a broken link fails the suite, so that
    * the list only shrinks.
    */
  private val knownExceptions: Vector[(String, String)] = Vector.empty

  private val headingWords: Gen[String] = Gen.element1(
    "Building",
    "and",
    "testing",
    "`zero_universe`",
    "16.13",
    "折叠沿类型的右脊汇合（28）",
    "C++",
    "a",
    "A",
    "under_score",
    "hyphen-ated",
    "[linked](elsewhere.md)",
    "*emphasis*"
  )

  private val destinations: Gen[String] = Gen.element1(
    "CONTRIBUTING.md",
    "CONTRIBUTING.md#building-and-testing",
    "#a",
    "../outside.md",
    "https://example.org/page",
    "doc/proofs/x.md#a-1"
  )

  private val line: Gen[String] = Gen.choice1(
    for
      level <- Gen.int(Range.linear(1, 6))
      words <- headingWords.list(Range.linear(1, 4))
    yield s"${"#" * level} ${words.mkString(" ")}",
    destinations.map(destination => s"see [text]($destination) here"),
    destinations.map(destination => s"""a [titled]($destination "title") link"""),
    destinations.map(destination => s"![image]($destination)"),
    destinations.map(destination => s"a code span `[text]($destination)` is no link"),
    destinations.map(destination => s"an escaped bracket D\\[Z]($destination) opens no link"),
    destinations.map(destination => s"    [indented]($destination)"),
    destinations.map(destination => s"- [listed]($destination)"),
    Gen.element1("```", "~~~", "", "plain prose")
  )

  private val document: Gen[String] = line.list(Range.linear(1, 12)).map(_.mkString("\n"))

  /** Its purpose is to catch a wrong anchor (GitHub's slug: lower case,
    * punctuation dropped but for `-` and `_`, spaces as hyphens, repeated
    * anchors numbered) and a link read inside code or missed outside it.
    */
  test("the anchors of a Markdown text's headings and its links, outside code") {
    assertSeededSnapshot(document, 20261121L, 40, "markdown-links/anchors-and-links.txt")(
      identity[String],
      identity[String]
    )(markdown =>
      (MarkdownLinks.headingAnchors(markdown).map(anchor => s"anchor $anchor") ++
        MarkdownLinks.links(markdown).map(link => s"link ${link.line}: ${link.destination}")).mkString("\n")
    )
  }

  private val repeatedHeadings: Gen[String] =
    Gen
      .element1("# A", "## a", "# a-1", "# [linked](elsewhere.md)", "# linked", "# B")
      .list(Range.linear(1, 6))
      .map(_.mkString("\n"))

  /** Its purpose is to catch a repeated heading numbered unlike GitHub's
    * github-slugger: the second `A` is `a-1`, and a heading whose anchor is
    * already `a-1` makes the next repeat count on to `a-2`.
    */
  test("repeated headings are numbered as GitHub numbers them") {
    assertSeededSnapshot(repeatedHeadings, 20261121L, 20, "markdown-links/numbered-anchors.txt")(
      identity[String],
      identity[String]
    )(markdown => MarkdownLinks.headingAnchors(markdown).mkString(" "))
  }

  private lazy val brokenLinks: Vector[MarkdownLinks.BrokenLink] =
    val root = ScalaSources.root
    MarkdownLinks.markdownFiles(root).flatMap(MarkdownLinks.brokenLinks(root, _))

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => brokenLinks)

  /** Its purpose is to catch a link of Gezi's Markdown files that names a
    * file Gezi lacks or a heading its file lacks, or that leaves Gezi.
    */
  test("every relative link of every Markdown file of gezi resolves inside gezi") {
    val reported = brokenLinks
      .filterNot(broken => knownExceptions.contains((broken.file, broken.link.destination)))
      .map(broken => s"${broken.file}:${broken.link.line}: ${broken.link.destination}: ${broken.reason}")
    assert(reported.isEmpty, reported.mkString("\n"))
  }

  /** Its purpose is to catch a known exception left on the list after its
    * link was fixed, which would let the link break again unnoticed.
    */
  test("every known exception is a broken link still") {
    val stale = knownExceptions.filterNot((file, destination) =>
      brokenLinks.exists(broken => broken.file == file && broken.link.destination == destination)
    )
    assert(stale.isEmpty, stale.map((file, destination) => s"$file: $destination resolves now").mkString("\n"))
  }
