package gezi.contest.judge

import java.nio.file.Files
import java.nio.file.LinkOption
import java.nio.file.Path
import gezi.ir.Instruction
import gezi.frontend.ExchangeText
import scala.annotation.tailrec

/** How the re-read of a point ended, the article check's first step: the family's budget, times the article allowance,
  * ran out before the point's answer; the JVM ended or wrote a line that is
  * not the point's answer; or it answered, the evaluation's answer given.
  */
enum Reread:
  case Exhausted
  case Stopped
  case Answered(answer: Option[Set[Instruction]])

/** The result of the article check of a point, as `articles.tsv` writes it
  * ([[ArticleCheck]]'s steps 1 and 2). Every result but
  * `ArticlesStored` stops the check at the step that found it.
  */
enum ArticleOutcome(val written: String):
  case NotReproducedBudget extends ArticleOutcome("没有重现（预算）")
  case NotReproducedStopped extends ArticleOutcome("没有重现（停止）")
  case AnswerChanged extends ArticleOutcome("记录改变了答案")
  case ArticlesMissing extends ArticleOutcome("文章缺失")
  case ArticlesStored extends ArticleOutcome("文章已存")

/** A point's article check: its result and the detail, a line of text with
  * no tab and no newline.
  */
final case class ArticleVerdict(outcome: ArticleOutcome, detail: String)

/** The judge's check of the OpenTheory articles an entry wrote for a point
  * in the re-read, in two steps:
  *
  *   1. the re-read: the budget ran out, or the JVM stopped, is "not
  *      reproduced"; an answer other than the scored pass's is "the
  *      recording changed the answer";
  *   2. the articles `round-1.art`, `round-2.art`, ... of the directory, up
  *      to the first number missing; none is "articles missing".
  *
  * Passing both is "articles stored", its detail the number of articles.
  * The judge reads no article and runs no proof checker: the articles are
  * evidence, stored for a verifier run on demand outside the judging: what
  * matters is that the exported evidence can be verified, not that every
  * pass verifies it.
  */
object ArticleCheck:

  /** The file of the article of the round, numbered from 1. */
  def articleFile(directory: Path, number: Int): Path = directory.resolve(s"round-$number.art")

  /** The verdict of the point's articles in the directory, the re-read's
    * ending and the answer of the scored pass (steps 1 and 2).
    */
  def checked(directory: Path, scored: Option[Set[Instruction]], reread: Reread): ArticleVerdict = reread match
    case Reread.Exhausted => ArticleVerdict(ArticleOutcome.NotReproducedBudget, "the family's budget times the allowance ran out")
    case Reread.Stopped   => ArticleVerdict(ArticleOutcome.NotReproducedStopped, "the JVM ended or wrote a line that is not the point's answer")
    case Reread.Answered(answer) if answer != scored =>
      ArticleVerdict(ArticleOutcome.AnswerChanged, s"scored ${answerText(scored)}, re-read ${answerText(answer)}")
    case Reread.Answered(_) =>
      val files = articleFiles(directory)
      if files.isEmpty then ArticleVerdict(ArticleOutcome.ArticlesMissing, s"no ${articleFile(directory, 1).getFileName}")
      else ArticleVerdict(ArticleOutcome.ArticlesStored, s"${files.size} 篇文章")

  /** The article files of the directory, `round-1.art` on, up to the first
    * one missing. A symbolic link is not an article: the entry wrote the
    * directory, and a link it planted would have a verifier read, as
    * evidence, a file of the judge's.
    */
  def articleFiles(directory: Path): Vector[Path] = articleFilesFrom(directory, 1, Vector.empty)

  @tailrec
  private def articleFilesFrom(directory: Path, number: Int, found: Vector[Path]): Vector[Path] =
    val file = articleFile(directory, number)
    if Files.isRegularFile(file, LinkOption.NOFOLLOW_LINKS) then articleFilesFrom(directory, number + 1, found :+ file) else found

  private def oneLine(text: String): String = text.map(character => if character == '\t' || character == '\n' then ' ' else character)

  private def answerText(answer: Option[Set[Instruction]]): String = answer match
    case None        => "no answer"
    case Some(found) => s"${found.size} normal forms ${found.toVector.map(ExchangeText.line).sorted.mkString(" ; ").take(200)}"

  /** The header of `articles.tsv`. */
  val header: String = "point\treader\toutcome\tdetail"

  /** The line of `articles.tsv` for the verdict of the reader on the point;
    * the detail's tabs and newlines are written as spaces.
    */
  def row(point: String, reader: String, verdict: ArticleVerdict): String =
    Vector(point, reader, verdict.outcome.written, oneLine(verdict.detail)).mkString("\t")
