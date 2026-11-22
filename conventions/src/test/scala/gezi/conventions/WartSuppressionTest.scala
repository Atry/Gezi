package gezi.conventions

/** The suppressions of WartRemover's warts, whether built in
  * (`org.wartremover.warts.<Name>`) or custom (`gezi.warts.<Name>`).
  *
  * Purpose: a suppression is an exception to the immutability rule, so each
  * one must carry the user's words that make it, either in a comment on its
  * line or on the line directly above. The words are recognised by their
  * attribution `(the user, <date>`.
  */
object WartSuppressionCheck:

  private val suppression = """@SuppressWarnings\(.*(org\.wartremover\.warts|gezi\.warts)\.""".r

  private val attribution = """the user, 20\d\d-\d\d-\d\d""".r

  /** The sources' suppressions that carry no attribution on their line or the
    * line above, each `path:number: text`.
    */
  def problems(sources: Vector[(String, String)]): Vector[String] =
    sources.flatMap((path, text) =>
      val lines = text.split('\n').toVector
      val code = ScalaSources.commentsBlanked(text).split('\n').toVector
      lines.zipWithIndex.collect {
        case (line, index)
            if suppression.findFirstIn(code(index)).isDefined &&
              attribution.findFirstIn(line).isEmpty &&
              (index == 0 || attribution.findFirstIn(lines(index - 1)).isEmpty) =>
          s"$path:${index + 1}: ${line.trim}"
      }
    )

class WartSuppressionTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  test("every WartRemover suppression in the Scala sources carries the user's words") {
    assert(ScalaSources.texts.nonEmpty, s"no Scala source found under ${ScalaSources.root}")
    val found = WartSuppressionCheck.problems(ScalaSources.texts)
    assert(found.isEmpty, found.mkString("\n"))
  }
