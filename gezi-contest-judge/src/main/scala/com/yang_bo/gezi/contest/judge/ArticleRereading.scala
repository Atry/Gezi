package com.yang_bo.gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path

/** The points whose articles are checked, the checks' table and the points'
  * manifests, checked after the scored pass on points it read.
  */
object ArticleRereading:

  /** The outcomes of an evaluation point that answered: success, false,
    * incomplete.
    */
  private val answeredOutcomes: Set[String] =
    Set(
      Outcome.Success.written,
      Outcome.False.written,
      Outcome.Incomplete.written
    )

  /** The points of the reader's rows to check, each with its family, in the
    * pass's order of families and of points within a family: every evaluation
    * point the reader answered falsely (`false`), and in each family one
    * evaluation point the reader answered, drawn from the article seed
    * (`SeededOrder.next`, one draw for every family, so that a family's draw
    * does not depend on another family's answers; the output's unsigned
    * remainder by the number of answered points picks one), each point once.
    */
  def selected(
      families: Vector[(String, Vector[Point])],
      rows: Vector[Row],
      articleSeed: Long
  ): Vector[(String, Point)] =
    val outcomeOf = rows
      .filter(_.point != "setup")
      .map(row => (row.family, row.point) -> row.outcome)
      .toMap
    def evaluation(point: Point) = point.question match
      case Question.Evaluation(_)  => true
      case Question.Judgment(_, _) => false
    val (chosen, _) =
      families.foldLeft((Vector.empty[(String, Point)], articleSeed)) {
        case ((gathered, state), (family, points)) =>
          val evaluations = points.filter(evaluation)
          val falsely = evaluations.filter(point =>
            outcomeOf.get((family, point.name)).contains(Outcome.False.written)
          )
          val answered = evaluations.filter(point =>
            outcomeOf
              .get((family, point.name))
              .exists(answeredOutcomes.contains)
          )
          val (after, output) = SeededOrder.next(state)
          val drawn = Option.when(answered.nonEmpty)(
            answered(
              java.lang.Long
                .remainderUnsigned(output, answered.size.toLong)
                .toInt
            )
          )
          val picked = points.filter(point =>
            falsely.contains(point) || drawn.contains(point)
          )
          (gathered ++ picked.map(family -> _), after)
      }
    chosen

  /** The directory of a point's re-read under the article root: the point's
    * name with every character but letters, digits and `_` written `-`, then
    * `-` and the point's position among the selected, so that two names written
    * alike get two directories.
    */
  def pointDirectory(articleRoot: Path, point: String, position: Int): Path =
    articleRoot.resolve(
      point.map(character =>
        if character.isLetterOrDigit || character == '_' then character else '-'
      ) + s"-$position"
    )

  /** The article check of each selected point of the reader (`selected`): the
    * re-read (`Supervisor.reread`) in a fresh directory under the article root,
    * `<point directory>/article` the article directory and the point directory
    * itself the log directory, within the reader's family budget times the
    * allowance, then `ArticleCheck`, and, once every point is checked, the
    * points' `ArticleManifest`s written in their point directories by
    * `manifestsWritten`, which the supervisor runs in a JVM of their own
    * (`ArticleManifests`); then the page under the article root, made here when
    * it does not exist yet (a pass that answered no point selects none), that
    * lists the points' trace pages, with the player's copy when its directory
    * is given (`TracePages.written`). The lines of `articles.tsv`: the article
    * seed and the allowance as comments, the header, a line for each point.
    * Throws `IllegalArgumentException` when the pass did not read the reader,
    * and `IllegalStateException` when a selected point has no answer of the
    * pass (the reader's rows were reused, `--reuse-table`, and hold no answer),
    * and, from `Files.createDirectory`, when a point's article directory exists
    * already: every re-read writes into a fresh one.
    */
  def table(
      reader: Reader,
      families: Vector[(String, Vector[Point])],
      read: PassRead,
      articleSeed: Long,
      allowance: Double,
      articleRoot: Path,
      manifestsWritten: Vector[(Point, ArticleOutcome, Path)] => Unit,
      limits: Limits,
      player: Option[Path]
  ): Vector[String] =
    val answers = read.answers.getOrElse(
      reader.name,
      throw IllegalArgumentException(
        s"the pass has no answers of ${reader.name}, so its articles are not checked"
      )
    )
    val budgets = read.budgets.getOrElse(
      reader.name,
      throw IllegalArgumentException(
        s"the pass has no budgets of ${reader.name}"
      )
    )
    val familyPoints = families.toMap
    Files.createDirectories(articleRoot)
    val rows = selected(
      families,
      read.rows.filter(_.reader == reader.name),
      articleSeed
    ).zipWithIndex.map { case ((family, point), position) =>
      val directory = pointDirectory(articleRoot, point.name, position + 1)
      val articleDirectory = directory.resolve("article")
      Files.createDirectories(directory)
      Files.createDirectory(articleDirectory)
      val reread = Supervisor.reread(
        reader,
        family,
        familyPoints(family),
        point,
        articleDirectory,
        budgets(family) * allowance,
        limits.copy(logDirectory = directory)
      )
      val scored = answers.getOrElse(
        point.name,
        throw IllegalStateException(s"no scored answer of ${point.name}")
      )
      val verdict = ArticleCheck.checked(articleDirectory, scored, reread)
      (
        ArticleCheck.row(point.name, reader.name, verdict),
        (point.name, directory),
        (point, verdict.outcome, directory)
      )
    }
    manifestsWritten(rows.map(_._3))
    TracePages.written(articleRoot, rows.map(_._2), player)
    Vector(
      s"# article-seed $articleSeed",
      s"# article-allowance $allowance",
      ArticleCheck.header
    ) ++ rows.map(_._1)

  /** The table's lines written to the file, one a line. */
  def written(file: Path, lines: Vector[String]): Unit =
    Files.writeString(
      file,
      lines.mkString("", "\n", "\n"),
      StandardCharsets.UTF_8
    )
