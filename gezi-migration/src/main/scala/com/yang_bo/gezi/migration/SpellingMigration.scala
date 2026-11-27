package com.yang_bo.gezi.migration

import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.LambdalatticeMalformed
import com.yang_bo.gezi.frontend.SyntaxSpans
import com.yang_bo.gezi.locations.Span
import scala.annotation.tailrec
import scala.jdk.StreamConverters.*

/** Migrations of a lambdalattice text's spelling that keep its term: the text
  * changes, the term it reads to does not, and every change is checked by
  * reading the text again. Positions are in code points, as
  * `com.yang_bo.gezi.locations.Span` says.
  */
object SpellingMigration:

  /** The text with each of the candidate pairs of parentheses removed whose
    * removal leaves the term the text reads to unchanged: the candidates tried
    * outermost first, then from left to right, each removal checked by reading
    * the text again and kept only when the term is the same; no other pair is
    * touched. A parenthesis between two characters of names is replaced by a
    * space, so that the names stay apart. Returns the text and the tracked
    * spans, moved by the removals. Throws the reader's errors when the text
    * given does not read, and `IllegalArgumentException` for a candidate that
    * is no pair of parentheses the reader reads.
    *
    * Each candidate tried reads the text once, so the cost is the number of
    * candidates times the text's length.
    */
  def parenthesesRemoved(
      text: String,
      candidates: Vector[Span],
      tracked: Vector[Span]
  ): (String, Vector[Span]) =
    parenthesesRemoved(Vector.empty, text, candidates, tracked)

  /** `parenthesesRemoved` of the text read in the scope of the enclosing names
    * (`Lambdalattice.locatedInScope`), as a file of a directory tree is read
    * under its directories' selves (`DirectoryTree.scope`): each removal is
    * checked by reading the text again in that scope. With no enclosing name,
    * the text is read closed. Throws as `parenthesesRemoved` does, and
    * `UnboundName` for a name that neither the text nor an enclosing name
    * binds.
    */
  def parenthesesRemoved(
      enclosing: Vector[String],
      text: String,
      candidates: Vector[Span],
      tracked: Vector[Span]
  ): (String, Vector[Span]) =
    val (term, spans) = Lambdalattice.locatedInScope(enclosing, text)
    val pairs = parentheses(spans).toSet
    require(
      candidates.forall(pairs.contains),
      s"a candidate of $candidates is no pair of parentheses of `$text`"
    )
    removed(
      enclosing,
      codePointsOf(text),
      term,
      candidates.distinct.sortBy(span => (span.start, -span.end)).toList,
      tracked
    )

  /** `parenthesesRemoved` with every pair of the text a candidate. */
  def parenthesesRemoved(text: String): String =
    parenthesesRemoved(Vector.empty, text)

  /** `parenthesesRemoved` in the scope of the enclosing names, with every pair
    * of the text a candidate.
    */
  def parenthesesRemoved(enclosing: Vector[String], text: String): String =
    parenthesesRemoved(
      enclosing,
      text,
      parentheses(Lambdalattice.locatedInScope(enclosing, text)._2),
      Vector.empty
    )._1

  /** The pairs of parentheses written in the text, outermost first, then from
    * left to right.
    */
  def parentheses(spans: SyntaxSpans): Vector[Span] =
    written(List(spans), Vector.empty).distinct.sortBy(span =>
      (span.start, -span.end)
    )

  @tailrec
  private def written(
      pending: List[SyntaxSpans],
      found: Vector[Span]
  ): Vector[Span] =
    pending match
      case Nil           => found
      case spans :: rest =>
        val below = spans match
          case SyntaxSpans.Written(_, _, children, _)  => children.toList
          case SyntaxSpans.Generated(_, _, written, _) =>
            written.map(_._2).toList
        written(below ++ rest, found ++ spans.parentheses)

  /** The candidates tried in order, at their positions in the current text,
    * each once.
    */
  @tailrec
  private def removed(
      enclosing: Vector[String],
      codePoints: Vector[Int],
      term: DeBruijnTerm,
      candidates: List[Span],
      tracked: Vector[Span]
  ): (String, Vector[Span]) =
    candidates match
      case Nil          => (textOf(codePoints), tracked)
      case pair :: rest =>
        val withoutPair = pairRemoved(codePoints, pair)
        if readTerm(enclosing, textOf(withoutPair)).contains(term) then
          def moved(span: Span): Span =
            Span(
              span.start - shift(codePoints, pair, span.start),
              span.end - shift(codePoints, pair, span.end)
            )
          removed(
            enclosing,
            withoutPair,
            term,
            rest.map(moved),
            tracked.map(moved)
          )
        else removed(enclosing, codePoints, term, rest, tracked)

  /** How far a position of the text moves left when the pair is removed: one
    * for each of its parentheses deleted before the position, none for one
    * replaced by a space.
    */
  private def shift(codePoints: Vector[Int], pair: Span, position: Int): Int =
    Vector(pair.start, pair.end - 1).count(at =>
      at < position && !betweenNames(codePoints, at)
    )

  private def pairRemoved(codePoints: Vector[Int], pair: Span): Vector[Int] =
    Vector(pair.end - 1, pair.start).foldLeft(codePoints)((current, at) =>
      if betweenNames(codePoints, at) then current.updated(at, ' '.toInt)
      else current.patch(at, Vector.empty, 1)
    )

  /** The parenthesis at the position stands between two characters of names,
    * which would read as one name without it.
    */
  private def betweenNames(codePoints: Vector[Int], at: Int): Boolean =
    def nameCharacter(position: Int): Boolean =
      codePoints
        .lift(position)
        .exists(codePoint =>
          Character.isLetterOrDigit(codePoint) || codePoint == '_'.toInt
        )
    nameCharacter(at - 1) && nameCharacter(at + 1)

  /** The term the text reads to in the scope of the enclosing names, or none
    * when it does not read: a removal may leave a text the grammar rejects,
    * which is a removal not to keep, as `ExchangeText` reads a line.
    */
  private def readTerm(
      enclosing: Vector[String],
      text: String
  ): Option[DeBruijnTerm] =
    try Some(Lambdalattice.locatedInScope(enclosing, text)._1)
    catch case LambdalatticeMalformed(_) => None

  private[migration] def codePointsOf(text: String): Vector[Int] =
    text.codePoints.toScala(Vector).map(_.toInt)

  private[migration] def textOf(codePoints: Vector[Int]): String =
    Span(0, codePoints.size).of(codePoints)
