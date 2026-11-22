package gezi.migration

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Lambdalattice
import gezi.frontend.Lexeme
import gezi.frontend.SyntaxSpans
import gezi.locations.Span
import scala.annotation.tailrec
import scala.jdk.StreamConverters.*
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The migration of a lambdalattice text written for the reader before
  * `+` and `∥` became left associative to the reader after, keeping the
  * term: every chain of `+` has its operands
  * written in the reverse order, so that the text reads to the term it read
  * to before.
  *
  * The reader before read a chain `t1 + t2 + t3` as the right-nested
  * `t1 + (t2 + t3)`, its operands in their order, and refused a chain that
  * mixes + and ∥. The reader after takes a `+`'s operand after it as the
  * choice's left side and the chain before it as its right side, the two
  * operands' roles swapped, so that `t3 + t2 + t1` is `t1 + (t2 + t3)`. A
  * chain in parentheses is an operand of its own under both readers and has
  * its own operands reversed.
  *
  * The operands move with their comments, and the layout and the `+` tokens
  * stay where they are, so a chain laid out one operand per line stays so.
  * A comment at the end of an operand's last line moves with the operand.
  * The lines of comments right above an operand's line move with it too, as
  * the comment of the operand below them, when every operand of the chain
  * starts a line (after its `+`, or, for the first, after at most one `(`)
  * and the lines moved stay inside the operand of every enclosing chain that
  * holds the chain; otherwise those lines stay in place. A comment over a
  * group of operands (`# ---- … ----`) moves with the group's first operand,
  * which the reversal puts last in the group: such headers are moved by hand.
  * Positions are in code points, as `gezi.locations.Span` says.
  */
object ChoiceOperandsReversal:

  /** The text of the file migrated, read in the scope of its own place in
    * its tree (`DirectoryTree.scope`). Throws as `reversed` of a text does.
    */
  def reversed(file: Path): String =
    reversed(DirectoryTree.scope(file.toAbsolutePath.normalize), Files.readString(file))

  /** The text migrated, read in the scope of the enclosing names. Throws the
    * reader's errors when the text does not read in that scope,
    * `IllegalArgumentException` when the text mixes + and ∥ in one chain,
    * which the reader before refused, and `IllegalStateException` when the
    * migrated text does not read to the term the reader before gave the
    * text, a defect of the migration.
    */
  def reversed(enclosing: Vector[String], text: String): String =
    val (term, spans) = Lambdalattice.locatedInScope(enclosing, text)
    val codePoints = text.codePoints.toScala(Vector)
    val layout = Layout(codePoints, classes(Lambdalattice.lexemes(text)))
    val found = chains(List((term, spans)), Vector.empty).map(layout.moved)
    val migrated = found
      .map(chain => if found.forall(_.admits(chain)) then chain else chain.withCommentsKept)
      .sortBy(chain => chain.region.end - chain.region.start)
      .foldLeft(codePoints)((current, chain) => chain.reversedIn(current))
    val migratedText = migrated.map(Character.toString).mkString
    val before = earlierReading(term, spans).result
    if Lambdalattice.locatedInScope(enclosing, migratedText)._1 != before then
      throw IllegalStateException(s"the migrated text reads to another term than the text did before step 1a:\n$migratedText")
    migratedText

  /** What a code point of the text is part of. */
  private enum Written:
    case Space, Comment, Token

  /** What each code point of the text is part of, by the pieces of the text
    * in order.
    */
  private def classes(lexemes: Vector[Lexeme]): Vector[Written] =
    lexemes.flatMap(lexeme =>
      val kind = lexeme match
        case Lexeme.Space(_)    => Written.Space
        case Lexeme.Comment(_)  => Written.Comment
        case Lexeme.Token(_, _) => Written.Token
      Vector.fill(lexeme.written.codePointCount(0, lexeme.written.length))(kind)
    )

  private val lineFeed: Int = '\n'.toInt

  /** The text's code points and what each is part of. */
  private final case class Layout(codePoints: Vector[Int], kinds: Vector[Written]):

    def lineStart(position: Int): Int = codePoints.lastIndexWhere(_ == lineFeed, position - 1) + 1

    def lineEnd(position: Int): Int =
      val found = codePoints.indexWhere(_ == lineFeed, position)
      if found < 0 then codePoints.size else found

    /** Whether the code points from start to end are white space and at least one comment. */
    private def onlyComments(start: Int, end: Int): Boolean =
      val inside = kinds.slice(start, end)
      inside.forall(_ != Written.Token) && inside.contains(Written.Comment)

    /** The end of the operand with the comment at the end of its last line. */
    def withTrailingComment(end: Int): Int =
      val lineFinish = lineEnd(end)
      if onlyComments(end, lineFinish) then lineFinish else end

    /** The lines of comments right above the line of the anchor, when the
      * line before the anchor is what the anchor may follow; none when it is
      * not.
      */
    def commentLinesAbove(anchor: Int, mayFollow: Vector[Int] => Boolean): Option[Span] =
      val start = lineStart(anchor)
      @tailrec
      def top(current: Int): Int =
        if current == 0 then current
        else
          val above = lineStart(current - 1)
          if onlyComments(above, current - 1) then top(above) else current
      Option.when(mayFollow(codePoints.slice(start, anchor)))(Span(top(start), start))

    /** The first token between the positions, the `+` of a gap. */
    def tokenBetween(start: Int, end: Int): Int =
      val found = kinds.indexWhere(_ == Written.Token, start)
      if found < 0 || found >= end then throw IllegalStateException(s"no + between $start and $end")
      found

    /** The chain of operands with the regions that move with each. */
    def moved(operands: Vector[Span]): MovedChain =
      val ends = operands.map(span => withTrailingComment(span.end))
      val anchors = operands.head.start +: operands.indices.tail.map(index => tokenBetween(ends(index - 1), operands(index).start)).toVector
      val blank: Vector[Int] => Boolean = _.forall(codePoint => Character.isWhitespace(codePoint))
      val firstMayFollow: Vector[Int] => Boolean = prefix =>
        blank(prefix.filter(_ != '('.toInt)) && prefix.count(_ == '('.toInt) <= 1
      val leads = anchors.zipWithIndex.map((anchor, index) => commentLinesAbove(anchor, if index == 0 then firstMayFollow else blank))
      MovedChain(
        operands.zip(ends).map((span, end) => Span(span.start, end)),
        Option.when(leads.forall(_.isDefined))(leads.flatten)
      )

  /** A chain's operands, each with the comment at the end of its last line,
    * and the lines of comments above each, when they move.
    */
  private final case class MovedChain(operands: Vector[Span], leads: Option[Vector[Span]]):

    /** From the first region that moves to the last. */
    def region: Span = Span(leads.fold(operands.head.start)(_.head.start), operands.last.end)

    def withCommentsKept: MovedChain = copy(leads = None)

    /** Whether the other chain's region, which may move, stays inside one
      * operand of this chain or out of this chain's region.
      */
    def admits(other: MovedChain): Boolean =
      val inner = other.region
      (other eq this) || !overlaps(region, inner) || contains(inner, region) ||
      operands.exists(operand => contains(operand, inner))

    private def overlaps(left: Span, right: Span): Boolean = left.start < right.end && right.start < left.end

    private def contains(outer: Span, inner: Span): Boolean = outer.start <= inner.start && inner.end <= outer.end

    /** The code points with the regions in the reverse order, each in the
      * place of another, the text between them kept.
      */
    def reversedIn(codePoints: Vector[Int]): Vector[Int] =
      val groups = leads.fold(Vector(operands))(found => Vector(found, operands))
      val replacements = groups.flatMap(regions => regions.zip(regions.reverse.map(span => codePoints.slice(span.start, span.end))))
      val (rebuilt, last) = replacements.sortBy(_._1.start).foldLeft((Vector.empty[Int], 0)) {
        case ((written, position), (span, content)) => (written ++ codePoints.slice(position, span.start) ++ content, span.end)
      }
      rebuilt ++ codePoints.drop(last)

  /** The span of a node with its parentheses, the outermost included. */
  private def extent(spans: SyntaxSpans): Span = spans.parentheses.lastOption.getOrElse(spans.span)

  /** Whether the node is a choice the text spells with no parentheses
    * around it: an operand before a `+` that continues a chain.
    */
  private def bareChoice(term: DeBruijnTerm, spans: SyntaxSpans): Boolean = (term, spans) match
    case (DeBruijnTerm.Choice(_, _), SyntaxSpans.Written(_, Vector(), _, _)) => true
    case _                                                                => false

  private def bareParallel(term: DeBruijnTerm, spans: SyntaxSpans): Boolean = (term, spans) match
    case (DeBruijnTerm.Parallel(_, _), SyntaxSpans.Written(_, Vector(), _, _)) => true
    case _                                                                  => false

  /** The operands of the chain of `+` whose last choice is the node, in the
    * text's order, each with its spans: the chain before each `+` is the
    * choice's right side, and continues while it is a bare choice. Throws
    * `IllegalArgumentException` for a ∥ continuing the chain.
    */
  private def chainOperands(term: DeBruijnTerm, spans: SyntaxSpans): Vector[(DeBruijnTerm, SyntaxSpans)] =
    @tailrec
    def collected(current: DeBruijnTerm, currentSpans: SyntaxSpans, after: List[(DeBruijnTerm, SyntaxSpans)])
        : Vector[(DeBruijnTerm, SyntaxSpans)] =
      current match
        case DeBruijnTerm.Choice(left, right) if (current eq term) || bareChoice(current, currentSpans) =>
          collected(right, currentSpans.child(1), (left, currentSpans.child(0)) :: after)
        case _ if bareParallel(current, currentSpans) =>
          throw IllegalArgumentException(s"a chain mixes + and ∥ at ${currentSpans.span}, which the reader before step 1a refused")
        case _ => ((current, currentSpans) :: after).toVector
    collected(term, spans, Nil)

  /** Whether the node is a chain of `+` written in the text: a choice whose
    * spans the text spells.
    */
  private def writtenChoice(term: DeBruijnTerm, spans: SyntaxSpans): Boolean = (term, spans) match
    case (DeBruijnTerm.Choice(_, _), SyntaxSpans.Written(_, _, _, _)) => true
    case _                                                        => false

  /** The children of the node with their spans. */
  private def children(term: DeBruijnTerm, spans: SyntaxSpans): List[(DeBruijnTerm, SyntaxSpans)] = term match
    case DeBruijnTerm.Lambda(body)              => List((body, spans.child(0)))
    case DeBruijnTerm.Apply(function, argument) => List((function, spans.child(0)), (argument, spans.child(1)))
    case DeBruijnTerm.Choice(left, right)       => List((left, spans.child(0)), (right, spans.child(1)))
    case DeBruijnTerm.Parallel(left, right)     =>
      if bareChoice(left, spans.child(0)) then
        throw IllegalArgumentException(s"a chain mixes + and ∥ at ${spans.span}, which the reader before step 1a refused")
      List((left, spans.child(0)), (right, spans.child(1)))
    case _ => Nil

  /** The spans of the operands of every chain of `+` written in the text,
    * each chain's in the text's order.
    */
  @tailrec
  private def chains(pending: List[(DeBruijnTerm, SyntaxSpans)], found: Vector[Vector[Span]]): Vector[Vector[Span]] =
    pending match
      case Nil => found
      case (term, spans) :: rest =>
        if writtenChoice(term, spans) then
          val operands = chainOperands(term, spans)
          chains(operands.toList ++ rest, found :+ operands.map((_, operandSpans) => extent(operandSpans)))
        else chains(children(term, spans) ++ rest, found)

  /** The term the reader before gave the text: each chain of `+`
    * written in the text nested to the right with its operands in the text's
    * order.
    */
  private def earlierReading(term: DeBruijnTerm, spans: SyntaxSpans): TailRec[DeBruijnTerm] =
    if writtenChoice(term, spans) then
      chainOperands(term, spans).reverse
        .foldLeft(None: Option[TailRec[DeBruijnTerm]]) {
          case (None, (operand, operandSpans)) => Some(tailcall(earlierReading(operand, operandSpans)))
          case (Some(rightSide), (operand, operandSpans)) =>
            Some(rightSide.flatMap(right => tailcall(earlierReading(operand, operandSpans)).map(DeBruijnTerm.Choice(_, right))))
        }
        .getOrElse(throw IllegalStateException("a chain of no operand"))
    else
      term match
        case DeBruijnTerm.Lambda(body) => tailcall(earlierReading(body, spans.child(0))).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(function, argument) =>
          tailcall(earlierReading(function, spans.child(0))).flatMap(readFunction =>
            tailcall(earlierReading(argument, spans.child(1))).map(DeBruijnTerm.Apply(readFunction, _))
          )
        case DeBruijnTerm.Choice(left, right) =>
          tailcall(earlierReading(left, spans.child(0))).flatMap(readLeft =>
            tailcall(earlierReading(right, spans.child(1))).map(DeBruijnTerm.Choice(readLeft, _))
          )
        case DeBruijnTerm.Parallel(left, right) =>
          tailcall(earlierReading(left, spans.child(0))).flatMap(readLeft =>
            tailcall(earlierReading(right, spans.child(1))).map(DeBruijnTerm.Parallel(readLeft, _))
          )
        case leaf => done(leaf)

  /** Each file under the directories (`LambdalatticeFormatting.files`)
    * migrated and written back when its text changes; returns the files
    * written.
    */
  def reversedInPlace(directories: Vector[Path]): Vector[Path] =
    LambdalatticeFormatting.files(directories).flatMap(file =>
      val written = reversed(file)
      if written == Files.readString(file) then None
      else
        val _ = Files.writeString(file, written)
        Some(file)
    )

/** Migrates the lambdalattice files under the directories in place
  * (`ChoiceOperandsReversal.reversedInPlace`) and prints the files written.
  */
@main def reverseChoiceOperands(directories: String*): Unit =
  ChoiceOperandsReversal.reversedInPlace(directories.toVector.map(Paths.get(_))).foreach(println)
