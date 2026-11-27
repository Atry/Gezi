package com.yang_bo.gezi.migration

import com.yang_bo.gezi.ir.{Configured, NoFacts}
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import com.yang_bo.gezi.directorysugar.DirectoryTree
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.Lambdalattice
import com.yang_bo.gezi.frontend.Lexeme
import com.yang_bo.gezi.frontend.SourceFormatting
import com.yang_bo.gezi.frontend.SpelledBinder
import com.yang_bo.gezi.frontend.SyntaxSpans
import com.yang_bo.gezi.frontend.TokenKind
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.knowledgereading.KnowledgeReadingError
import com.yang_bo.gezi.knowledgereading.Reading
import com.yang_bo.gezi.locations.Span
import scala.annotation.tailrec
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The configuration of the terms here: no facts. */
private given exportBinderConversionNoFacts: NoFacts.type = NoFacts

/** The conversion of a lambdalattice file's export from a Scott tuple at the
  * end of the file's spine, `… λx tuple. tuple M1 … Mn`, to an abstraction of
  * the whole file, `λexport. … λx. export M1 … Mn` (`CONTRIBUTING.md`,
  * "lambdalattice files export through their first binder `export`"), for every
  * existing file.
  *
  * The old content is C[λt. t M1 … Mn], C the spine of imports and local
  * definitions; the new content is λe. C[e M1 … Mn]. Applied to an importer's
  * continuation k, the new content is C[k M1 … Mn] by the β rule, which is what
  * the old content gives once C is reduced and its tuple applied to k, so an
  * import `omega (omega … "file") λa b c.` and the host's reading of a file's
  * fields (`KnowledgeReading.alternative`) read the same fields from either
  * form.
  *
  * The text is edited at three places located by the reader's spans
  * (`Lambdalattice.locatedInScope`), on the advice of the session that wrote
  * the source maps (2026-11-20): the printer names a binder from its origin in
  * the text, and `export` has none, so the conversion edits tokens and leaves
  * names, literals and comments as they are written:
  *
  *   1. `export` is added as the first binder of the file: after the `λ` of the
  *      file's first token when it is one, or as `λ export.` before the file's
  *      first token otherwise;
  *   2. the binder of the tuple is deleted from its parameter list;
  *   3. the head of the tuple, its variable, is respelled `export`.
  *
  * A file that is the tuple alone, `λtuple. tuple M`, has its two `tuple`s
  * respelled `export`, which is α-equivalent. The text is then formatted
  * (`SourceFormatting.formatted`).
  *
  * The tuple is the first abstraction along the file's right spine (an
  * application's argument, an abstraction's body) whose binder is spelled
  * `tuple` and whose body applies its variable to arguments that do not read
  * it. It is the file's term itself or the body of another abstraction: a tuple
  * that is the last argument of an expression, `E λtuple. tuple M`, is E's
  * argument, and deleting its binder would change the term, so such a file is
  * refused (`Refused`), as is a file with no tuple.
  *
  * Each conversion is checked, a failure being a defect of the conversion
  * (`IllegalStateException`): the converted text reads, in the file's scope, to
  * the term the old text reads to with the same structural change made
  * (`exported`), and holds the same comments in the same order; formatting it
  * again changes nothing.
  */
object ExportBinderConversion:

  /** The name of the binder of a file's export. */
  val exportName: String = "export"

  /** The name of the binder of the tuple the conversion looks for. */
  val tupleName: String = "tuple"

  /** A file the conversion leaves as it is, and why. */
  final case class Refused(reason: String) extends Exception(reason)

  /** Where a file's tuple is: the number of abstractions of the spine above it,
    * the span of its binder's name, the span of its head, and whether it is the
    * file's term itself.
    */
  final case class Site(depth: Int, binder: Span, head: Span, root: Boolean)

  /** The text of the file converted, read in the scope of its own place in its
    * tree (`DirectoryTree.scope`). Throws as `converted` of a text does.
    */
  def converted(file: Path)(using com.yang_bo.gezi.ir.StorageAccess): String =
    converted(
      DirectoryTree.scope(file.toAbsolutePath.normalize),
      Files.readString(file)
    )

  /** The text converted, read in the scope of the enclosing names, then
    * formatted. Throws the reader's errors when the text does not read in that
    * scope, `Refused` for a text with no tuple the conversion may remove, and
    * `IllegalStateException` when a check fails, a defect of the conversion.
    */
  def converted(enclosing: Vector[String], text: String)(using
      com.yang_bo.gezi.ir.StorageAccess
  ): String =
    val (term, spans) = Lambdalattice.locatedInScope(enclosing, text)
    val body = under(term, enclosing.size)
    val bodySpans = Vector
      .fill(enclosing.size)(0)
      .foldLeft(spans)((current, position) => current.child(position))
    val found = site(body, bodySpans)
    val edited = edits(text, found)
      .sortBy((span, _) => -span.start)
      .foldLeft(codePoints(text)) { case (written, (span, replacement)) =>
        written.take(span.start) ++ codePoints(replacement) ++ written.drop(
          span.end
        )
      }
    val editedText = edited.map(Character.toString(_)).mkString
    val written = SourceFormatting.formatted(enclosing, editedText)
    val expected = Vector
      .fill(enclosing.size)(())
      .foldLeft(exported(body, found.depth))((inner, _) =>
        DeBruijnTerm.Lambda(inner)
      )
    if Lambdalattice.termInScope(enclosing, written) != expected then
      throw IllegalStateException(
        s"the converted text reads to another term than the old one exported:\n$written"
      )
    if comments(written) != comments(text) then
      throw IllegalStateException(
        s"the converted text holds other comments:\n$written"
      )
    if SourceFormatting.formatted(enclosing, written) != written then
      throw IllegalStateException(
        s"formatting the converted text again changes it:\n$written"
      )
    written

  /** The term under the `count` abstractions of the enclosing names. */
  private def under(term: DeBruijnTerm, count: Int): DeBruijnTerm =
    (0 until count).foldLeft(term)((current, _) =>
      current match
        case DeBruijnTerm.Lambda(body) => body
        case other                     =>
          throw IllegalStateException(
            s"a term read in scope is no abstraction of its enclosing names: $other"
          )
    )

  /** Whether the body applies the variable of the abstraction right outside it
    * to arguments that do not read it: the body of a tuple.
    */
  private def tupleBody(body: DeBruijnTerm): Boolean =
    @tailrec
    def headed(current: DeBruijnTerm, arguments: List[DeBruijnTerm]): Boolean =
      current match
        case DeBruijnTerm.Apply(function, argument) =>
          headed(function, argument :: arguments)
        case DeBruijnTerm.Variable(0) =>
          arguments.forall(argument => !reads(argument, 0))
        case _ => false
    headed(body, Nil)

  /** The site of the file's tuple on the body's right spine. Throws `Refused`
    * when there is none, or when it is the last argument of an expression.
    */
  def site(body: DeBruijnTerm, spans: SyntaxSpans): Site =
    // Where the walk stands: the file's term itself, the body of an
    // abstraction, or the argument of an application.
    enum Place:
      case Root, Body, Argument
    @tailrec
    def walk(
        current: DeBruijnTerm,
        currentSpans: SyntaxSpans,
        depth: Int,
        place: Place
    ): Site =
      current match
        case DeBruijnTerm.Lambda(inner) =>
          currentSpans.nodeBinder match
            case Some(SpelledBinder.Named(`tupleName`, binder))
                if tupleBody(inner) =>
              if place == Place.Argument then
                throw Refused(
                  "the tuple is the last argument of an expression, not the body of an abstraction"
                )
              Site(
                depth,
                binder,
                headSpan(inner, currentSpans.child(0)),
                place == Place.Root
              )
            case _ => walk(inner, currentSpans.child(0), depth + 1, Place.Body)
        case DeBruijnTerm.Apply(_, argument) =>
          walk(argument, currentSpans.child(1), depth, Place.Argument)
        case _ => throw Refused("no tuple at the end of the file's spine")
    walk(body, spans, 0, Place.Root)

  /** The span of the head variable of an application. */
  @tailrec
  private def headSpan(term: DeBruijnTerm, spans: SyntaxSpans): Span =
    term match
      case DeBruijnTerm.Apply(function, _) => headSpan(function, spans.child(0))
      case _                               => spans.span

  /** The edits of the text, each a span of code points and its replacement. */
  private def edits(text: String, found: Site): Vector[(Span, String)] =
    if found.root then
      Vector(found.binder -> exportName, found.head -> exportName)
    else
      Vector(
        deletedBinder(text, found.binder),
        found.head -> exportName,
        firstBinder(text)
      )

  /** The deletion of a binder's name with the white space before it on its
    * line, so that `λ x tuple` becomes `λ x`.
    */
  private def deletedBinder(text: String, binder: Span): (Span, String) =
    val written = codePoints(text)
    @tailrec
    def start(position: Int): Int =
      if position > 0 && (written(position - 1) == ' ' || written(
          position - 1
        ) == '\t')
      then start(position - 1)
      else position
    Span(start(binder.start), binder.end) -> ""

  /** The code points of the text, walked by `codePointAt`. */
  private def codePoints(text: String): Vector[Int] =
    Vector.unfold(0)(offset =>
      Option.when(offset < text.length) {
        val codePoint = text.codePointAt(offset)
        (codePoint, offset + Character.charCount(codePoint))
      }
    )

  /** The insertion of `export` as the file's first binder: after the `λ` of the
    * first token when it is one, else as `λ export.` before the first token.
    */
  private def firstBinder(text: String): (Span, String) =
    val lexemes = Lambdalattice.lexemes(text)
    val offsets = lexemes.scanLeft(0)((offset, lexeme) =>
      offset + lexeme.written.codePointCount(0, lexeme.written.length)
    )
    val (first, index) = lexemes.zipWithIndex
      .collectFirst { case (token: Lexeme.Token, index) => (token, index) }
      .getOrElse(throw Refused("a text with no token"))
    first.kind match
      case TokenKind.Lambda =>
        val after = offsets(index + 1)
        val spaced = lexemes.lift(index + 1) match
          case Some(Lexeme.Token(TokenKind.Name(_), _)) => s" $exportName "
          case _                                        => s" $exportName"
        Span(after, after) -> spaced
      case _ =>
        Span(offsets(index), offsets(index)) -> s"λ $exportName. "

  /** The term with its export moved: one more abstraction around it, the
    * tuple's abstraction, the first abstraction of the right spine at the
    * site's depth, removed and its variable read as the new abstraction's.
    * Throws `IllegalStateException` when the spine has no tuple there.
    */
  def exported(body: DeBruijnTerm, siteDepth: Int): DeBruijnTerm =
    def spine(current: DeBruijnTerm, depth: Int): TailRec[DeBruijnTerm] =
      current match
        case DeBruijnTerm.Lambda(inner) if depth == siteDepth =>
          if !tupleBody(inner) then
            throw IllegalStateException(
              s"the abstraction at depth $depth of the spine is no tuple"
            )
          done(remapped(inner, depth))
        case DeBruijnTerm.Lambda(inner) =>
          tailcall(spine(inner, depth + 1)).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(function, argument) =>
          tailcall(spine(argument, depth)).map(
            DeBruijnTerm.Apply(shifted(function, depth), _)
          )
        case other =>
          throw IllegalStateException(
            s"the spine ends before depth $siteDepth: $other"
          )
    DeBruijnTerm.Lambda(spine(body, 0).result)

  /** A subterm off the spine at the depth, its variables bound outside the file
    * (the enclosing names) made one deeper for `export`.
    */
  private def shifted(term: DeBruijnTerm, depth: Int): DeBruijnTerm =
    mapped(
      term,
      (index, local) => if index >= local + depth then index + 1 else index
    )

  /** The tuple's body at the spine's depth, its abstraction removed: at a local
    * depth, the tuple's variable is `export`, a variable bound on the spine is
    * one shallower, and one bound outside the file is unchanged (one shallower
    * for the tuple's abstraction, one deeper for `export`).
    */
  private def remapped(inner: DeBruijnTerm, depth: Int): DeBruijnTerm =
    mapped(
      inner,
      (index, local) =>
        if index < local then index
        else if index == local then local + depth
        else if index <= local + depth then index - 1
        else index
    )

  /** The term with each variable's index mapped, given its local depth. */
  private def mapped(term: DeBruijnTerm, map: (Int, Int) => Int): DeBruijnTerm =
    def go(current: DeBruijnTerm, local: Int): TailRec[DeBruijnTerm] =
      current match
        case DeBruijnTerm.Variable(index) =>
          done(DeBruijnTerm.Variable(map(index, local)))
        case DeBruijnTerm.Lambda(inner) =>
          tailcall(go(inner, local + 1)).map(DeBruijnTerm.Lambda(_))
        case DeBruijnTerm.Apply(left, right) =>
          for
            left <- tailcall(go(left, local));
            right <- tailcall(go(right, local))
          yield DeBruijnTerm.Apply(left, right)
        case DeBruijnTerm.Choice(left, right) =>
          for
            left <- tailcall(go(left, local));
            right <- tailcall(go(right, local))
          yield DeBruijnTerm.Choice(left, right)
        case DeBruijnTerm.Parallel(left, right) =>
          for
            left <- tailcall(go(left, local));
            right <- tailcall(go(right, local))
          yield DeBruijnTerm.Parallel(left, right)
        case other => done(other)
    go(term, 0).result

  /** Whether the term reads the variable bound `index` abstractions outside it.
    */
  private def reads(term: DeBruijnTerm, index: Int): Boolean =
    def go(current: DeBruijnTerm, local: Int): TailRec[Boolean] = current match
      case DeBruijnTerm.Variable(found)    => done(found == index + local)
      case DeBruijnTerm.Lambda(inner)      => tailcall(go(inner, local + 1))
      case DeBruijnTerm.Apply(left, right) =>
        tailcall(go(left, local)).flatMap(found =>
          if found then done(true) else tailcall(go(right, local))
        )
      case DeBruijnTerm.Choice(left, right) =>
        tailcall(go(left, local)).flatMap(found =>
          if found then done(true) else tailcall(go(right, local))
        )
      case DeBruijnTerm.Parallel(left, right) =>
        tailcall(go(left, local)).flatMap(found =>
          if found then done(true) else tailcall(go(right, local))
        )
      case _ => done(false)
    go(term, 0).result

  /** The comments of a text, in order. */
  private def comments(text: String): Vector[String] =
    Lambdalattice.lexemes(text).collect { case Lexeme.Comment(written) =>
      written.stripTrailing
    }

  /** The evaluator steps one read of a file's fields may take, from the tree's
    * root. MEASURED 2026-11-13 by the conversion to the tuple module encoding
    * (`ModuleTupleConversion`, since deleted; read it back by
    * `git show ca2a2dbdc:gezi/migration/src/main/scala/gezi/migration/ModuleTupleConversion.scala`):
    * the most steps a read of the tree at 14ae534ef took was 199,242 (a read of
    * contest-entries-solo/entry); the limit is that with a quarter's margin,
    * rounded up. A read that the limit stops is listed, never taken as equal or
    * different, and the limit is not raised before its cause is found.
    */
  val readingLimit: Long = 250_000

  /** Whether a read stopped on its budget of steps or tables
    * (`KnowledgeReading.run`), not for a reason of the file's term: such a stop
    * says nothing of the file, so the check never accepts it.
    */
  def budgetStop(reason: String): Boolean =
    reason.startsWith("the knowledge was not read within")

  /** A read of a file's fields: the fields read back to the IR unevaluated,
    * with the evaluator steps and the tables the read took; or why it stopped.
    */
  final case class FieldsRead(
      fields: Vector[Configured[NoFacts.type]],
      steps: Long,
      tables: Int
  )

  /** The fields of the file's tuple read from the tree's visible root under the
    * compilation's reading state, within `readingLimit`.
    */
  def fieldsRead(visible: Path, file: Path): Either[String, FieldsRead] =
    val instance = DirectoryTree.instance(visible, file)
    val reading: Reading[NoFacts.type, Vector[Configured[NoFacts.type]]] =
      KnowledgeReading
        .alternative(com.yang_bo.gezi.ir.Value.of(instance)(using NoFacts), 1)(using
          NoFacts
        )
        .map(_._2.map(KnowledgeReading.term(_, Set.empty)))
    try
      val (fields, after) = KnowledgeReading.run(
        reading,
        readingLimit,
        KnowledgeReading.compilationState
      )
      Right(
        FieldsRead(
          fields,
          after.budget.spent,
          after.tables.complete.size + after.tables.open.size
        )
      )
    catch case KnowledgeReadingError(reason) => Left(reason)

/** Converts the files under the directories in place
  * (`ExportBinderConversion`), the tree's visible root first, and checks that
  * every file's fields read the same before and after; prints the refused
  * files, then a line per file of the steps and tables of its reads before and
  * after, then the files whose reads differ or stop; exits with a failure when
  * any does.
  */
@main def convertExportBinders(visible: String, directories: String*): Unit =
  // The command line is where this tool sets up its reader: the text it formats reads no storage's view.
  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()
  val visibleRoot = Paths.get(visible).toAbsolutePath.normalize
  val all = LambdalatticeFormatting.files(
    directories.toVector.map(Paths.get(_).toAbsolutePath.normalize)
  )
  val conversions = all.map(file =>
    file -> (try Right(ExportBinderConversion.converted(file))
    catch case ExportBinderConversion.Refused(reason) => Left(reason))
  )
  conversions
    .collect { case (file, Left(reason)) => s"refused\t$file\t$reason" }
    .foreach(println)
  val converted = conversions.collect { case (file, Right(text)) =>
    (file, text)
  }
  val before = converted.map((file, _) =>
    ExportBinderConversion.fieldsRead(visibleRoot, file)
  )
  converted.foreach((file, text) =>
    val _ = Files.writeString(file, text)
  )
  val after = converted.map((file, _) =>
    ExportBinderConversion.fieldsRead(visibleRoot, file)
  )
  println("steps before\tsteps after\ttables before\ttables after\tfile")
  converted.zip(before.zip(after)).foreach { case ((file, _), (old, current)) =>
    def shown(
        read: Either[String, ExportBinderConversion.FieldsRead],
        part: ExportBinderConversion.FieldsRead => Long
    ): String =
      read.fold(_ => "stopped", found => part(found).toString)
    println(
      Vector(
        shown(old, _.steps),
        shown(current, _.steps),
        shown(old, _.tables.toLong),
        shown(current, _.tables.toLong),
        file.toString
      )
        .mkString("\t")
    )
  }
  // A file whose old read stops for a reason of its term is a fixture of a
  // failing read: its new read must stop as well, and each such pair is
  // listed. A stop on the budget is never accepted.
  def budgetStopped(old: String, current: String): Boolean =
    ExportBinderConversion.budgetStop(old) || ExportBinderConversion.budgetStop(
      current
    )
  converted
    .zip(before.zip(after))
    .collect {
      case ((file, _), (Left(old), Left(current)))
          if !budgetStopped(old, current) =>
        s"both reads stop\t$file\t$old / $current"
    }
    .foreach(println)
  val problems = converted.zip(before.zip(after)).collect {
    case ((file, _), (Left(old), Left(current)))
        if budgetStopped(old, current) =>
      s"a read stopped on its budget\t$file\t$old / $current"
    case ((file, _), (Left(old), Right(_))) =>
      s"the old read stopped\t$file\t$old"
    case ((file, _), (Right(_), Left(current))) =>
      s"the new read stopped\t$file\t$current"
    case ((file, _), (Right(old), Right(current)))
        if old.fields != current.fields =>
      s"the reads differ\t$file"
  }
  problems.foreach(println)
  if problems.nonEmpty then
    throw IllegalStateException(
      s"${problems.size} files whose reads differ or stop"
    )
