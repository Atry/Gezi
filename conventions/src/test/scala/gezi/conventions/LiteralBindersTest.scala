package gezi.conventions

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters.*
import scala.util.Using

/** The binders of the lambdalattice files of the tree that are literals.
  *
  * Purpose: catch a string key written back into a file the host reads. A
  * literal binder makes the abstraction a variable arguments partial function
  * keyed by the literal, and the host reads no string key (`CONTRIBUTING.md`,
  * "The Architecture"): an entry or a table of
  * terms is a Scott tuple read by position, knowledge a fixed-width mixin. A
  * literal that begins with `$` is a synthetic label, which the compiler's
  * knowledge (library files and lemmas) writes and an end user's program may
  * not, and is allowed. A directory's name is
  * an argument of `omega`, never a binder, so it is not checked. The files
  * under `problems/` are not checked: a problem may be written against the
  * conventions on purpose, to test the spellings they do not adopt
  * (`CONTRIBUTING.md`, "lambdalattice coding conventions").
  */
object LiteralBinders:

  /** The lambdalattice files under the root, outside `target` and
    * `problems`, each with its path relative to the root.
    */
  def files(root: Path): Vector[(String, String)] =
    Using.resource(Files.walk(root))(paths =>
      paths.toList.asScala.toVector
        .map(path => (root.relativize(path).toString, path))
        .filter((name, _) =>
          name.endsWith(".lambdalattice") && !name.split('/').contains("target") && !name.startsWith("problems/")
        )
        .map((name, path) => (name, Files.readString(path)))
    )

  private def isNameStart(character: Char): Boolean = character.isLetter || character == '_' || character == '$'

  private def isNamePart(character: Char): Boolean = character.isLetterOrDigit || character == '_' || character == '$'

  /** The end of the string literal that starts at the offset, past its
    * closing quote.
    */
  private def stringEnd(text: String, start: Int): Int =
    @scala.annotation.tailrec
    def scanned(cursor: Int): Int =
      if cursor >= text.length then text.length
      else
        text(cursor) match
          case '"'  => cursor + 1
          case '\\' => scanned(cursor + 2)
          case _    => scanned(cursor + 1)
    scanned(start + 1)

  /** The offset of each binder after a `λ` that is a literal but a string
    * that begins with `$`, comments and strings outside binders skipped.
    */
  def literalBinders(text: String): Vector[Int] =
    @scala.annotation.tailrec
    def binders(cursor: Int, found: Vector[Int]): (Int, Vector[Int]) =
      if cursor >= text.length then (cursor, found)
      else
        text(cursor) match
          case '.'                                 => (cursor + 1, found)
          case character if character.isWhitespace => binders(cursor + 1, found)
          case '#' =>
            text.indexOf('\n', cursor) match
              case -1      => (text.length, found)
              case newline => binders(newline + 1, found)
          case '"' =>
            val end = stringEnd(text, cursor)
            binders(end, if text.startsWith("\"$", cursor) then found else found :+ cursor)
          case character if isNameStart(character) =>
            binders(text.indexWhere(!isNamePart(_), cursor) match { case -1 => text.length; case end => end }, found)
          case _ => (cursor + 1, found :+ cursor)
    @scala.annotation.tailrec
    def scanned(cursor: Int, found: Vector[Int]): Vector[Int] =
      if cursor >= text.length then found
      else
        text(cursor) match
          case '#' =>
            text.indexOf('\n', cursor) match
              case -1      => found
              case newline => scanned(newline + 1, found)
          case '"' => scanned(stringEnd(text, cursor), found)
          case 'λ' =>
            val (after, more) = binders(cursor + 1, found)
            scanned(after, more)
          case _ => scanned(cursor + 1, found)
    scanned(0, Vector.empty)

  /** Each literal binder of the files, `path:line: text`. */
  def problems(files: Vector[(String, String)]): Vector[String] =
    files.flatMap((path, text) =>
      val lines = text.split('\n').toVector
      literalBinders(text).map(offset =>
        val line = text.take(offset).count(_ == '\n')
        s"$path:${line + 1}: ${lines(line).trim}"
      )
    )

class LiteralBindersTest extends gezi.generatedinputs.FailFastSuite:

  private lazy val files: Vector[(String, String)] = LiteralBinders.files(ScalaSources.root)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => files)

  test("no lambdalattice file of the tree binds a literal but a synthetic label") {
    assert(files.nonEmpty, s"no lambdalattice file found under ${ScalaSources.root}")
    val found = LiteralBinders.problems(files)
    assert(found.isEmpty, found.mkString("\n"))
  }

