package gezi.migration

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.frontend.SourceFormatting
import scala.jdk.StreamConverters.*
import scala.util.Using

/** The formatter of the lambdalattice files of a directory tree: each file's
  * text respelled with the term it reads to kept, every change checked by
  * reading the text again in the file's scope in its tree
  * (`DirectoryTree.scope`), so that the names it uses of its directories
  * resolve as the tree resolves them. Names, literals, comments and the
  * bindings the text writes stay as they are written.
  *
  * The text is read into the IR with its source map and written back in the
  * layout of CONTRIBUTING.md, "lambdalattice layout: no right-associative parentheses, CPS one step per line" (`gezi.frontend.SourceFormatting`):
  * the formatter works on the debug information, parsing into the IR first
  * and formatting back from it.
  */
object LambdalatticeFormatting:

  /** The text of the file formatted, read in the scope of its own place in
    * its tree. Throws the reader's errors when the file does not read in
    * that scope.
    */
  def formatted(file: Path)(using gezi.ir.StorageAccess): String =
    formatted(DirectoryTree.scope(file.toAbsolutePath.normalize), Files.readString(file))

  /** The text formatted, read in the scope of the enclosing names
    * (`SourceFormatting.formatted`, which throws the reader's errors when the
    * text does not read in that scope, and `IllegalStateException` when the
    * formatted text reads to another term or holds other comments, a defect
    * of the formatter).
    */
  def formatted(enclosing: Vector[String], text: String)(using gezi.ir.StorageAccess): String = SourceFormatting.formatted(enclosing, text)

  /** The lambdalattice files under the directories, in order of their
    * paths: every file of the extension `DirectoryTree.fileExtension`,
    * outside the directories `target` and those whose name starts with a dot,
    * which hold build output and tools' state, no source.
    */
  def files(directories: Vector[Path]): Vector[Path] =
    directories.flatMap(directory =>
      Using.resource(Files.walk(directory))(_.toScala(Vector)).filter(path =>
        Files.isRegularFile(path) && path.getFileName.toString.endsWith(DirectoryTree.fileExtension) &&
          levels(directory.relativize(path)).forall(level => level != "target" && !level.startsWith("."))
      )
    ).distinct.sorted

  /** Each file under the directories formatted and written back when its
    * text changes; returns the files written.
    */
  def formattedInPlace(directories: Vector[Path])(using gezi.ir.StorageAccess): Vector[Path] =
    files(directories).flatMap(file =>
      val written = formatted(file)
      if written == Files.readString(file) then None
      else
        val _ = Files.writeString(file, written)
        Some(file)
    )

  /** The names of the levels of the relative path. */
  private def levels(relative: Path): Vector[String] =
    (0 until relative.getNameCount).map(index => relative.getName(index).toString).toVector

/** Formats the lambdalattice files under the directories in place
  * (`LambdalatticeFormatting.formattedInPlace`) and prints the files written.
  */
@main def formatLambdalatticeFiles(directories: String*): Unit =
  // The command line is where this tool sets up its reader: the text it formats reads no storage's view.
  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()
  LambdalatticeFormatting.formattedInPlace(directories.toVector.map(Paths.get(_))).foreach(println)
