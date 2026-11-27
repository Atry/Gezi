package gezi.standardlibrary

import gezi.directorysugar.DirectoryTree
import gezi.ir.NoFacts
import gezi.knowledgereading.KnowledgeReading
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.ir.{Configured, NativeSpecializer}

/** The terms of library files as the tree read gives them, for the tests
  * that need a library term in hand: each file's fields, the members of the
  * file in the positions an import binds them, read by
  * projection off the tree (`fileFields`), with no text written. A file is
  * reached by its path in the tree, never by a name the index keeps: the
  * index has no library files.
  */
object TreeTerms:

  /** The fields of each path's file, in the order of the paths, such as
    * `corpora/library/prelude/natural`, each file's fields in their
    * positions, the reads threaded through one compilation's reading state.
    */
  def fields(paths: Vector[String]): Vector[Vector[Configured[NoFacts.type]]] =
    given NoFacts.type = NoFacts
    paths
      .foldLeft((Vector.empty[Vector[Configured[NoFacts.type]]], KnowledgeReading.compilationState)) { case ((read, state), path) =>
        val (fileRead, after) = fileFields(path, state)
        (read :+ fileRead, after)
      }
      ._1

  /** The paths of the files of the directory, such as
    * `corpora/library/prelude`, in the directory's order.
    */
  def filePaths(directory: String): Vector[String] =
    DirectoryTree.fileKeys(LibraryFiles.buildRoot.resolve(directory)).map(key => s"$directory/$key")

  /** The fields of the tuple the file at the path returns (relative to the
    * build root, without its extension), each read back to a closed
    * instruction: the file read by projection off the tree whose visible
    * subtree is Gezi's directory (`StandardLibrary.entryTerm`), its
    * fields taken by `KnowledgeReading.alternative`, under the state given,
    * within `StandardLibrary.memberReadingLimit`.
    */
  private def fileFields(path: String, state: ReadingState[NoFacts.type])(using NoFacts.type): (Vector[Configured[NoFacts.type]], ReadingState[NoFacts.type]) =
    val root = LibraryFiles.buildRoot
    val reading = StandardLibrary.entryTerm(root, root.resolve(path + DirectoryTree.fileExtension), state)
    val (found, after) = KnowledgeReading.run(
      KnowledgeReading.alternative(reading.term, 1).map(_._2),
      StandardLibrary.memberReadingLimit,
      reading.state
    )
    (found.map(KnowledgeReading.term(_, Set.empty)), after)
