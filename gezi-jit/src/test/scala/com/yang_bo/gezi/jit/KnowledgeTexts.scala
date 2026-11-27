package com.yang_bo.gezi.jit

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.StreamConverters.*
import scala.util.Using
import com.yang_bo.gezi.standardlibrary.KnowledgeSlot
import com.yang_bo.gezi.standardlibrary.KnowledgeText
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.StandardLibrary

/** The knowledge files and the library files the jit's tests generate, in a
  * fresh tree under the build.
  */
object KnowledgeTexts:

  /** The directory the generated trees are written under: `jit/target`, inside
    * the build, so that a tree's files are read off the tree whose visible
    * subtree is Gezi's directory (`compiled`) and its knowledge files reach the
    * library's conversions of literals under corpora/ by `gezi "corpora"`. A
    * temporary directory of the system is not under that subtree.
    */
  private val generatedTrees: Path =
    LibraryFiles.buildRoot.resolve("jit/target/generated-knowledge")

  /** Runs the body on a fresh tree of the name and deletes the tree when the
    * body ends, normally or by an exception, because the test that made a tree
    * owns it and a leftover tree is listed by every later reading of the
    * directory it stood in. The tree is its own root: the body's path is
    * `<base>/<gezi's directory name>/<name>`, beside a link `corpora` to the
    * real `corpora`, so that a reading rooted at the tree's parent (`compiled`)
    * lists nothing but the tree and `corpora`. The name is the tree's binder in
    * the files written under it, so no file of the tree may be named as it is,
    * nor as `library`, `compiler` or `compiled_knowledge` (`compiled`).
    */
  def withFreshTree[Result](name: String)(body: Path => Result): Result =
    Files.createDirectories(generatedTrees)
    val base = Files.createTempDirectory(generatedTrees, "tree")
    try
      val root = Files.createDirectories(
        base.resolve(LibraryFiles.buildRoot.getFileName.toString)
      )
      Files.createSymbolicLink(
        root.resolve("corpora"),
        LibraryFiles.sourceTree.toAbsolutePath
      )
      body(root.resolve(name))
    finally deleteRecursively(base)

  /** Deletes the directory and everything under it, a link as a link. */
  private def deleteRecursively(directory: Path): Unit =
    val paths = Using.resource(Files.walk(directory))(_.toScala(Vector))
    paths.reverse.foreach(Files.delete)

  /** The imports of the conversions of literals for a file of a tree under
    * `generatedTrees` (`KnowledgeText.literalImports`).
    */
  val literalImports: Vector[KnowledgeText.Import] =
    KnowledgeText.literalImports("gezi", Vector("corpora"))

  /** The text of a knowledge file, a tuple of one field: the mixin of the
    * members given, each with its slot (`StandardLibrary.knowledgeSlots`) and
    * written by `KnowledgeText`, under the imports and the conversions of
    * literals. Throws `IllegalArgumentException` for no member.
    */
  def knowledgeFile(
      imports: Vector[KnowledgeText.Import],
      members: Vector[(KnowledgeSlot, String)]
  ): String =
    KnowledgeText.file(
      literalImports ++ imports,
      KnowledgeText.mixin(
        StandardLibrary.knowledgeSlots.map(slot =>
          (
            slot,
            members.collect { case (`slot`, member) =>
              KnowledgeText.Member(member)
            }
          )
        )
      )
    )

  /** The text of a library file of the members' terms, each a closed term's
    * text, in order: a Scott tuple of them, which the test reads by position
    * (`StandardLibrary.entryMembers` of `libraryTable`) and a knowledge file
    * imports by position (`KnowledgeText.Import.Grouped`;
    * `KnowledgeText.groupFile`).
    */
  def libraryFile(members: Vector[(String, String)]): String =
    KnowledgeText.groupFile(members.map(_._2))

  /** The term table of a library file of the members (`libraryFile`), at the
    * path relative to the tree's directory, the members' names its fields'.
    */
  def libraryTable(
      file: String,
      members: Vector[(String, String)]
  ): com.yang_bo.gezi.standardlibrary.TermTable =
    com.yang_bo.gezi.standardlibrary.TermTable(file, members.map(_._1))

  /** The library of the knowledge files of the paths in the generated tree,
    * each a tuple of one field (`knowledgeFile`) and its path relative to the
    * tree's parent, its first label the tree's own name, with the backends'
    * checks: a file `compiled_knowledge.lambdalattice` written at the tree's
    * root imports them and returns their choice as the one field of its tuple,
    * which `StandardLibrary.compiledAt` compiles, read off the tree whose
    * visible subtree is the tree's parent (`withFreshTree`). Throws
    * `IllegalArgumentException` for no path, or for a path whose first label is
    * not the tree's name.
    */
  def compiled(
      tree: Path,
      knowledgeFiles: Vector[String],
      backends: Vector[com.yang_bo.gezi.standardlibrary.LibraryBackend]
  ): StandardLibrary =
    if knowledgeFiles.isEmpty then
      throw IllegalArgumentException(
        "a generated tree's library needs a knowledge file"
      )
    val treeName = tree.getFileName.toString
    val imports = knowledgeFiles.zipWithIndex.map((path, index) =>
      path.split('/').toVector match
        case `treeName` +: labels if labels.nonEmpty =>
          KnowledgeText.Import
            .Positional(treeName, labels, Vector(s"knowledge_file_$index"))
        case _ =>
          throw IllegalArgumentException(
            s"the knowledge file $path is not under the tree $treeName"
          )
    )
    val body = knowledgeFiles.indices
      .map(index => s"knowledge_file_$index")
      .mkString(" + ")
    val knowledge = Files.writeString(
      tree.resolve("compiled_knowledge.lambdalattice"),
      KnowledgeText.file(imports, body)
    )
    StandardLibrary.compiledAt(tree.getParent, knowledge, backends)
