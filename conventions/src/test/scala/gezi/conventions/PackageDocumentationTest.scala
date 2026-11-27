package gezi.conventions

import java.nio.file.Files
import java.nio.file.Path
import scala.util.matching.Regex

/** The rule that every Scala package has a package-level Scaladoc, read off the
  * sources of every module, tests included.
  *
  * Scaladoc shows on a package's page the doc comment of the package's package
  * object, and not one written on a package clause, so a package's
  * documentation is an empty package object, in a file `package.scala` of the
  * package's directory, with its doc comment directly above it. Every package
  * that a source file declares by its package clauses has exactly one package
  * object, since two package objects of one package on one classpath clash;
  * that object carries a doc comment and nothing follows it in its file, so
  * that it holds no member. A file that holds a package object declares the
  * package of the object, not the package of its clause: a parent package that
  * holds no source of its own needs no package object.
  */
class PackageDocumentationTest extends gezi.generatedinputs.FailFastSuite:

  private val packageClausePattern: Regex = """(?m)^package\s+([\w.]+)\s*$""".r

  private val packageObjectPattern: Regex =
    """(?m)^package\s+object\s+(\w+)""".r

  /** A package object: the package it documents, whether a doc comment stands
    * directly above it, whether its file ends with it, and where it is.
    */
  private final case class PackageObject(
      packageName: String,
      documented: Boolean,
      endsItsFile: Boolean,
      location: String
  )

  /** A source file: its path, its text, and its text with comments blanked.
    */
  private final case class Source(path: Path, text: String, code: String)

  /** The package the file's package clauses name, the clauses joined. */
  private def clausePackage(source: Source): String =
    packageClausePattern
      .findAllMatchIn(source.code)
      .toVector
      .map(_.group(1))
      .mkString(".")

  private def packageObjects(
      root: Path,
      source: Source
  ): Vector[PackageObject] =
    val enclosing = clausePackage(source)
    packageObjectPattern
      .findAllMatchIn(source.code)
      .toVector
      .map(found =>
        val before = source.text.substring(0, found.start).stripTrailing
        val commentStart = before.lastIndexOf("/*")
        val documented = before.endsWith("*/") && commentStart >= 0 &&
          before.startsWith("/**", commentStart)
        val line = source.text.substring(0, found.start).count(_ == '\n') + 1
        val name = found.group(1)
        PackageObject(
          packageName = if enclosing.isEmpty then name else s"$enclosing.$name",
          documented = documented,
          endsItsFile = source.code.substring(found.end).isBlank,
          location = s"${root.relativize(source.path)}:$line"
        )
      )

  test(
    "every package declared by a source file has one documented package object"
  ) {
    val root = ScalaSources.root
    val sources = ScalaSources
      .sources(root)
      .map(path =>
        val text = Files.readString(path)
        Source(path, text, ScalaSources.commentsBlanked(text))
      )
    assert(sources.nonEmpty, s"no Scala source found under $root")
    val objects = sources.flatMap(packageObjects(root, _))
    val declared = sources
      .filter(source => packageObjectPattern.findFirstIn(source.code).isEmpty)
      .map(clausePackage)
      .filter(_.nonEmpty)
      .distinct
      .sorted
    val wrongCounts = declared.flatMap(packageName =>
      val documenting = objects.filter(_.packageName == packageName)
      if documenting.size == 1 then Vector.empty
      else
        Vector(
          s"package $packageName has ${documenting.size} package objects, one expected, found at [" +
            documenting.map(_.location).mkString(", ") + "]"
        )
    )
    val undocumented = objects
      .filterNot(_.documented)
      .map(found =>
        s"${found.location}: the package object of ${found.packageName} has no doc comment directly above it"
      )
    val notEmpty = objects
      .filterNot(_.endsItsFile)
      .map(found =>
        s"${found.location}: something follows the package object of ${found.packageName}"
      )
    val found = wrongCounts ++ undocumented ++ notEmpty
    assert(found.isEmpty, found.mkString("\n"))
  }
