package gezi.conventions

import java.nio.file.Files
import scala.util.matching.Regex

/** The framework is a list of projects, not a prefix (`CONTRIBUTING.md`,
  * "The framework"), so that the framework stays distinct from the
  * experiments built on it while every project is named by its domain
  * terms. Its purpose is to catch a framework project that comes to depend
  * on a project outside the list, by a `dependsOn` of the build or by a name
  * in its sources: the framework is what every entry builds on and must not
  * reach into the standard library, the front end, the contest or an entry.
  * A framework project may depend on the other framework projects, and its
  * tests on `generatedinputs`.
  */
class FrameworkBoundaryTest extends gezi.generatedinputs.FailFastSuite:

  private val framework: Vector[String] = Vector(
    "ir",
    "orientation",
    "egraph",
    "ematching",
    "ematching-indexing",
    "ematching-interpretation",
    "ematching-closures",
    "ematching-bytecode",
    "saturation",
    "extraction"
  )

  private val allowedProjects: Set[String] = framework.toSet + "generatedinputs"

  /** A project's package is `gezi.` and its directory with `-` read as
    * `.`; a package name is allowed when its first segment below `gezi`
    * is an allowed project's.
    */
  // The suppression of a custom wart names it (`gezi.warts.NoJavaUtilConcurrent`),
  // as a string in an annotation, not as a dependency: the project `warts`
  // depends on nothing and no project depends on it.
  private val allowedRoots: Set[String] = (allowedProjects + "warts").map(_.split('-').head)

  private val declarationPattern: Regex = """(?m)^lazy val `?([\w-]+)`?\s*=""".r

  private val dependsOnPattern: Regex = """(?s)dependsOn\((.*?)\)""".r

  /** A string literal, such as a configuration mapping, which names no
    * project.
    */
  private val stringPattern: Regex = """"[^"]*"""".r

  private val dependencyPattern: Regex = """`([\w-]+)`|(?<![\w-])([A-Za-z]\w*)(?![\w-])""".r

  private val packageReferencePattern: Regex = """\bgezi\.(\w+)""".r

  test("the framework's projects depend on framework projects only, in the build") {
    val build = ScalaSources.commentsBlanked(Files.readString(ScalaSources.root.resolve("build.sbt")))
    val declarations = declarationPattern.findAllMatchIn(build).toVector
    val blocks = declarations.zip(declarations.drop(1).map(_.start) :+ build.length).map((declaration, end) =>
      declaration.group(1) -> build.substring(declaration.end, end)
    )
    assertEquals(blocks.map(_._1).filter(framework.contains).sorted, framework.sorted)
    val found = blocks.filter((name, _) => framework.contains(name)).flatMap((name, block) =>
      dependsOnPattern
        .findAllMatchIn(block)
        .flatMap(arguments => dependencyPattern.findAllMatchIn(stringPattern.replaceAllIn(arguments.group(1), "")))
        .map(dependency => Option(dependency.group(1)).getOrElse(dependency.group(2)))
        .filterNot(dependency => dependency == "Test" || allowedProjects.contains(dependency))
        .map(dependency => s"$name depends on $dependency")
    )
    assertEquals(found, Vector.empty)
  }

  test("the framework's sources name packages of framework projects only") {
    val root = ScalaSources.root
    val sources = ScalaSources
      .sources(root)
      .filter(path => framework.exists(project => path.startsWith(root.resolve(project))))
    assert(sources.nonEmpty, s"no Scala source found under the framework's directories of $root")
    val found = sources.flatMap(path =>
      packageReferencePattern
        .findAllMatchIn(ScalaSources.commentsBlanked(Files.readString(path)))
        .map(_.group(1))
        .filterNot(allowedRoots.contains)
        .distinct
        .map(segment => s"${root.relativize(path)}: gezi.$segment")
    )
    assertEquals(found, Vector.empty)
  }
