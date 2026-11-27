package gezi.conventions

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import scala.jdk.CollectionConverters.*
import scala.util.Using
import scala.util.matching.Regex

/** The Scala sources the convention tests read: every `.scala` file under a
  * `src/main/scala` or `src/test/scala` directory of the build whose root the
  * build passes in the property `gezi.buildRoot`, outside `target`.
  */
object ScalaSources:

  /** The root of the build to scan. */
  def root: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException(
        "the build passes gezi.buildRoot to the forked test JVM"
      )
    )
  )

  /** The Scala sources under the root, tests included. */
  def sources(root: Path): Vector[Path] =
    Using.resource(Files.walk(root))(paths =>
      paths.toList.asScala.toVector.filter(path =>
        val name = root.relativize(path).toString
        name.endsWith(".scala") &&
        (name.contains("/src/main/scala/") ||
          name.contains("/src/test/scala/")) &&
        !name.split('/').contains("target")
      )
    )

  /** The Scala sources under the build root (`sources`), each with its path
    * relative to the root and its text, read once per test JVM: the suites that
    * check every source list it as their shared fixture
    * (`FailFastSuite.sharedFixtures`), so that the walk of the root, whose
    * build outputs hold most of its files, is made once and charged to no test
    * (WartSuppressionTest, which walked and read every source in its test,
    * overran its 3 s deadline twice beside the other conventions suites doing
    * the same at the 1-minute load 5, 2026-11-19, and passed alone in 0.76 to
    * 0.87 s).
    */
  lazy val texts: Vector[(String, String)] =
    val found = root
    sources(found).map(source =>
      (found.relativize(source).toString, Files.readString(source))
    )

  private val commentPattern: Regex = """(?s)/\*.*?\*/|//[^\n]*""".r

  /** The text with every comment replaced by spaces, its line breaks kept, so
    * that offsets still count the original lines.
    */
  def commentsBlanked(text: String): String =
    commentPattern.replaceAllIn(
      text,
      comment =>
        Regex.quoteReplacement(
          comment.matched.map(character =>
            if character == '\n' then '\n' else ' '
          )
        )
    )
