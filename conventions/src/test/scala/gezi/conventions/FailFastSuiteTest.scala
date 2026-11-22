package gezi.conventions

import java.nio.file.Files

/** The sources that declare a suite directly on munit's `FunSuite`.
  *
  * Purpose: munit's own timeout does not stop a synchronous test body
  * (https://github.com/scalameta/munit/issues/730), so a suite that extends
  * `munit.FunSuite` instead of `FailFastSuite` can hold the sbt server for
  * hours and has no default deadline (CONTRIBUTING.md, "Tests fail fast").
  */
object FailFastSuiteCheck:

  private val directFunSuite = """extends\s+(munit\.)?FunSuite\b""".r

  private val baseSuiteSource = "FailFastSuite.scala"

  /** The sources, other than the base suite's own, that extend `FunSuite`
    * directly, each `path:number: text`.
    */
  def problems(sources: Vector[(String, String)]): Vector[String] =
    sources.filterNot((path, _) => path.endsWith(baseSuiteSource)).flatMap((path, text) =>
      val lines = text.split('\n').toVector
      val code = ScalaSources.commentsBlanked(text).split('\n').toVector
      lines.zipWithIndex.collect {
        case (line, index) if directFunSuite.findFirstIn(code(index)).isDefined =>
          s"$path:${index + 1}: ${line.trim}"
      }
    )

class FailFastSuiteTest extends gezi.generatedinputs.FailFastSuite:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => ScalaSources.texts)

  test("every test suite of the Scala sources extends FailFastSuite, not munit.FunSuite") {
    assert(ScalaSources.texts.nonEmpty, s"no Scala source found under ${ScalaSources.root}")
    val found = FailFastSuiteCheck.problems(ScalaSources.texts)
    assert(found.isEmpty, found.mkString("\n"))
  }
