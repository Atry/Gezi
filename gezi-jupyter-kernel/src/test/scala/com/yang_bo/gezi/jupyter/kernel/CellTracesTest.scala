package com.yang_bo.gezi.jupyter.kernel

import almond.interpreter.api.DisplayData
import almond.interpreter.api.ExecuteResult
import hedgehog.Result
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Paths
import com.yang_bo.gezi.contest.entry.ArticleDestination
import com.yang_bo.gezi.contest.entry.Defaults
import com.yang_bo.gezi.contest.entry.generic.GenericEntryProvider
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.rewritetrace.TracePageText

/** The traces a kernel started with `--trace-directory` shows (`CellTraces`),
  * on the data entry `contest-entries-wren` through the kernel's interpreter,
  * generated normal forms bound by a cell and shown through the entry. Its
  * purpose is to catch a player's file or a font a style sheet loads that the
  * kernel's build does not put on the classpath, a page that still loads a file
  * (which the sandbox of Jupyter Server's `/files/` answers by the login's
  * redirect), a frame whose path does not lead from the working directory to
  * the page of a trace the cell wrote, and a trace written but not shown or
  * shown twice.
  */
class CellTracesTest extends GeneratedProperties:
  // Measured 2026-11-19 on 8 CPUs (contest.slice, CPUs 0-7, nice 10), the 1-minute load 6.1: the suite 30.9 s, nearly
  // all of it the property's three cases, each of which writes a page of 4.8 MB; the bound is 1.5 times that rounded up
  // to 5 s.
  // FIXME: this suite exceeds the 3 s default: each case reads the whole entry `contest-entries-wren`, as CellInterpreterLawTest does, with https://github.com/Atry/private-overlay/issues/1925
  // its destination in a fresh directory, and the entry writes an article and a trace for the cell.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(50, "s")

  private def text(term: Term): String = LambdalatticeText.text(term)

  test("the player a page holds loads no file") {
    val player = CellTraces.player()
    val loaded = player.styleSheets
      .flatMap("""url\("?([^")]+)""".r.findAllMatchIn(_).map(_.group(1)))
      .filterNot(_.startsWith("data:"))
    assertEquals(loaded, Vector.empty[String])
    assert(
      player.script.nonEmpty && player.styleSheets.size == TracePageText.playerStyleSheets.size
    )
  }

  property(
    "a cell's output shows the page of each trace the cell wrote, each of which holds its player",
    _.copy(testLimit = 3)
  ) {
    for shown <- HoasGenerators.normalForm.forAllWithLog(text)
    yield
      val working = Files.createTempDirectory("cell-traces")
      val traces = CellTraces.started(working.resolve("traces"), working)
      val entry = GenericEntryProvider().initial(
        Paths.get(sys.props("gezi.buildRoot")).resolve("gezi-contest-entries-wren"),
        Defaults.caches(),
        ArticleDestination.WrittenWithTraces(traces.directory)
      )
      val buildRoot = Paths.get(sys.props("gezi.buildRoot"))
      val interpreter =
        CellInterpreter.started(
          buildRoot,
          NotebookLocation.of(working.resolve("cell-traces.ipynb")),
          entry,
          Some(traces)
        )
      val before = traces.traces()
      interpreter.execute(
        s"λ\"shown\". (${text(shown)})",
        storeHistory = true,
        None,
        None,
        None
      ) match
        case ExecuteResult.Success(data) =>
          val written = traces
            .traces()
            .filterNot(before.contains)
            .map(CellTraces.notebookPage)
          val html = data.detailedData.get("text/html") match
            case Some(DisplayData.Value.String(value)) => value
            case other => fail(s"the output has no HTML: $other")
          val sources =
            """src="([^"]+)"""".r.findAllMatchIn(html).map(_.group(1)).toVector
          Result
            .diff(
              sources.map(source => working.resolve(source).normalize),
              written.map(_.toAbsolutePath.normalize)
            )(_ == _)
            .and(
              Result.diff(
                written.filterNot(Files.isRegularFile(_)),
                Vector.empty
              )(_ == _)
            )
            .and(
              Result.diff(
                written.filter(page =>
                  val content = Files.readString(page, StandardCharsets.UTF_8)
                  content.contains("<link rel=\"stylesheet\"") || content
                    .contains("<script src=")
                ),
                Vector.empty
              )(_ == _)
            )
            .and(Result.assert(written.nonEmpty).log("the cell wrote no page"))
        case other => Result.failure.log(s"the cell was not answered: $other")
  }
