package com.yang_bo.gezi.traceplayer

import hedgehog.Size
import com.yang_bo.gezi.generatedinputs.SeededSamples
import com.yang_bo.gezi.rewritetrace.TracePageText
import com.yang_bo.gezi.rewritetrace.TraceStart
import com.yang_bo.gezi.rewritetrace.TraceText
import snapshot4s.generated.snapshotConfig

/** The page `TracePageText.page` writes for a generated trace
  * (`TermSequences.trace`, from a fixed seed), recorded as a snapshot. Its
  * purpose is to show, as a diff, any change of the page's text: the embedded
  * start and trace, the paths of the script and the style sheets, the
  * container. The snapshot is also the page the player is looked at with in a
  * browser: the sbt task `trace-player/demonstrationPage` copies it beside the
  * linked script and the style sheets.
  */
class TracePageTextSnapshotTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  test("the page of a generated trace") {
    // Of eight samples, the one with the most commands, so that the page
    // shows terms of several layers rewritten over several steps.
    val (start, trace) = SeededSamples
      .samples(TermSequences.trace.resize(Size(80)), 20261116L, 8)
      .maxBy(_._2.rounds.flatten.size)
    val page = TracePageText.playerPage(
      "Generated trace",
      TraceStart.written(start, None),
      TraceText.written(trace)
    )
    assertFileSnapshot(page, "trace_page/generated_trace.html")
  }
