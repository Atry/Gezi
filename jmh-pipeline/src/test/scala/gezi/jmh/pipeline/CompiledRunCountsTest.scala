package gezi.jmh.pipeline

import snapshot4s.generated.snapshotConfig

/** The deterministic counts beside `CompiledRunBenchmark`: for each size,
  * the normal forms and the evaluator steps of the timed reading, from the
  * warmed JIT state. Its purpose: a change of the fixture entry's compilation or
  * of the JIT that changes what the benchmark reads or how many steps a
  * level takes shows in the snapshot's diff, so that a per-level reading is
  * not taken on a run that no longer runs the loop natively.
  */
class CompiledRunCountsTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:
  // Measured 2026-11-17 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load about 10, on the framework's fixture entry: "compiledRunCounts" takes 6.1 s (38.4 s on 2026-11-16 on the deleted baseline entry's route); the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  test("compiledRunCounts") {
    val inputs = CompiledRunInputs()
    // TODO: the counts of the runs with native blocks ("blocks") stand here
    // again with those runs (`CompiledRunInputs`, the TODO there).
    val counts = Vector(("machine", inputs.small), ("machine", inputs.large)).flatMap((mode, run) =>
      val (normalForms, after) = CompiledRunBenchmark.read(run.entry, run.refined, run.warmed)
      val (_, afterFirstHead) = CompiledRunBenchmark.firstHead(run)
      Vector(
        s"${run.size}\t$mode\tnormal forms\t${normalForms.size}",
        s"${run.size}\t$mode\tsteps of the warmed reading\t${after.budget.spent}",
        s"${run.size}\t$mode\tsteps to the first head\t${afterFirstHead.budget.spent}"
      )
    )
    assertFileSnapshot(counts.mkString("", "\n", "\n"), "compiled_run/counts.tsv")
  }
