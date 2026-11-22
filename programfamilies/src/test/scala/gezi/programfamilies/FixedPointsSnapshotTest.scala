package gezi.programfamilies

import gezi.generatedinputs.ProgramGenerators
import gezi.generatedinputs.SeededSamples
import snapshot4s.generated.snapshotConfig

/** The fixed points the saturation reaches on items of the configurations'
  * program families drawn from a fixed seed (`ProgramGenerators.anyItem`,
  * `SeededSamples`), one line per drawn item as `ItemRun.line` writes it:
  * configuration, item, End, classes, live nodes and the digest of the
  * fixed point's form. Its purpose: catch a change in the saturation's
  * fixed points on the program families, a run that no longer reaches its
  * fixed point within the budget included. Sizes above 256 (the 512 and
  * 1024 of the deleted FixedPointsSlowTest) are exercised by no test since
  * 9a43e75c6; the coverage items are not drawn, and only
  * `InputAgreementTest` checks them, by their inputs.
  *
  * It runs within munit's default timeout of 30 s: MEASURED 2026-11-13, the
  * test alone on CPUs 0 and 1 (`taskset -c 0,1`, the build's forked JVM of
  * -Xmx304m), 14.8 s, 14.9 s and 19.8 s in three runs.
  */
class FixedPointsSnapshotTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of FixedPointsSnapshotTest, "the fixed points of drawn program family items", takes 53.164 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(80, "s")

  test("the fixed points of drawn program family items") {
    val drawn = SeededSamples.samples(
      ProgramGenerators.anyItem(FixedPointsSnapshotTest.largestSize),
      FixedPointsSnapshotTest.seed,
      FixedPointsSnapshotTest.count
    )
    val lines = drawn.map((family, item) =>
      FixedPointRuns.run(CompiledConfigurations.byName(family.configuration.name), item).line(family.configuration.name)
    )
    assertFileSnapshot(lines.mkString("\n") + "\n", "fixed_points/drawn_program_family_items.tsv")
  }

object FixedPointsSnapshotTest:

  /** The seed the items are drawn from. */
  val seed: Long = 20261113L

  /** The number of items drawn. */
  val count: Int = 32

  /** The largest size an item is drawn at, the largest size of the tier the
    * default `test` ran before this test replaced it (256).
    */
  val largestSize: Int = 256
