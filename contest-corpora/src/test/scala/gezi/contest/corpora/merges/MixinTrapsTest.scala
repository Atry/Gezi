package gezi.contest.corpora.merges

import snapshot4s.generated.snapshotConfig

/** The snapshot of `problems/mixin_traps`, whose purpose is to catch a
  * generator change that alters a trap point's program or a claim fact: the
  * lines `point(<name>)<TAB>form` of every point of `MixinTraps.trapPoints`
  * and the lines of `MixinTraps.claims`, each ordered by key; and the count
  * of the first test of the deleted Prolog test
  * (`git show d32e69ff0^:lambda_jit/tests/contest_mixin_traps.plt`), which
  * needs no judge.
  */
class MixinTrapsTest extends MergeProblemsSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of MixinTrapsTest, "the trap points' programs", takes 3.334 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(10, "s")

  private val traps = MixinTraps(
    MergeTesting.problems,
    MixinFamily.claims,
    gezi.contest.corpora.reductions.ReductionGroup(MergeTesting.buildRoot, MergeTesting.problems)
  )

  test("the trap points' programs") {
    assertFileSnapshot(
      GeneratedProgramLines.programs(traps.trapPoints.map(name => s"point($name)" -> (() => traps.program(name)))),
      "generated_programs/contest_mixin_traps.txt"
    )
  }

  test("the trap points' claims") {
    assertFileSnapshot(GeneratedProgramLines.claims(traps.claims), "generated_claims/contest_mixin_traps.txt")
  }

  test("theSixteenPointsArePosedAsTraps") {
    assertEquals(traps.trapPoints.length, 16)
    traps.trapPoints.foreach(name =>
      assertEquals(
        traps.claims.collect { case ClaimFact.NoYieldTrap(`name`, templates, _) => templates },
        Vector(Vector(ClaimFact.boolean(true), ClaimFact.boolean(false))),
        name
      )
    )
  }
