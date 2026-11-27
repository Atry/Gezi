package com.yang_bo.gezi.jmh.pipeline

/** Laws beside `CompiledRunBenchmark`, on its two sizes of the framework's
  * fixture entry: the warmed reading of each gives one normal form; its steps
  * per level do not grow from the small size to the large one; and the steps to
  * the first head are the same at both sizes. Its purpose: a change of the
  * fixture entry's compilation or of the JIT under which a level costs more as
  * the run grows, or the loop runs before the first head, fails here, so that a
  * per-level reading of the benchmark is not taken on a run that no longer runs
  * the loop as one level's work. Steps are compared with each other, a law of
  * the reading's complexity, never with a recorded count.
  */
class CompiledRunStepsLawTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:
  /** The two runs compiled, a fixture the law reads, not its subject: forced
    * before the test and not charged to it (FailFastSuite).
    */
  private lazy val inputs: CompiledRunInputs = CompiledRunInputs()

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => inputs.small, _ => inputs.large)

  test(
    "a level of the compiled run costs no more steps at the larger size, and the first head the same"
  ) {
    // TODO: the runs with native blocks ("blocks") stand here again with those
    // runs (`CompiledRunInputs`, the TODO there).
    val Vector(small, large) = Vector(inputs.small, inputs.large).map(run =>
      val (normalForms, after) =
        CompiledRunBenchmark.read(run.entry, run.refined, run.warmed)
      val (_, afterFirstHead) = CompiledRunBenchmark.firstHead(run)
      assertEquals((run.size, normalForms.size), (run.size, 1))
      (run.size, after.budget.spent, afterFirstHead.budget.spent)
    ): @unchecked
    val (smallSize, smallSteps, smallFirstHead) = small
    val (largeSize, largeSteps, largeFirstHead) = large
    assert(smallSize < largeSize, s"the sizes $smallSize and $largeSize")
    assert(
      largeSteps * smallSize <= smallSteps * largeSize,
      s"a level costs more steps at size $largeSize ($largeSteps steps) than at size $smallSize ($smallSteps steps)"
    )
    assertEquals(largeFirstHead, smallFirstHead)
  }
