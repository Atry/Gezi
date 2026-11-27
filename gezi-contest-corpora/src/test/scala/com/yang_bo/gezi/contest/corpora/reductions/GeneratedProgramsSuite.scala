package com.yang_bo.gezi.contest.corpora.reductions

import snapshot4s.generated.snapshotConfig

/** A suite that records the lines a corpus file's Scala generators write,
  * `key<TAB>form`, ordered by key, as the snapshot
  * `generated_programs/<file>.txt`, so that a change of a generator that alters
  * a line shows in the snapshot's diff.
  */
abstract class GeneratedProgramsSuite(file: String)
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:

  /** The URI expansions every family of the reduction group the generators read
    * shares (`ProblemFamilies.sharedExpansions`), which the first reading of
    * any family forces, built once for the suites.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures :+ (_ =>
      ReductionTesting.group.problems.sharedExpansions
    )

  /** The lines the Scala generators write, each form computed when it is
    * called.
    */
  def generated(group: ReductionGroup): Vector[(String, () => String)]

  test(s"$file: the generated programs") {
    val lines = generated(ReductionTesting.group)
    val keys = lines.map(_._1)
    assert(
      keys.distinct.size == keys.size,
      s"the generators write a key twice in $file"
    )
    val text = lines
      .sortBy(_._1)
      .map((key, form) => s"$key\t${form()}")
      .mkString("", "\n", "\n")
    assertFileSnapshot(text, s"generated_programs/$file.txt")
  }
