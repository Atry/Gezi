package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import snapshot4s.generated.snapshotConfig

/** The points file the writer makes with member judgments from the practice
  * seed 20261031, for the repeated family `repeated_reduction_meanings` at R =
  * 1 and 2: each evaluation row followed by its judgment rows, and the programs
  * file the judgment rows refer to. Its purpose is to catch a change in the
  * rows' columns, names, families, weights, programs or order, which would
  * change a published points file.
  */
class MemberJudgmentsSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with snapshot4s.munit.SnapshotAssertions:
  /** The parts of the law families' group the draws read, built once
    * (`LawFamilies.sharedFixtures`).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures

  /** The tabling(weak_head) steps the writer reads a reference within. */
  private val writerBudget: Long = 200000

  test("the points file of the practice seed with member judgments") {
    val sources = CorpusSources.seededSources(
      LawFamilies.group,
      "repeated_reduction_meanings",
      20261031L,
      Vector(1, 2),
      "practice",
      BigDecimal(1)
    )
    val directory = Files.createTempDirectory("member-judgments")
    assertEquals(
      PointsFile
        .written(
          directory,
          sources,
          writerBudget,
          Some(JudgmentPoints(BigDecimal("0.5"), false, None))
        )
        .unwritten,
      Vector.empty
    )
    assertFileSnapshot(
      Files.readString(
        directory.resolve(PointsFile.fileName),
        StandardCharsets.UTF_8
      ),
      "judge/member_judgments_repeated_reduction_meanings.tsv"
    )
    assertFileSnapshot(
      Files.readString(
        directory.resolve(PointsFile.programsFileName),
        StandardCharsets.UTF_8
      ),
      "judge/member_judgments_repeated_reduction_meanings_programs.tsv"
    )
  }
