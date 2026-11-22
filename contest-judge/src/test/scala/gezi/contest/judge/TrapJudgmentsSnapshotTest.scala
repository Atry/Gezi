package gezi.contest.judge

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import gezi.contest.corpora.reductions.Reference
import gezi.frontend.Term
import snapshot4s.generated.snapshotConfig

/** The points file the writer makes with traps, its programs
  * file, and the trap
  * outcome of each evaluation point, from the practice seed 20261031 and
  * the trap seed 20261101, for the repeated family
  * `repeated_reduction_meanings` at R = 1 and 2, with two points added per
  * drawn point: the choice of its program with itself (one normal form, a
  * program that is not pure) and the choice of its program with the
  * second instance's (two normal forms when the two differ). Its purpose is
  * to catch a trap given to a program with a choice, a judgment point left
  * on a point withheld from traps, a change in which
  * reasons are reported, or a change in the rows' names, candidates,
  * expectations or order.
  */
class TrapJudgmentsSnapshotTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  /** The parts of the law families' group the draws read, built once (`LawFamilies.sharedFixtures`). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    super.sharedFixtures ++ LawFamilies.sharedFixtures


  /** The tabling(weak_head) steps the writer reads a reference within. */
  private val writerBudget: Long = 200000

  private def drawn(seed: Long): Vector[PointSource.EvaluationSource] =
    CorpusSources.seededSources(LawFamilies.group, "repeated_reduction_meanings", seed, Vector(1, 2), "practice", BigDecimal(1)).collect {
      case source: PointSource.EvaluationSource => source
    }

  /** The drawn points followed by their two choices, the second choice's
    * other member the program of the other instance's point of the same
    * name. A choice's reference is tabling(weak_head)'s reading of the choice
    * (`Reference.Read`): the drawn point's reference, computed natively
    * is the reference of its own program, not of the choice.
    */
  private def withChoices(
      instance: Vector[PointSource.EvaluationSource],
      other: Vector[PointSource.EvaluationSource]
  ): Vector[PointSource] =
    instance ++ instance.zip(other).flatMap((source, otherSource) =>
      Vector(
        source.copy(
          name = s"${source.name}/choice_with_itself",
          program = Term.Choice(source.program, source.program),
          reference = Reference.Read
        ),
        source.copy(
          name = s"${source.name}/choice_with_other",
          program = Term.Choice(source.program, otherSource.program),
          reference = Reference.Read
        )
      )
    )

  test("the points file of the practice seed with traps") {
    val first = drawn(20261031L)
    val second = drawn(20261101L)
    val directory = Files.createTempDirectory("trap-judgments")
    val writtenFile = PointsFile.written(
      directory,
      withChoices(first, second),
      writerBudget,
      Some(JudgmentPoints(BigDecimal("0.5"), false, Some(TrapDraw(withChoices(second, first), 3))))
    )
    assertEquals(writtenFile.unwritten, Vector.empty)
    assertFileSnapshot(
      writtenFile.traps.map((name, outcome) => s"$name\t${outcome.reported}").mkString("", "\n", "\n"),
      "judge/trap_outcomes_repeated_reduction_meanings.tsv"
    )
    assertFileSnapshot(
      Files.readString(directory.resolve(PointsFile.fileName), StandardCharsets.UTF_8),
      "judge/trap_judgments_repeated_reduction_meanings.tsv"
    )
    assertFileSnapshot(
      Files.readString(directory.resolve(PointsFile.programsFileName), StandardCharsets.UTF_8),
      "judge/trap_judgments_repeated_reduction_meanings_programs.tsv"
    )
  }
