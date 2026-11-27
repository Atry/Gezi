package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import gezi.generatedinputs.GeneratedProperties

/** The laws of the seed options (`SupervisorCommand.seed`): a seed file whose
  * first line is a number gives the seed `--seed` gives for that number,
  * whatever lines follow, and giving both options throws. Its purpose is to
  * catch a seed file read other than by its first line (a round ordered by
  * another seed than the one whose hash was published), or a command line that
  * silently prefers one of two seeds.
  */
class SeedOptionLawTest extends GeneratedProperties:

  private val seeds: Gen[Long] =
    Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue))

  private val followingLines: Gen[List[String]] =
    Gen
      .element1("", "# the round's seed", "12345", " ")
      .list(Range.linear(0, 3))

  private def seedFile(seed: Long, following: List[String]): String =
    val file = Files.createTempFile("judge-seed", ".txt")
    Files.writeString(file, (seed.toString :: following).mkString("\n"))
    file.toString

  property("a seed file gives the seed of its first line") {
    for
      seed <- seeds.forAll
      following <- followingLines.forAll
    yield Result.diff(
      SupervisorCommand.seed(Map("seed-file" -> seedFile(seed, following))),
      SupervisorCommand.seed(Map("seed" -> seed.toString))
    )(_ == _)
  }

  property("giving both a seed and a seed file throws") {
    for
      seed <- seeds.forAll
      other <- seeds.forAll
    yield
      intercept[IllegalArgumentException](
        SupervisorCommand.seed(
          Map("seed" -> seed.toString, "seed-file" -> seedFile(other, Nil))
        )
      )
      Result.success
  }
