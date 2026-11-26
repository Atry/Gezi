package gezi.contest.judge

import java.nio.file.Files
import gezi.frontend.DeBruijnTerm
import gezi.frontend.ExchangeText
import gezi.frontend.Term
import snapshot4s.generated.snapshotConfig

/** The judge end to end: the supervisor reads the tabling(weak_head) reference and
  * the framework's fixture entry (`contest-entries-fixture`), under the
  * published reference times, on points the writer put in a points
  * file, and writes the table. Its purpose is to catch a broken pipe protocol, a
  * misjudged outcome (an evaluation's set against its reference, a
  * judgment's proved against member and not_member), a family not read
  * consecutively or a table missing its setup rows or its columns.
  *
  * The points are generated: the problems of two small corpus families,
  * ordered by the seed, the first two of each that tabling(weak_head) reads within
  * the writer's budget (`ProbedFamilies`), and, for each family's first
  * problem, two judgment points, one whose candidate is a normal form of
  * the problem (member) and one whose candidate is a normal form of the
  * other family's first problem (not member, since tabling(weak_head)'s reading of
  * the problem is complete). The points each reader judged are a snapshot,
  * and every row's outcome is checked to be its verdict (`success` for an
  * evaluation, `proved` for a member's judgment, `refuted` for a trap's) or
  * `stopped`. Whether a point stops depends on wall time: a stop is no
  * verdict, so it misjudges nothing, and the supervisor's `setup` row after
  * it, the reader's JVM started again, comes and goes with it, so neither is
  * in the snapshot (measured 2026-11-19: the fixture entry's
  * `reduction_even_count_five_hundred_twelve`, stopped when the snapshot was
  * recorded, answered within its budget on main). The fixture entry's JVM
  * runs in the sandbox, the supervisor's default (`Sandbox`), so the
  * snapshot also shows the fixture answering correctly inside it.
  */
class SupervisorTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of SupervisorTest, then reading the deleted baseline entry, takes 63.654 s; the bound is 1.5 times that rounded up to 5 s. On the fixture entry, 2026-11-17 on 4 CPUs (contest.slice, CPUs 4 to 7, nice 10), the 1-minute load about 10: 18.3 s.
  // Reason: it runs the judge supervisor end to end, starting real JVMs.
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(100, "s")

  private val seed = 20261031L

  test("the supervisor reads tabling(weak_head) and the fixture entry on the points file") {
    assume(TestSandbox.unavailable.isEmpty, TestSandbox.unavailable.getOrElse(""))
    val directory = Files.createTempDirectory("judge-points")
    val evaluations = Vector(ProbedFamilies.meanings, ProbedFamilies.nonCanonical).map(probed =>
      (probed, probed.sourcesOf(probed.ordered(seed).take(2)))
    )
    val firstNormalForm = evaluations.map((probed, chosen) =>
      val source = chosen.headOption.getOrElse(fail(s"no point of ${probed.family} within the writer's budget"))
      val first = probed.written.find(_.name == source.pointName).getOrElse(fail(s"no written point ${source.pointName}"))
      first.question match
        case Question.Evaluation(reference) => (probed.family, source, reference.toVector.map(line).min)
        case other                          => fail(s"$other")
    )
    val judgments = firstNormalForm.zip(firstNormalForm.reverse).flatMap { case ((family, source, member), (_, _, other)) =>
      val program = source match
        case PointSource.EvaluationSource(_, _, _, _, found, _, _) => found
        case other                                              => fail(s"$other")
      Vector(
        PointSource.JudgmentSource(s"${source.pointName}_member", "test", family, BigDecimal(1), program, term(member), true),
        PointSource.JudgmentSource(s"${source.pointName}_not_member", "test", family, BigDecimal(1), program, term(other), false)
      )
    }
    val pointsDirectory = directory.resolve("points")
    assertEquals(PointsFile.written(pointsDirectory, evaluations.flatMap(_._2) ++ judgments, ProbedFamilies.writerBudget), Vector.empty)
    val output = directory.resolve("table.tsv")
    val familyReferences = PublishedReferences.written(directory, evaluations.map(_._1.family))
    val rows = SupervisorCommand.run(
      Map(
        "entry" -> "fixture",
        "points" -> pointsDirectory.toString,
        "seed" -> seed.toString,
        "references" -> "tabling(weak_head)",
        "family-references" -> familyReferences.toString,
        "setup-limit" -> "300",
        "budget-cap" -> "300",
        "slice" -> "none",
        "cores" -> "any",
        "output" -> output.toString
      )
    )
    val table = Files.readString(output)
    // The seed, points, programs, build and family references lines, the
    // header, then one line a row.
    assertEquals(table.split('\n').toVector.size, rows.size + 6)
    val judged = rows.filter(_.point != "setup")
    assertFileSnapshot(
      judged.map(row => Vector(row.point, row.reader, row.family, row.kind, row.cores).mkString("\t")).mkString("\n"),
      "judge/supervisor_points.tsv"
    )
    val misjudged = judged.filterNot(row => row.outcome == Outcome.Stopped.written || row.outcome == verdict(row))
    assertEquals(misjudged.map(row => (row.point, row.reader, row.outcome)), Vector.empty)
  }

  /** The outcome a row's point is to be judged with: an evaluation's
    * `success`, a member's judgment `proved`, a trap's `refuted`.
    */
  private def verdict(row: Row): String =
    if row.kind == "evaluation" then Outcome.Success.written
    else if row.point.endsWith("_not_member") then Outcome.Refuted.written
    else if row.point.endsWith("_member") then Outcome.Proved.written
    else fail(s"a row of no known kind: $row")

  private def line(term: DeBruijnTerm): String = ExchangeText.line(gezi.frontend.Defunctionalization.thunkInstruction(term)(using gezi.ir.NoFacts))

  /** The HOAS term of a closed pure de Bruijn term. */
  private def term(text: String): Term =
    hoas(gezi.frontend.Defunctionalization.instructionTerm(ExchangeText.term(text).getOrElse(fail(s"no term: $text"))), Vector.empty)

  private def hoas(term: DeBruijnTerm, bound: Vector[Term]): Term = term match
    case DeBruijnTerm.Variable(index)           => bound(bound.size - 1 - index)
    case DeBruijnTerm.Lambda(body)              => Term.λ(variable => hoas(body, bound :+ variable))
    case DeBruijnTerm.Apply(function, argument) => hoas(function, bound)(hoas(argument, bound))
    case DeBruijnTerm.Choice(left, right)       => Term.Choice(hoas(left, bound), hoas(right, bound))
    case DeBruijnTerm.Parallel(left, right)     => Term.Parallel(hoas(left, bound), hoas(right, bound))
    case DeBruijnTerm.Constant(instruction)          => fail(s"a constant $instruction in a point")
    case DeBruijnTerm.Free(name)                => fail(s"a free name $name in a point")
