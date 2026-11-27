package gezi.contest.corpora.merges

import gezi.frontend.Term
import snapshot4s.generated.snapshotConfig

/** The snapshot of `problems/mixin_datalog`, whose purpose is to catch a
  * generator change that alters a point's program, a tuple's program or a claim
  * fact: the program of every point (`point(<name>)`); for every distinct
  * program the points name over at most three constants, the program of each
  * head relation of its rules at every pair of its constants
  * (`datalog_surface(Program,Relation,First,Second)`); and the claim lines.
  * Also the port of the deleted Prolog test's (`git show
  * d32e69ff0^:lambda_jit/tests/contest_mixin_datalog.plt`) test that needs no
  * evaluation.
  */
class MixinDatalogTest
    extends MergeProblemsSuite
    with snapshot4s.munit.SnapshotAssertions:

  private val datalog = MixinDatalog(MergeTesting.problems, MixinFamily.library)

  /** The largest number of constants of a program whose tuples the snapshot
    * records, so that their count, the square of it, stays small.
    */
  private val largestConstantCount = 3

  private def points: Vector[(String, () => Term)] =
    datalog.points.map((name, _, _, _, _, _) =>
      s"point($name)" -> (() => datalog.pointTerm(name))
    )

  private def tuples: Vector[(String, () => Term)] =
    datalog.points
      .map((_, programName, _, _, _, _) =>
        MixinDatalog.programKind(programName).written -> programName
      )
      .distinctBy(_._1)
      .flatMap((written, programName) =>
        val program = datalog.program(programName)
        if program.constants.length > largestConstantCount then Vector.empty
        else
          for
            relation <- program.rules.map(_.head).distinct
            first <- program.constants
            second <- program.constants
          yield s"datalog_surface($written,$relation,$first,$second)" ->
            (() => datalog.datalogSurface(program, relation, first, second))
      )

  test("the points' and the small programs' tuples' programs") {
    assertFileSnapshot(
      GeneratedProgramLines.programs(points ++ tuples),
      "generated_programs/contest_mixin_datalog.txt"
    )
  }

  test("the points' claims") {
    assertFileSnapshot(
      GeneratedProgramLines.claims(datalog.claims),
      "generated_claims/contest_mixin_datalog.txt"
    )
  }

  test("everyPointPosesADerivedTuple") {
    datalog.points.foreach((name, programName, relation, first, second, _) =>
      assert(
        datalog.referenceHolds(
          datalog.program(programName),
          relation,
          first,
          second
        ),
        name
      )
      datalog.pointTerm(name)
    )
  }
