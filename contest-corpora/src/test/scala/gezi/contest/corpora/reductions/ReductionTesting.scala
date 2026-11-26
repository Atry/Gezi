package gezi.contest.corpora.reductions

import java.nio.file.Path
import java.nio.file.Paths
import gezi.frontend.Lambdalattice
import gezi.frontend.Term
import gezi.weakhead.Expansions

/** The reduction group, read from Gezi's directory once for the test
  * JVM, and the lines the snapshots of the generators write
  * (`GeneratedProgramsSuite`).
  */
object ReductionTesting:

  /** Gezi's directory. */
  val root: Path = Paths.get(
    sys.props.getOrElse(
      "gezi.buildRoot",
      throw IllegalStateException("the build passes gezi.buildRoot to the forked test JVM")
    )
  )

  /** The group read from Gezi's directory. */
  lazy val group: ReductionGroup = ReductionGroup(root, Expansions.none, gezi.hotspot.baselines.BaselineCaches.provider())

  /** The form of a closed term, each closed instruction in it (a library
    * term read off a file by projection) written out as its de Bruijn term,
    * as the lambdalattice text of the tree, as `MergeTesting.form` writes it.
    */
  def form(term: Term): String =
    Lambdalattice.textWithLiterals(Encodings.deBruijn(term), Map.empty)

  /** The lines of the reduction problems, keyed
    * `reduction_problem/<point>/<field>`: the program, the type, the
    * snapshot of the expected trees and the limits, each form computed when
    * it is called.
    */
  def problemLines(group: ReductionGroup, problems: Vector[ReductionProblem]): Vector[(String, () => String)] =
    problems.flatMap(problem =>
      val point = problem.point
      Vector(
        s"reduction_problem/$point/program" -> (() => form(problem.program)),
        s"reduction_problem/$point/type" -> (() => "\"" + problem.typeName + "\""),
        s"reduction_problem/$point/snapshot" -> (() =>
          Reduction.snapshot(group.scott, problem).mkString("[", ",", "]")
        ),
        s"reduction_problem/$point/limits" -> (() =>
          val limits = problem.limits
          s"[${limits.seconds},${limits.stackMegabytes},${limits.tableMegabytes}]"
        )
      )
    )
