package gezi.contest.judge

import java.nio.file.Files

/** The probe the judge's end-to-end tests draw their small points from
  * (`SupervisorTest`, `ArticleCheckTest`, `ReuseTableTest`): each corpus
  * family's test sources and the points the points file writer wrote of them at
  * the writer's budget, a source whose reading stops within it left out.
  * Probing a family reads every one of its problems under tabling(weak_head),
  * and the three tests probed the same families at the same budget, so each
  * family is probed once per test JVM.
  */
object ProbedFamilies:

  /** The tabling(weak_head) steps the writer reads a test point's normal forms
    * within: small points only.
    */
  val writerBudget: Long = 200000

  /** A family's name, its test sources in corpus order and the points the
    * writer wrote of them within `writerBudget`, in file order.
    */
  final case class ProbedFamily(
      family: String,
      sources: Vector[PointSource],
      written: Vector[Point]
  ):

    /** The written points in the order the seed draws them
      * (`PointsFile.ordered`); fails the test unless they are one family's.
      */
    def ordered(seed: Long): Vector[Point] =
      PointsFile.ordered(written, seed) match
        case Vector((_, found)) => found
        case other              =>
          munit.Assertions.fail(s"${other.size} families in one corpus's file")

    /** The sources of the named points, in corpus order. */
    def sourcesOf(points: Vector[Point]): Vector[PointSource] =
      val names = points.map(_.name).toSet
      sources.filter(source => names.contains(source.pointName))

    /** The sources the writer wrote, in corpus order. */
    def writtenSources: Vector[PointSource] = sourcesOf(written)

  lazy val meanings: ProbedFamily = probed("contest_reduction_meanings")

  lazy val nonCanonical: ProbedFamily = probed(
    "contest_reduction_non_canonical"
  )

  private def probed(family: String): ProbedFamily =
    val sources =
      CorpusSources.sources(LawFamilies.group, family, "test", BigDecimal(1))
    val directory = Files.createTempDirectory(s"probe-$family")
    PointsFile.written(directory, sources, writerBudget)
    ProbedFamily(family, sources, PointsFile.read(directory))
