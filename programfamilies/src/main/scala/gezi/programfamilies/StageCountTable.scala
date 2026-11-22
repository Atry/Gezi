package gezi.programfamilies

import java.nio.file.Files
import java.nio.file.Paths

/** One count of one stage on a size family at the sizes of the migration's
  * criterion 4, 64, 128, 512 and 1,024, in that order.
  */
final case class CountGrowth(family: String, stage: String, count: String, values: Vector[Long]):
  require(values.size == 4, s"a count at the four sizes of criterion 4: $values")

  private val Vector(at64, at128, at512, at1024) = values: @unchecked

  /** The marginal count per unit of size from 64 to 128. */
  def smallMarginal: Double = (at128 - at64) / 64.0

  /** The marginal count per unit of size from 512 to 1,024. */
  def largeMarginal: Double = (at1024 - at512) / 512.0

  /** Whether the count does not change from 64 to 128 nor from 512 to
    * 1,024: the inequality then reads 0 ≤ 0.
    */
  def constant: Boolean = at64 == at128 && at512 == at1024

  /** Criterion 4, (C₁₀₂₄ − C₅₁₂)/512 ≤ 1.6 × (C₁₂₈ − C₆₄)/64, in integers:
    * 10 (C₁₀₂₄ − C₅₁₂) ≤ 128 (C₁₂₈ − C₆₄).
    */
  def holds: Boolean = 10 * (at1024 - at512) <= 128 * (at128 - at64)

  /** The line of the table: the family, the stage, the count, its four
    * values, the two marginals, their ratio (`constant` for a constant
    * count) and whether the inequality holds.
    */
  def line: String =
    Vector(
      family,
      stage,
      count,
      values.mkString("\t"),
      f"$smallMarginal%.4f",
      f"$largeMarginal%.4f",
      if constant then "constant" else f"${largeMarginal / smallMarginal}%.4f",
      if holds then "yes" else "no"
    ).mkString("\t")

/** The table of criterion 4: every stage count of the pipeline on the eight
  * size families at 64, 128, 512 and 1,024 (`Pipeline.counts`).
  */
object StageCountTable:

  /** The header of the table. */
  val header: String = Vector(
    "family",
    "stage",
    "count",
    "at_64",
    "at_128",
    "at_512",
    "at_1024",
    "marginal_64_128",
    "marginal_512_1024",
    "ratio",
    "holds"
  ).mkString("\t")

  /** The growth of every count of the family, the configuration compiled
    * once.
    */
  def growths(family: SizeFamily, compiled: CompiledConfiguration): Vector[CountGrowth] =
    val counts = Pipeline.countedSizes.map(size =>
      Pipeline.counts(compiled, family.item(size)).named
    )
    counts.transpose.map { named =>
      val (stage, count) = named.map((stage, count, _) => (stage, count)).distinct match
        case Vector(single) => single
        case different      => throw IllegalStateException(s"the sizes name the counts differently: $different")
      CountGrowth(family.family, stage, count, named.map(_._3))
    }

  /** The table of every size family, each line printed as computed. */
  def lines: Vector[String] =
    val compiled = Pipeline.sizeFamilies
      .map(_.configuration)
      .distinct
      .map(configuration => configuration.name -> Pipeline.libraryCompiled(configuration, FixedPointLines.buildRoot))
      .toMap
    Pipeline.sizeFamilies.flatMap(family =>
      growths(family, compiled(family.configuration.name)).map { growth =>
        println(growth.line)
        growth.line
      }
    )

/** `gezi.programfamilies.CriterionFourCounts <output>`: the table of criterion 4
  * written to the output file.
  */
@main def CriterionFourCounts(arguments: String*): Unit = arguments.toList match
  case output :: Nil =>
    Files.writeString(Paths.get(output), (StageCountTable.header +: StageCountTable.lines).mkString("", "\n", "\n"))
  case _ =>
    throw IllegalArgumentException("usage: CriterionFourCounts <output>")
