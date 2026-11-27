package gezi.contest.judge

import java.nio.file.Files
import java.nio.file.Path

/** The published reference times the end-to-end tests give the supervisor
  * (`--family-references`, `FamilyReferences`), which every pass requires.
  */
object PublishedReferences:

  /** The reference time of every family in the tests: with the default multiple
    * of 20 its budget is 300 s, the cap the tests give (`--budget-cap 300`).
    */
  val seconds: Double = 15.0

  /** The file of the families' reference times, each `seconds`, written in the
    * directory; its path.
    */
  def written(directory: Path, families: Vector[String]): Path =
    val path = directory.resolve("family-references.tsv")
    Files.createDirectories(directory)
    Files.writeString(
      path,
      ("# family\tseconds" +: families.distinct.map(family =>
        s"$family\t$seconds"
      )).mkString("", "\n", "\n")
    )
    path
