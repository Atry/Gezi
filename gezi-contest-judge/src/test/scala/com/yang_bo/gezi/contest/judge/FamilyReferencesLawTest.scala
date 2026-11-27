package com.yang_bo.gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The laws of the published reference times (`FamilyReferences`): a file
  * written gives back each family's seconds, and a points file with a family
  * the file does not give is refused. Its purpose is to catch a reader that
  * sets a family's budget from another family's time, or that lets a family
  * without a published time fall back to some default.
  */
class FamilyReferencesLawTest extends GeneratedProperties:

  private val family: Gen[String] = Gen.string(Gen.lower, Range.linear(1, 12))

  /** Seconds with at most three decimals, above zero. */
  private val seconds: Gen[Double] =
    Gen.long(Range.linear(1L, 120000L)).map(_ / 1e3)

  private val entry: Gen[(String, Double)] =
    for
      name <- family
      time <- seconds
    yield (name, time)

  private def written(references: Map[String, Double]): java.nio.file.Path =
    val path = Files.createTempFile("family-references", ".tsv")
    Files.writeString(
      path,
      ("# family\tseconds" +: references.toVector.map((name, time) =>
        s"$name\t$time"
      )).mkString("", "\n", "\n")
    )
    path

  property("a file written gives back each family's seconds") {
    for references <- entry.list(Range.linear(1, 20)).map(_.toMap).forAll
    yield Result.diff(
      FamilyReferences.read(written(references), references.keys.toVector),
      references
    )(_ == _)
  }

  property("a family the file does not give is refused") {
    for
      references <- entry.list(Range.linear(0, 20)).map(_.toMap).forAll
      absent <- family.filter(name => !references.contains(name)).forAll
    yield
      intercept[IllegalArgumentException](
        FamilyReferences.read(
          written(references),
          references.keys.toVector :+ absent
        )
      )
      Result.success
  }
