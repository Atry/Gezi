package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of the options a pass cannot do without, each checked before the
  * pass reads anything. A pass missing `--slice` or `--cores`
  * (`SupervisorCommand.placement`), whatever other options it gives, throws
  * with a message naming both: its purpose is to catch a default creeping
  * back, since a practice command that left them out ran on the judge's cores
  * during a round. A pass with its placement but no `--family-references`
  * (`SupervisorCommand.familyReferencesOption`) throws with a message naming
  * the option and saying that the budgets go by the published reference
  * times: its purpose is to catch a pass that sets the families' budgets from
  * anything else.
  */
class PlacementOptionLawTest extends GeneratedProperties:

  private val placementOptions: Gen[Map[String, String]] =
    Gen.element1(Map.empty, Map("slice" -> "none"), Map("cores" -> "any"), Map("slice" -> "contest-judge.slice"), Map("cores" -> "8,9"))

  private val completePlacement: Gen[Map[String, String]] =
    Gen.element1(Map("slice" -> "none", "cores" -> "any"), Map("slice" -> "contest-judge.slice", "cores" -> "8,9"))

  private val otherOptions: Gen[Map[String, String]] =
    Gen.element1(
      Map.empty,
      Map("entry" -> "fixture", "points" -> "no-such-directory", "seed" -> "1", "setup-limit" -> "300", "output" -> "no-such-table.tsv")
    )

  property("a pass missing --slice or --cores throws naming both") {
    for
      placement <- placementOptions.forAll
      other <- otherOptions.forAll
    yield
      val thrown = intercept[IllegalArgumentException](SupervisorCommand.run(other ++ placement))
      Result.assert(thrown.getMessage.contains("--slice") && thrown.getMessage.contains("--cores"))
  }

  property("a pass missing --family-references throws naming it and the published reference times") {
    for
      placement <- completePlacement.forAll
      other <- otherOptions.forAll
    yield
      val thrown = intercept[IllegalArgumentException](SupervisorCommand.run(other ++ placement))
      Result.assert(thrown.getMessage.contains("--family-references") && thrown.getMessage.contains("published reference times"))
  }
