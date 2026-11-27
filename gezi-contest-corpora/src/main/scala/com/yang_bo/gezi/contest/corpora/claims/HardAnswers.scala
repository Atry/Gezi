package com.yang_bo.gezi.contest.corpora.claims

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemFamily

/** The answer tables of the hard corpus, the code of `problems/hard_answers`:
  * its facts (the intended answers and the roles) are read from the file,
  * together with the drawn sizes of `problems/hard_parameters`; the families
  * add their own intended answers (`HardFamily`).
  */
final class HardAnswers(corpora: Corpora, families: Vector[HardFamily]):

  private def file: ProblemFamily = corpora.contestHardAnswers

  private def atomFacts(name: String): Set[String] =
    file.rows(name).map(arguments => ProblemData.text(arguments(0))).toSet

  private def drawnSize(point: String, parameter: String): Int =
    ProblemData.small(
      corpora.contestHardParameters
        .row("drawn_size", Map(0 -> point, 1 -> parameter))(2)
    )

  /** The three rules of `hard_intended/3`: the sized points' intended naturals
    * are their drawn sizes.
    */
  private def drawnIntended: Vector[(String, Intended)] = Vector(
    "lasso_floyd_cycle_start_120" -> ("lasso_floyd_cycle_start_120", "prefix"),
    "lasso_visited_cycle_start_60" -> (
      "lasso_visited_cycle_start_60",
      "prefix"
    ),
    "stream_nth_naturals_by_map_1600" -> (
      "stream_nth_naturals_by_map_1600",
      "index"
    )
  ).map((point, size) =>
    point -> Intended(
      IntendedOutcome.Head,
      IntendedValue.NaturalValue(drawnSize(size._1, size._2))
    )
  )

  /** `hard_intended(Point, Outcome, Value)`, every clause's answer for the
    * point.
    */
  def hardIntended(point: String): Vector[Intended] =
    val facts = file.rows("hard_intended").collect {
      case arguments if ProblemData.text(arguments(0)) == point =>
        Intended(
          IntendedOutcome.read(arguments(1)),
          IntendedValue.read(arguments(2))
        )
    }
    facts ++ (drawnIntended ++ families.flatMap(_.intended)).collect {
      case (`point`, intended) => intended
    }

  /** `hard_role(Point, Role)`: none for a point with no intended answer. */
  def hardRole(point: String): Option[String] =
    if hardIntended(point).isEmpty then None
    else if atomFacts("retired")(point) then Some("retired")
    else if atomFacts("regression")(point) then Some("regression")
    else if atomFacts("control")(point) then Some("control")
    else Some("scored")
