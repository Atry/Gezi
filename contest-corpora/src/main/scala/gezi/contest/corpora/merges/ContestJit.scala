package gezi.contest.corpora.merges

import gezi.contest.corpora.claims
import gezi.frontend.Term

/** The port of the deleted Prolog file (`git show
  * 6ab16a338^:lambda_jit/corpora/contest_jit.pl`): the JIT arena's points, one
  * program each. Twenty-four points delegate to the former `contest_hard`
  * module, which names their programs and fixes their parameters (the claims
  * group's port, `claims.Hard` and `claims.HardClauses`); the six regression
  * points not carried over keep their own bodies, the programs of the contest
  * corpus of the same names (`Contest`).
  */
final class ContestJit(
    contest: Contest,
    hard: claims.Hard,
    clauses: claims.HardClauses
):

  private def fromHard(name: String): (String, () => ProblemTerm) =
    name -> (() =>
      hard.points
        .get(name)
        .orElse(clauses.points.get(name))
        .getOrElse(
          throw IllegalStateException(s"contest_hard.pl has no point $name")
        )()
    )

  private def fromContest(name: String): (String, () => ProblemTerm) =
    name -> (() => contest.program(name))

  private val pointTerms: Vector[(String, () => ProblemTerm)] = Vector(
    fromHard("input_independent_stretch"),
    fromHard("jit_hot_body_count_down_3200"),
    fromHard("jit_hot_combinator_count_down_3200"),
    fromHard("jit_hot_compose_count_down"),
    fromHard("argument_used_twice_16"),
    fromHard("argument_used_twice_24"),
    fromHard("edit_distance_6"),
    fromHard("edit_distance_8"),
    fromHard("lasso_floyd_cycle_start_120"),
    fromHard("lasso_visited_cycle_start_60"),
    fromHard("regex_matches_8"),
    fromHard("regex_rejects_medium"),
    fromHard("stream_nth_naturals_by_map_1600"),
    fromHard("lasso_visited_cycle_start_medium"),
    fromContest("lasso_ends_large"),
    fromContest("type_self_record"),
    fromContest("type_abstract_stack"),
    fromContest("type_binary_method_renamed"),
    fromContest("proof_evens_large"),
    fromContest("stream_mutual_all_one"),
    fromHard("acyclic_floyd_has_cycle_medium"),
    fromHard("type_this_superclass"),
    fromHard("acyclic_ends_medium"),
    fromHard("proof_infinite_finite_list"),
    fromHard("reverse_of_three"),
    fromHard("length_of_eight"),
    fromHard("lasso_ends_unrolled"),
    fromHard("stream_all_one_unrolled"),
    fromHard("regex_all_prefixes_unrolled"),
    fromHard("type_self_record_unrolled")
  )

  /** The points, in the order the deleted `contest_jit` module exported them.
    */
  def points: Vector[String] = pointTerms.map(_._1)

  /** The point's program. */
  def program(name: String): ProblemTerm =
    pointTerms
      .find(_._1 == name)
      .map(_._2())
      .getOrElse(
        throw IllegalArgumentException(s"$name is no point of contest_jit.pl")
      )
