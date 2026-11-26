package gezi.contest.corpora.claims

import gezi.frontend.Term
import gezi.frontend.Term.λ

/** The points of the deleted Prolog file itself
  * (`git show 6ab16a338^:lambda_jit/corpora/contest_hard.pl`): the former JIT
  * arena's gain, regression and control points, which call into `contest`,
  * `long_runs` and `jit_witnesses` (the merge group's ports, `merges.Contest`,
  * `merges.LongRuns` and `merges.JitWitnesses`) and into
  * `problems/hard_clauses` (`HardClauses`).
  */
final class Hard(corpora: Corpora, clauses: HardClauses):

  import corpora.prelude.{cons, falseValue, fixpoint, identity, length, nil, trueValue}

  private def contest = corpora.contest

  def jitHotBodyCountDown3200: ProblemTerm =
    clauses.hotBodyCountDown(40)(clauses.numeral(clauses.drawnSize("jit_hot_body_count_down_3200", "count")))

  def jitHotCombinatorCountDown3200: ProblemTerm =
    clauses.hotCombinatorCountDown(20)(
      clauses.numeral(clauses.drawnSize("jit_hot_combinator_count_down_3200", "count")))

  def inputIndependentStretch: ProblemTerm = corpora.longRuns.inputIndependentStretch(trueValue)

  def argumentUsedTwice(point: String): ProblemTerm =
    corpora.longRuns.argumentUsedTwice(clauses.drawnSize(point, "depth"))(trueValue)

  def editDistance6: ProblemTerm = corpora.longRuns.editDistance(Vector(0, 1, 2, 0, 1, 2), Vector(1, 2, 0, 2, 1, 0), 3)

  def editDistance8: ProblemTerm =
    corpora.longRuns.editDistance(Vector(0, 1, 2, 0, 1, 2, 0, 1), Vector(1, 2, 0, 2, 1, 0, 1, 2), 4)

  def lassoFloydCycleStart120: ProblemTerm =
    contest.floydCycleStart(
      contest.lasso(
        clauses.drawnSize("lasso_floyd_cycle_start_120", "prefix"),
        clauses.drawnSize("lasso_floyd_cycle_start_120", "cycle")))

  def lassoVisitedCycleStart60: ProblemTerm =
    contest.visitedCycleStart(
      contest.lasso(
        clauses.drawnSize("lasso_visited_cycle_start_60", "prefix"),
        clauses.drawnSize("lasso_visited_cycle_start_60", "cycle")))

  def regexMatches8: ProblemTerm =
    contest.regexMatches(contest.grammarANBN)(
      contest.aNBNWord(clauses.drawnSize("regex_matches_8", "n"), Vector.empty))

  def streamNthNaturalsByMap1600: ProblemTerm =
    contest.streamNth(contest.numeral(clauses.drawnSize("stream_nth_naturals_by_map_1600", "index")))(
      contest.streamNaturalsByMap)

  /** `identity_equal`: the boolean equality of `x true` and `y true`. */
  val identityEqual: ProblemTerm =
    λ(left => λ(right => left(trueValue)(right(trueValue))(right(trueValue)(falseValue)(trueValue))))

  /** `identity_list_equal`. */
  val identityListEqual: ProblemTerm =
    fixpoint(λ(self => λ(xs => λ(ys =>
      xs(ys(trueValue)(λ(_ => λ(_ => falseValue))))(
        λ(head => λ(tail => ys(falseValue)(λ(otherHead => λ(otherTail =>
          identityEqual(head)(otherHead)(self(tail)(otherTail))(falseValue)))))))))))

  /** `identity_list(Count)`. */
  def identityList(count: Int): ProblemTerm = (1 to count).foldLeft(nil)((rest, _) => cons(identity)(rest))

  def reverseOfThree: ProblemTerm = identityListEqual(corpora.jitWitnesses.reverseOfThree)(identityList(3))

  /** The points of the former `contest_hard` module, by name. */
  def points: Map[String, () => ProblemTerm] = Map(
    "jit_hot_body_count_down_3200" -> (() => jitHotBodyCountDown3200),
    "jit_hot_combinator_count_down_3200" -> (() => jitHotCombinatorCountDown3200),
    "input_independent_stretch" -> (() => inputIndependentStretch),
    "argument_used_twice_16" -> (() => argumentUsedTwice("argument_used_twice_16")),
    "argument_used_twice_24" -> (() => argumentUsedTwice("argument_used_twice_24")),
    "edit_distance_6" -> (() => editDistance6),
    "edit_distance_8" -> (() => editDistance8),
    "lasso_floyd_cycle_start_120" -> (() => lassoFloydCycleStart120),
    "lasso_visited_cycle_start_60" -> (() => lassoVisitedCycleStart60),
    "regex_matches_8" -> (() => regexMatches8),
    "regex_rejects_medium" -> (() => contest.program("regex_rejects_medium")),
    "stream_nth_naturals_by_map_1600" -> (() => streamNthNaturalsByMap1600),
    "lasso_visited_cycle_start_medium" -> (() => contest.program("lasso_visited_cycle_start_medium")),
    "acyclic_floyd_has_cycle_medium" -> (() => contest.program("acyclic_floyd_has_cycle_medium")),
    "type_this_superclass" -> (() => contest.program("type_this_superclass")),
    "acyclic_ends_medium" -> (() => contest.program("acyclic_ends_medium")),
    "proof_infinite_finite_list" -> (() => contest.program("proof_infinite_finite_list")),
    "reverse_of_three" -> (() => reverseOfThree),
    "length_of_eight" -> (() => length(corpora.jitWitnesses.listOf(8))),
    "lasso_ends_unrolled" -> (() => contest.program("lasso_ends_unrolled")),
    "stream_all_one_unrolled" -> (() => contest.program("stream_all_one_unrolled")),
    "regex_all_prefixes_unrolled" -> (() => contest.program("regex_all_prefixes_unrolled")),
    "type_self_record_unrolled" -> (() => contest.program("type_self_record_unrolled"))
  )
