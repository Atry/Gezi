package gezi.contest.corpora.claims

import gezi.contest.corpora.common.ProblemData

import gezi.frontend.Term
import gezi.frontend.Term.λ

/** The qualifying points, the code of
  * the deleted Prolog file
  * (`git show 6ab16a338^:lambda_jit/corpora/contest_qualifying_clauses.pl`, included by
  * the module `contest_qualifying`): common list and stream programs at sizes that
  * take plain weak head reduction a few hundred milliseconds.
  */
final class Qualifying(corpora: Corpora, clauses: HardClauses):

  import corpora.prelude.{append, fixpoint, identity, length, map, naturalEqual, nil, successor, trueValue, zero}

  private def contest = corpora.contest

  def lengthOfMap(count: Int): Term =
    naturalEqual(length(map(successor)(clauses.zerosList(count))))(contest.numeral(count))

  def appendLength(count: Int): Term =
    naturalEqual(length(append(clauses.zerosList(count))(clauses.zerosList(count))))(contest.numeral(2 * count))

  def reverseTwice(count: Int): Term =
    naturalEqual(clauses.listHead(clauses.listReverse(clauses.listReverse(contest.labelsList(1 to count, nil)))))(
      contest.numeral(1))

  def allZero(count: Int): Term = contest.everyElementIs(zero)(clauses.zerosList(count))

  def hotLoop(rounds: Int): Term =
    val heavy = λ(k => corpora.longRuns.churchNumeral(256)(identity)(k))
    fixpoint(λ(self => λ(m => m(identity)(λ(m1 => heavy(self(m1)))))))(contest.numeral(rounds))(trueValue)

  def streamNth(count: Int): Term =
    naturalEqual(contest.streamNth(contest.numeral(count))(contest.streamNaturalsByMap))(contest.numeral(count))

  def sum(count: Int): Term =
    val total = fixpoint(λ(self => λ(items => items(zero)(λ(item => λ(rest => clauses.naturalPlus(item)(self(rest))))))))
    naturalEqual(total(contest.labelsList(1 to count, nil)))(contest.numeral(count * (count + 1) / 2))

  /** The points of `contest_qualifying`, by name. */
  def points: Map[String, () => Term] = Map(
    "qualifying_length_of_map" -> (() => lengthOfMap(700)),
    "qualifying_append_length" -> (() => appendLength(400)),
    "qualifying_reverse_twice" -> (() => reverseTwice(400)),
    "qualifying_all_zero" -> (() => allZero(1000)),
    "qualifying_hot_loop" -> (() => hotLoop(120)),
    "qualifying_stream_nth" -> (() => streamNth(60)),
    "qualifying_sum" -> (() => sum(20))
  )
