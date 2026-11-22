package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemFamilies

import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of `gezi/corpora/case_two_clauses.pl`, which `case_two.pl`
  * includes: two symbols that refer to each other through one fixpoint over
  * a pair, the unbounded judge that visits them forever, three bounded
  * judges and the consumer `all_seen`. `down` is a program of the directory
  * `gezi/problems/case_two_clauses` and is read from it.
  */
final class CaseTwo(problems: ProblemFamilies, prelude: Prelude):

  private val file = problems("case_two_clauses")

  import prelude.{cons, first, fixpoint, identity, konstant, nil, pair, second, trueValue}

  /** The tree and the forest symbol, tied through one fixpoint over a pair
    * (`tree_forest/1`).
    */
  def treeForest: Term =
    fixpoint(λ(symbols =>
      pair(λ(treeContinuation => treeContinuation(identity)(second(symbols))))(
        λ(forestContinuation => forestContinuation(konstant)(first(symbols)))
      )
    ))

  /** `first tree_forest` (`tree_symbol/1`). */
  def treeSymbol: Term = first(treeForest)

  /** `second tree_forest` (`forest_symbol/1`). */
  def forestSymbol: Term = second(treeForest)

  /** A symbol's down neighbour (`down/1`). */
  def down: Term = file.program("down")

  /** What a judge records per visited subject (`seen/1`). */
  def seen: Term = identity

  /** The unbounded judge (`judge/1`). */
  def judge: Term = fixpoint(λ(judgeVariable => λ(subject => cons(seen)(judgeVariable(down(subject))))))

  /** `judge tree_symbol` (`unbounded/1`). */
  def unbounded: Term = judge(treeSymbol)

  /** The judge of zero down steps (`judge_zero/1`). */
  def judgeZero: Term = λ(_ => cons(seen)(nil))

  /** The judge of one down step (`judge_one/1`). */
  def judgeOne: Term = λ(subject => cons(seen)(judgeZero(down(subject))))

  /** The judge of two down steps (`judge_two/1`). */
  def judgeTwo: Term = λ(subject => cons(seen)(judgeOne(down(subject))))

  /** `all_seen xs`: nil answers true, cons h t recurses on t (`all_seen/1`). */
  def allSeen: Term = fixpoint(λ(function => λ(list => list(trueValue)(λ(_ => λ(tail => function(tail)))))))

  /** The points, in the order `case_two.pl` exports them. */
  val points: Vector[(String, () => Term)] = Vector(
    "tree_forest" -> (() => treeForest),
    "tree_symbol" -> (() => treeSymbol),
    "forest_symbol" -> (() => forestSymbol),
    "down" -> (() => down),
    "seen" -> (() => seen),
    "judge" -> (() => judge),
    "unbounded" -> (() => unbounded),
    "judge_zero" -> (() => judgeZero),
    "judge_one" -> (() => judgeOne),
    "judge_two" -> (() => judgeTwo),
    "judge_zero_verdict" -> (() => judgeZero(treeSymbol)),
    "judge_one_verdict" -> (() => judgeOne(treeSymbol)),
    "judge_two_verdict" -> (() => judgeTwo(treeSymbol)),
    "all_seen" -> (() => allSeen),
    "all_seen_unbounded" -> (() => allSeen(unbounded)),
    "all_seen_judge_two" -> (() => allSeen(judgeTwo(treeSymbol)))
  )

/** The port of `gezi/corpora/hidden_growth_clauses.pl`, which
  * `hidden_growth.pl` includes: recursions whose argument keeps its value
  * but grows its spelling inside a constructor's field.
  */
final class HiddenGrowth(prelude: Prelude):

  import prelude.{fixpoint, identity}

  private def wrap: Term = λ(value => λ(continuation => continuation(value)))

  private def unwrap: Term = λ(box => box(λ(value => value)))

  /** `f p = f (wrap (identity (unwrap p)))`, from `f (wrap v0)`
    * (`growth_in_a_field/1`).
    */
  def growthInAField: Term =
    fixpoint(λ(self => λ(argument => self(wrap(identity(unwrap(argument)))))))(wrap(identity))

  /** `f p = f (wrap (wrap (identity (unwrap (unwrap p)))))`, from
    * `f (wrap (wrap v0))` (`growth_in_a_field_of_a_field/1`).
    */
  def growthInAFieldOfAField: Term =
    fixpoint(λ(self => λ(argument => self(wrap(wrap(identity(unwrap(unwrap(argument)))))))))(wrap(wrap(identity)))

  /** The points, in the order `hidden_growth.pl` exports them. */
  val points: Vector[(String, () => Term)] = Vector(
    "growth_in_a_field" -> (() => growthInAField),
    "growth_in_a_field_of_a_field" -> (() => growthInAFieldOfAField)
  )

/** The port of `gezi/corpora/witnesses_clauses.pl`, which
  * `witnesses.pl` includes: the separation witnesses of pairs of settings.
  * `omega` and `self_application` are programs of the directory
  * `gezi/problems/witnesses_clauses` and are read from it.
  */
final class Witnesses(problems: ProblemFamilies, prelude: Prelude):

  private val file = problems("witnesses_clauses")

  import prelude.{fixpoint, identity, konstant}

  /** `(\a. a a) (\b. b b)` (`omega/1`). */
  def omega: Term = file.program("omega")

  /** The points, in the order `witnesses.pl` exports them. */
  val points: Vector[(String, () => Term)] = Vector(
    "omega" -> (() => omega),
    "argument_ignored" -> (() => λ(_ => λ(x => x))(omega)),
    "self_application" -> (() => file.program("self_application")),
    "applied_identity" -> (() => identity(identity)),
    "growing_argument" -> (() => fixpoint(λ(recursive => λ(x => recursive(identity(x)))))(konstant))
  )

/** The port of `gezi/corpora/jit_witnesses_clauses.pl`, which
  * `jit_witnesses.pl` includes: what a JIT backed by an interpreter must
  * decide as that interpreter does.
  */
final class JitWitnesses(prelude: Prelude, caseTwo: CaseTwo):

  import prelude.{cons, fixpoint, identity, konstant, nil, pair, successor, zero}

  /** A Scott list of `count` identities (`list_of/2`). */
  def listOf(count: Int): Term = (1 to count).foldLeft(nil)((rest, _) => cons(identity)(rest))

  /** `reverse xs acc` on a list of three (`reverse_of_three/1`). */
  def reverseOfThree: Term =
    fixpoint(λ(self => λ(list => λ(accumulated =>
      list(accumulated)(λ(head => λ(tail => self(tail)(cons(head)(accumulated)))))
    ))))(listOf(3))(nil)

  /** The points, in the order `jit_witnesses.pl` exports them. */
  val points: Vector[(String, () => Term)] = Vector(
    "data_dispatch" -> (() =>
      fixpoint(λ(recursive => λ(x => recursive(x(λ(a => λ(b => pair(a)(b))))))))(pair(identity)(konstant))
    ),
    "unknown_function" -> (() =>
      λ(function => λ(x => fixpoint(λ(recursive => λ(y => recursive(function(y)))))(x)))(identity)(konstant)
    ),
    "bounded_judge_of_omega" -> (() =>
      caseTwo.allSeen(
        fixpoint(λ(self => λ(n => λ(x => n(nil)(λ(m => cons(caseTwo.seen)(self(m)(caseTwo.down(x)))))))))(
          successor(successor(zero))
        )(λ(a => a(a))(λ(b => b(b))))
      )
    ),
    "reverse_of_three" -> (() => reverseOfThree),
    "length_of_one" -> (() => prelude.length(listOf(1))),
    "length_of_two" -> (() => prelude.length(listOf(2))),
    "length_of_four" -> (() => prelude.length(listOf(4))),
    "length_of_eight" -> (() => prelude.length(listOf(8)))
  )

/** The port of `gezi/corpora/long_runs_clauses.pl`, which
  * `long_runs.pl` includes: points whose runs are tens of thousands of
  * contractions.
  */
final class LongRuns(prelude: Prelude):

  import prelude.{cons, fixpoint, identity, naturalAtLeast, naturalEqual, nil, successor, zero}

  /** `\f. \x. f (f (... x))`, `count` times (`church_numeral/2`). */
  def churchNumeral(count: Int): Term =
    λ(function => λ(x => (1 to count).foldLeft(x)((body, _) => function(body))))

  /** The Scott numeral `count` (`numeral_of/2`). */
  def numeralOf(count: Int): Term =
    require(count >= 0, s"a numeral is not negative: $count")
    (1 to count).foldLeft(zero)((rest, _) => successor(rest))

  /** `loop n = n done (\m. heavy (loop m))`, `heavy k = church identity k`,
    * over the numeral 200 (`input_independent_stretch/1`).
    */
  def inputIndependentStretch: Term =
    val heavy = λ(k => churchNumeral(256)(identity)(k))
    fixpoint(λ(self => λ(m => m(identity)(λ(m1 => heavy(self(m1)))))))(numeralOf(200))

  /** `twice n = n done (\m. (\y. y y) (twice m))` over the numeral
    * `depth` (`argument_used_twice/2`).
    */
  def argumentUsedTwice(depth: Int): Term =
    fixpoint(λ(self => λ(n => n(identity)(λ(m => λ(y => y(y))(self(m)))))))(numeralOf(depth))

  /** `min x y = at_least x y y x` (`minimum/1`). */
  private def minimum: Term = λ(x => λ(y => naturalAtLeast(x)(y)(y)(x)))

  /** The Levenshtein distance of the two lists of numerals compared with
    * the expected numeral (`edit_distance/4`).
    */
  def editDistance(left: Seq[Int], right: Seq[Int], expected: Int): Term =
    val distance = fixpoint(λ(self => λ(a => λ(b =>
      a(prelude.length(b))(λ(headA => λ(tailA =>
        b(prelude.length(a))(λ(headB => λ(tailB =>
          naturalEqual(headA)(headB)(self(tailA)(tailB))(
            successor(minimum(self(tailA)(tailB))(minimum(self(tailA)(b))(self(a)(tailB))))
          )
        )))
      )))
    ))))
    naturalEqual(distance(numeralList(left))(numeralList(right)))(numeralOf(expected))

  private def numeralList(integers: Seq[Int]): Term =
    integers.foldRight(nil)((integer, rest) => cons(numeralOf(integer))(rest))
