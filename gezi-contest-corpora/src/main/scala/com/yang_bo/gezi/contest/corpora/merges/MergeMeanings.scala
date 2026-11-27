package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies

import com.yang_bo.gezi.contest.corpora.claims.Template
import com.yang_bo.gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_meanings.pl`; its data are
  * `problems/merge_meanings`): the count of the even numbers below 2^k, by the
  * `is_even`, `count` and `upto` of `problems/reduction_meanings`, compared
  * with a claimed unary numeral. The bodies of `double` and `equal` and the
  * table of points are read from the file, and the bodies of `is_even`, `count`
  * and `upto`, which are facts of `problems/reduction_meanings`, from that
  * family.
  */
final class MergeMeanings(problems: ProblemFamilies):

  private val file = problems("merge_meanings")

  private val meanings = problems("reduction_meanings")

  /** `double` applied `times` times to `one` (`doubled_on/4`). */
  private def doubledOn(
      times: Int,
      double: ProblemTerm,
      one: ProblemTerm
  ): ProblemTerm =
    (1 to times).foldLeft(one)((inner, _) => double(inner))

  /** 2^exponent + extra built from `trueValue` at run time: `extra` successors
    * over the doubling of one (`claimed_on/5`).
    */
  private def claimedOn(
      exponent: Int,
      extra: Int,
      double: ProblemTerm,
      trueValue: ProblemTerm
  ): ProblemTerm =
    (1 to extra).foldLeft(
      doubledOn(exponent, double, λ(_ => λ(successor => successor(trueValue))))
    )((inner, _) => λ(_ => λ(successor => successor(inner))))

  /** The Church Boolean of `count (upto 2^exponent true) true = 2^(exponent -
    * 1) + extra` under the lets of true, false, not, is_even, count, upto,
    * double and equal (`count_test_surface/3`).
    */
  def countTestSurface(exponent: Int, extra: Int): ProblemTerm =
    require(exponent >= 1, s"the exponent is at least 1: $exponent")
    λ(trueValue =>
      λ(falseValue =>
        λ(not =>
          λ(isEven =>
            λ(count =>
              λ(upto =>
                λ(double =>
                  λ(equal =>
                    equal(
                      count(
                        upto(
                          doubledOn(
                            exponent,
                            double,
                            λ(_ => λ(successor => successor(trueValue)))
                          )
                        )(trueValue)
                      )(trueValue)
                    )(
                      claimedOn(exponent - 1, extra, double, trueValue)
                    )
                  )(
                    file.program("equal_body", trueValue, falseValue)(
                      file.program("equal_body", trueValue, falseValue)
                    )
                  )
                )(
                  file.program("double_body", trueValue)(
                    file.program("double_body", trueValue)
                  )
                )
              )(meanings.program("upto_body")(meanings.program("upto_body")))
            )(
              meanings.program("count_body", isEven)(
                meanings.program("count_body", isEven)
              )
            )
          )(
            meanings.program("is_even_body", trueValue, not)(
              meanings.program("is_even_body", trueValue, not)
            )
          )
        )(λ(boolean => boolean(falseValue)(trueValue)))
      )(λ(_ => λ(second => second)))
    )(λ(first => λ(_ => first)))

  /** The points, each with its exponent and the extra of its claim
    * (`count_point/3`).
    */
  val points: Vector[(String, Int, Int)] =
    file
      .rows("count_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          ProblemData.small(arguments(1)),
          ProblemData.small(arguments(2))
        )
      )

  /** The point's program. */
  def program(name: String): ProblemTerm =
    points
      .find(_._1 == name)
      .map((_, exponent, extra) => countTestSurface(exponent, extra))
      .getOrElse(
        throw IllegalArgumentException(
          s"$name is no point of contest_merge_meanings"
        )
      )

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, exponent, extra) =>
      val template: Template = ClaimFact.boolean(extra == 0)
      val n = BigInt(2).pow(exponent)
      val evens = n / 2
      ClaimFact.headPoint(name, template) :+ ScoredFiniteHead(
        name,
        Vector(template),
        s"among 0, ..., ${n - 1} there are $evens even numbers, and the claim is ${evens + extra}, so the equation is ${ClaimFact.text(template)}: upto makes $n numerals, is_even of each takes finitely many steps, the count is a unary numeral of depth $evens, and the unary equality compares $evens successors before it answers a Church Boolean, all in finitely many head reductions"
      )
    )
