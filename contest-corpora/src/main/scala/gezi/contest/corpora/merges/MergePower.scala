package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_merge_power.pl`; its data are
  * `problems/merge_power`): base^k by k
  * binary multiplications, with the original or the twin arithmetic of
  * `MergeDynamic`, compared with the true power. The body of the recursion,
  * the base and the table of points are read from the family's directory,
  * `gezi/problems/merge_power`.
  */
final class MergePower(problems: ProblemFamilies, dynamic: MergeDynamic):
  import MergePower.PowerArithmetic

  private val file = problems("merge_power")

  /** The base of every point (`base/1`). */
  val base: BigInt = file.rows("base") match
    case Vector(Vector(value)) => ProblemData.integer(value)
    case several => throw IllegalArgumentException(s"contest_merge_power has ${several.length} bases")

  /** The Church Boolean of `base^exponent == claimed`, with the original or
    * the twin arithmetic (`power_term/4`).
    */
  def powerTerm(arithmetic: PowerArithmetic, exponent: Int, claimed: BigInt): ProblemTerm = arithmetic match
    case PowerArithmetic.Original =>
      dynamic.withArithmetic(names =>
        powerBodyTerm(exponent, claimed, names.equality, zero => dynamic.timesFunction(names.plus, zero))
      )
    case PowerArithmetic.Twin =>
      dynamic.withTwinArithmetic(names =>
        powerBodyTerm(exponent, claimed, names.equality, zero => dynamic.twinTimesFunction(names.plus, zero))
      )

  private def powerBody(times: ProblemTerm, base: ProblemTerm, one: ProblemTerm): ProblemTerm =
    file.program("power_body", times, base, one)

  private def powerBodyTerm(exponent: Int, claimed: BigInt, equality: ProblemTerm, timesTerm: ProblemTerm => ProblemTerm): ProblemTerm =
    λ(zero =>
      λ(one =>
        λ(times =>
          λ(baseVariable =>
            λ(power => equality(power(dynamic.unary(exponent)))(dynamic.binary(claimed)))(
              powerBody(times, baseVariable, one)(powerBody(times, baseVariable, one))
            )
          )(dynamic.binary(base))
        )(timesTerm(zero))
      )(dynamic.binary(1))
    )(dynamic.binary(0))

  /** The points, each with its arithmetic and exponent (`power_point/3`),
    * the arithmetic a constructor of problems/merge_power/arithmetic read
    * by its position (`ProblemData.alternative`).
    */
  val points: Vector[(String, PowerArithmetic, Int)] =
    file.rows("power_point").map(arguments =>
      (
        ProblemData.text(arguments(0)),
        ProblemData.alternative(arguments(1), PowerArithmetic.values.size) match
          case (position, Vector()) => PowerArithmetic.fromOrdinal(position)
          case (_, fields)          => throw IllegalArgumentException(s"an arithmetic of contest_merge_power has ${fields.size} fields"),
        ProblemData.small(arguments(2))
      )
    )

  /** The point's program. */
  def program(name: String): ProblemTerm =
    points
      .find(_._1 == name)
      .map((_, arithmetic, exponent) => powerTerm(arithmetic, exponent, base.pow(exponent)))
      .getOrElse(throw IllegalArgumentException(s"$name is no point of contest_merge_power"))

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, arithmetic, exponent) =>
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"$base^$exponent = ${base.pow(exponent)}, computed by $exponent multiplications with the ${arithmetic.written} arithmetic, each a finite recursion on finite binary numerals, and the binary equality compares bit by bit, so the check reaches the Church true in finitely many head reductions"
      )
    )

object MergePower:

  /** The arithmetic of a point, the constructors of
    * problems/merge_power/arithmetic in order: the original arithmetic of
    * `MergeDynamic`, and its twin. `written` is the arithmetic's name in the
    * claims' prose, not a key of the data.
    */
  enum PowerArithmetic(val written: String):
    case Original extends PowerArithmetic("original")
    case Twin extends PowerArithmetic("twin")
