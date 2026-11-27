package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** One value with several meanings, the port of `problems/reduction_meanings`:
  * the value the program let binds as True means true at boolean and zero at
  * unary, and the count of the even numbers among 0 .. n - 1 is read at unary.
  */
object ReductionMeanings:

  private val family = "reduction_meanings"

  /** `\self. \x. x True (\p. not (self self p))`. */
  private def isEvenBody(
      trueValue: ProblemTerm,
      not: ProblemTerm
  ): ProblemTerm =
    λ(self =>
      λ(number =>
        number(trueValue)(λ(predecessor => not(self(self)(predecessor))))
      )
    )

  /** The count of the elements the predicate holds of, on an accumulator. */
  private def countBody(isEven: ProblemTerm): ProblemTerm =
    λ(self =>
      λ(list =>
        λ(accumulator =>
          list(accumulator)(
            λ(head =>
              λ(tail =>
                self(self)(tail)(
                  isEven(head)(λ(_ => λ(successor => successor(accumulator))))(
                    accumulator
                  )
                )
              )
            )
          )
        )
      )
    )

  /** `\self. \k. \x. k nil (\p. cons x (self self p (successor x)))`. */
  private def uptoBody: ProblemTerm =
    λ(self =>
      λ(count =>
        λ(start =>
          count(λ(nil => λ(_ => nil)))(
            λ(predecessor =>
              λ(_ =>
                λ(cons =>
                  cons(start)(
                    self(self)(predecessor)(
                      λ(_ => λ(successor => successor(start)))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The unary numeral built on the variable, successor after successor
    * (`numeral_on/3`).
    */
  private def numeralOn(number: Int, zero: ProblemTerm): ProblemTerm =
    if number == 0 then zero
    else λ(_ => λ(successor => successor(numeralOn(number - 1, zero))))

  /** `count (upto N True) True` under the lets of True, False, not, is_even,
    * count and upto (`count_surface/2`).
    */
  def countSurface(number: Int): ProblemTerm =
    withDefinitions(definitions =>
      counted(definitions, numeral(definitions, number))
    )

  /** The let variables a count is written over. */
  private[reductions] final case class Definitions(
      trueValue: ProblemTerm,
      count: ProblemTerm,
      upto: ProblemTerm
  )

  /** The body under the lets of True, False, not, is_even, count and upto. */
  private[reductions] def withDefinitions(
      body: Definitions => ProblemTerm
  ): ProblemTerm =
    λ(trueValue =>
      λ(falseValue =>
        λ(not =>
          λ(isEven =>
            λ(count =>
              λ(upto => body(Definitions(trueValue, count, upto)))(
                uptoBody(uptoBody)
              )
            )(
              countBody(isEven)(countBody(isEven))
            )
          )(isEvenBody(trueValue, not)(isEvenBody(trueValue, not)))
        )(λ(boolean => boolean(falseValue)(trueValue)))
      )(λ(_ => λ(otherwise => otherwise)))
    )(λ(chosen => λ(_ => chosen)))

  /** `count (upto Numeral True) True`. */
  private[reductions] def counted(
      definitions: Definitions,
      numeral: ProblemTerm
  ): ProblemTerm =
    definitions.count(definitions.upto(numeral)(definitions.trueValue))(
      definitions.trueValue
    )

  /** The unary numeral of the number built on the let variable True. */
  private[reductions] def numeral(
      definitions: Definitions,
      number: Int
  ): ProblemTerm = numeralOn(number, definitions.trueValue)

  /** The problems: the count of n has (n + 1) / 2 evens (`problem/2`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("problem").map {
      case Vector(point, number) =>
        val count = ProblemData.small(number)
        ReductionProblem(
          ProblemData.text(point),
          countSurface(count),
          "unary",
          Expected.One(Scott.unaryTree((count + 1) / 2)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a problem: $other")
    }
