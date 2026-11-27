package gezi.contest.corpora.claims

import gezi.contest.corpora.merges
import gezi.frontend.Term
import gezi.frontend.Term.λ

/** A Boolean circuit of the tautology family, the formulas of
  * `contest_tautology:circuit/3`: `variable(Index)` (from 1), `not`, `and`,
  * `or` and `exclusive`.
  */
enum Formula:
  case Variable(index: Int)
  case Not(formula: Formula)
  case And(left: Formula, right: Formula)
  case Or(left: Formula, right: Formula)
  case Exclusive(left: Formula, right: Formula)

/** Building formulas as the Prolog builds them. */
object Formula:

  /** `folded(Connective, Formulas)`: the connective folded to the right over
    * the formulas, one formula itself. Throws for no formula.
    */
  def folded(
      connective: (Formula, Formula) => Formula,
      formulas: Seq[Formula]
  ): Formula =
    if formulas.isEmpty then throw IllegalArgumentException("nothing to fold")
    else formulas.init.foldRight(formulas.last)(connective)

  /** `variables(Low, High)`: the variables Low to High. */
  def variables(low: Int, high: Int): Vector[Formula] =
    Vector.range(low, high + 1).map(Variable(_))

/** The encoding of the tautology family, the deleted Prolog file (`git show
  * 6ab16a338^:lambda_jit/corpora/contest_tautology.pl`): the connectives, a
  * circuit over an environment of variables, and the point that enumerates
  * every assignment, over the prelude's Booleans.
  */
final class Tautology(prelude: merges.Prelude):

  import prelude.{falseValue, trueValue}

  /** `not b = b false true`. */
  val negation: ProblemTerm = λ(boolean => boolean(falseValue)(trueValue))

  /** `and a b = a b false`. */
  val conjunction: ProblemTerm = λ(left => λ(right => left(right)(falseValue)))

  /** The prelude's `or`. */
  val disjunction: ProblemTerm = prelude.or

  /** `exclusive a b = a (not b) b`. */
  val exclusive: ProblemTerm =
    λ(left => λ(right => left(negation(right))(right)))

  /** `every_assignment f = and (f true) (f false)`. */
  val everyAssignment: ProblemTerm =
    λ(function => conjunction(function(trueValue))(function(falseValue)))

  /** The connectives by their names in the deleted Prolog file (`git show
    * 6ab16a338^:lambda_jit/corpora/contest_tautology.pl`).
    */
  val connectives: Map[String, ProblemTerm] = Map(
    "negation" -> negation,
    "conjunction" -> conjunction,
    "disjunction" -> disjunction,
    "exclusive" -> exclusive,
    "every_assignment" -> everyAssignment
  )

  /** `circuit(Formula, Environment)`: the variable `variable(Index)` is the
    * Index-th of the environment, from 1. Throws for an index outside it.
    */
  def circuit(formula: Formula, environment: Vector[ProblemTerm]): ProblemTerm =
    formula match
      case Formula.Variable(index) =>
        environment
          .lift(index - 1)
          .getOrElse(throw IllegalArgumentException(s"no variable $index"))
      case Formula.Not(inner)       => negation(circuit(inner, environment))
      case Formula.And(left, right) =>
        conjunction(circuit(left, environment))(circuit(right, environment))
      case Formula.Or(left, right) =>
        disjunction(circuit(left, environment))(circuit(right, environment))
      case Formula.Exclusive(left, right) =>
        exclusive(circuit(left, environment))(circuit(right, environment))

  /** `quantified(Count, Formula)`: `every_assignment (\x1. ... every_assignment
    * (\xCount. C) ...)`, C the circuit over x1 ... xCount.
    */
  def quantified(count: Int, formula: Formula): ProblemTerm =
    quantifiedFrom(count, Vector.empty, formula)

  private def quantifiedFrom(
      remaining: Int,
      bound: Vector[ProblemTerm],
      formula: Formula
  ): ProblemTerm =
    if remaining == 0 then circuit(formula, bound)
    else
      everyAssignment(
        λ(variable => quantifiedFrom(remaining - 1, bound :+ variable, formula))
      )
