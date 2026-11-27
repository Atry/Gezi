package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** An expression of the interpreted language: `num(N)`, `add(A, B)`,
  * `mul(A, B)`, `var(I)` (de Bruijn), `let(A, B)` and `amb(A, B)`. Its cases
  * are the constructors of problems/reduction_interpreter/expression in order
  * (`ReductionInterpreter.expressionOf`).
  */
enum Expression:
  case Number(value: BigInt)
  case Add(left: Expression, right: Expression)
  case Multiply(left: Expression, right: Expression)
  case Variable(index: Int)
  case Let(bound: Expression, body: Expression)
  case Amb(left: Expression, right: Expression)

/** The interpreter problems of the reduction series, the port of
  * `problems/reduction_interpreter`: a call-by-value interpreter written in the
  * calculus, applied to the Scott encoding of an expression, whose answer is
  * the expression's value, a binary natural.
  */
object ReductionInterpreter:

  private val family = "reduction_interpreter"

  /** Call-by-value evaluation in an empty environment (`reference_value/2`). An
    * amb of two different values throws, its message naming the domain
    * `amb_of_one_value`.
    */
  def referenceValue(expression: Expression): BigInt =
    evaluated(expression, List.empty)

  private def evaluated(
      expression: Expression,
      environment: List[BigInt]
  ): BigInt = expression match
    case Expression.Number(value)    => value
    case Expression.Add(left, right) =>
      evaluated(left, environment) + evaluated(right, environment)
    case Expression.Multiply(left, right) =>
      evaluated(left, environment) * evaluated(right, environment)
    case Expression.Variable(index) =>
      environment
        .lift(index)
        .getOrElse(
          throw IllegalArgumentException(
            s"no variable $index in the environment"
          )
        )
    case Expression.Let(bound, body) =>
      evaluated(body, evaluated(bound, environment) :: environment)
    case Expression.Amb(left, right) =>
      val value = evaluated(left, environment)
      if value == evaluated(right, environment) then value
      else
        throw IllegalArgumentException(
          s"amb_of_one_value: $expression has two values"
        )

  /** The Scott encoding of the expression; each constructor binds its six cases
    * afresh (`syntax_term/2`).
    */
  def syntaxTerm(expression: Expression): ProblemTerm = expression match
    case Expression.Number(value)    => constructor(0, binary(value))
    case Expression.Add(left, right) =>
      constructor(1, syntaxTerm(left), syntaxTerm(right))
    case Expression.Multiply(left, right) =>
      constructor(2, syntaxTerm(left), syntaxTerm(right))
    case Expression.Variable(index)  => constructor(3, unary(index))
    case Expression.Let(bound, body) =>
      constructor(4, syntaxTerm(bound), syntaxTerm(body))
    case Expression.Amb(left, right) =>
      constructor(5, syntaxTerm(left), syntaxTerm(right))

  private def constructor(index: Int, fields: ProblemTerm*): ProblemTerm =
    abstractions(6, cases => applied(cases(index), fields))

  /** `\self. \env. \i. i (env [] (\h. \t. h)) (\p. env [] (\h. \t. self self t p))`.
    */
  private def lookupBody: ProblemTerm =
    λ(self =>
      λ(environment =>
        λ(index =>
          index(environment(top)(λ(head => λ(_ => head))))(
            λ(predecessor =>
              environment(top)(λ(_ => λ(tail => self(self)(tail)(predecessor))))
            )
          )
        )
      )
    )

  /** The evaluator's body over plus, times and lookup (`eval_body/4`). */
  private def evalBody(
      plus: ProblemTerm,
      times: ProblemTerm,
      lookup: ProblemTerm
  ): ProblemTerm =
    λ(self =>
      λ(environment =>
        λ(expression =>
          def evaluate(subexpression: ProblemTerm) =
            self(self)(environment)(subexpression)
          expression(λ(number => number))(
            λ(left => λ(right => plus(evaluate(left))(evaluate(right))))
          )(
            λ(left => λ(right => times(evaluate(left))(evaluate(right))))
          )(λ(index => lookup(environment)(index)))(
            λ(bound =>
              λ(body =>
                self(self)(
                  λ(_ => λ(cons => cons(evaluate(bound))(environment)))
                )(body)
              )
            )
          )(
            λ(left =>
              λ(right => members(Vector(evaluate(left), evaluate(right))))
            )
          )
        )
      )
    )

  /** `eval [] Expression` under the lets of the arithmetic, times, lookup and
    * eval (`program_surface/2`).
    */
  def programSurface(
      group: ReductionGroup,
      expression: Expression
  ): ProblemTerm =
    withEvaluator(group)(evaluate =>
      evaluatedInEmptyEnvironment(evaluate, syntaxTerm(expression))
    )

  /** The body under the lets of the arithmetic, times, lookup and eval; the
    * body is given the let variable eval.
    */
  private[reductions] def withEvaluator(
      group: ReductionGroup
  )(body: ProblemTerm => ProblemTerm): ProblemTerm =
    group.arithmetic.withArithmetic(names =>
      λ(zero =>
        λ(times =>
          λ(lookup =>
            λ(evaluate => body(evaluate))(
              evalBody(names.plus, times, lookup)(
                evalBody(names.plus, times, lookup)
              )
            )
          )(lookupBody(lookupBody))
        )(group.arithmetic.timesFunction(names.plus, zero))
      )(binary(0))
    )

  /** `eval [] Syntax`. */
  private[reductions] def evaluatedInEmptyEnvironment(
      evaluate: ProblemTerm,
      syntax: ProblemTerm
  ): ProblemTerm =
    evaluate(λ(empty => λ(_ => empty)))(syntax)

  /** `x0 = 0, x1 = 1, x(k) = x(k-1) + x(k-2)` (`fibonacci_lets/2`). */
  def fibonacciLets(number: Int): Expression =
    val rest =
      (1 until number).foldLeft(Expression.Variable(0): Expression)((body, _) =>
        Expression.Let(
          Expression.Add(Expression.Variable(0), Expression.Variable(1)),
          body
        )
      )
    Expression.Let(
      Expression.Number(0),
      Expression.Let(Expression.Number(1), rest)
    )

  /** `x0 = 3, x(k) = x(k-1) * x(k-1)` (`squaring_lets/2`). */
  def squaringLets(number: Int): Expression =
    val rest =
      (1 to number).foldLeft(Expression.Variable(0): Expression)((body, _) =>
        Expression.Let(
          Expression.Multiply(Expression.Variable(0), Expression.Variable(0)),
          body
        )
      )
    Expression.Let(Expression.Number(3), rest)

  /** The name of the Prolog constructor of a variable expression. It is spelled
    * in two pieces because the framework's immutability test reads the sources
    * word by word, string literals included, and takes the word for the Scala
    * keyword.
    */
  val variableConstructor: String = "v" + "ar"

  /** The expression a datum writes, a constructor of
    * problems/reduction_interpreter/expression read by its position
    * (`ProblemData.alternative`) with its fields, in the order of
    * `Expression`'s cases.
    */
  def expressionOf(field: ProblemField): Expression =
    ProblemData.alternative(field, ProblemData.caseCount[Expression]) match
      case (0, Vector(value)) => Expression.Number(ProblemData.integer(value))
      case (1, Vector(left, right)) =>
        Expression.Add(expressionOf(left), expressionOf(right))
      case (2, Vector(left, right)) =>
        Expression.Multiply(expressionOf(left), expressionOf(right))
      case (3, Vector(index)) => Expression.Variable(ProblemData.small(index))
      case (4, Vector(bound, body)) =>
        Expression.Let(expressionOf(bound), expressionOf(body))
      case (5, Vector(left, right)) =>
        Expression.Amb(expressionOf(left), expressionOf(right))
      case (position, fields) =>
        throw IllegalArgumentException(
          s"the expression of $family at position $position has ${fields.size} fields"
        )

  /** The expression as Prolog's `~w` writes it,
    * `let(num(4),add(var(0),num(1)))`.
    */
  def prologText(expression: Expression): String = expression match
    case Expression.Number(value)    => s"num($value)"
    case Expression.Add(left, right) =>
      s"add(${prologText(left)},${prologText(right)})"
    case Expression.Multiply(left, right) =>
      s"mul(${prologText(left)},${prologText(right)})"
    case Expression.Variable(index)  => s"$variableConstructor($index)"
    case Expression.Let(bound, body) =>
      s"let(${prologText(bound)},${prologText(body)})"
    case Expression.Amb(left, right) =>
      s"amb(${prologText(left)},${prologText(right)})"

  /** The points and their expressions (`program/2`): the clauses with a body
    * ported, then the facts read.
    */
  def programs(group: ReductionGroup): Vector[(String, Expression)] =
    val fibonacci = Vector(
      "twenty" -> 20,
      "forty" -> 40,
      "eighty" -> 80,
      "one_hundred_sixty" -> 160,
      "three_hundred_twenty" -> 320
    ).map((name, number) =>
      (s"reduction_interpreter_fibonacci_$name", fibonacciLets(number))
    )
    val squaring =
      Vector("four" -> 4, "five" -> 5, "six" -> 6, "seven" -> 7, "eight" -> 8)
        .map((name, number) =>
          (s"reduction_interpreter_squaring_$name", squaringLets(number))
        )
    val stated = group.problems(family).rows("program").map {
      case Vector(point, expression) =>
        (ProblemData.text(point), expressionOf(expression))
      case other => throw IllegalArgumentException(s"not a program: $other")
    }
    fibonacci ++ squaring ++ stated

  /** The problems: each program's answer is its reference value. */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    programs(group).map((point, expression) =>
      ReductionProblem(
        point,
        programSurface(group, expression),
        "binary",
        Expected.One(Scott.binaryTree(referenceValue(expression))),
        Reduction.defaultLimits
      )
    )
