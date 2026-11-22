package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies

import gezi.contest.corpora.claims.Template
import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The port of the deleted Prolog file
  * (`git show 91b3f11e1^:lambda_jit/corpora/contest_merge_fibonacci.pl`; its data are
  * `problems/merge_fibonacci`): fib(n) by
  * the doubly recursive definition on a unary n with binary sums, compared
  * with a claimed number. The body of the recursion and the table of points
  * are read from the family's directory, `gezi/problems/merge_fibonacci`.
  */
final class MergeFibonacci(problems: ProblemFamilies, dynamic: MergeDynamic):

  private val file = problems("merge_fibonacci")

  /** fib(n) by iteration, the expected algorithm (`reference_fibonacci/2`). */
  def referenceFibonacci(n: Int): BigInt =
    require(n >= 0, s"fib takes no negative number: $n")
    (1 to n).foldLeft((BigInt(0), BigInt(1)))((pair, _) => (pair._2, pair._1 + pair._2))._1

  /** `\self. \n. n 0 (\p. p 1 (\q. plus (self self p) (self self q)))`
    * applied to itself (`fibonacci_function/4`).
    */
  def fibonacciFunction(plus: Term, zero: Term, one: Term): Term =
    file.program("fibonacci_body", plus, zero, one)(file.program("fibonacci_body", plus, zero, one))

  /** The Church Boolean of `fib(n) == claimed` (`fibonacci_term/3`). */
  def fibonacciTerm(n: Int, claimed: BigInt): Term =
    dynamic.withArithmetic(names =>
      λ(zero =>
        λ(one =>
          λ(fibonacci => names.equality(fibonacci(dynamic.unary(n)))(dynamic.binary(claimed)))(
            fibonacciFunction(names.plus, zero, one)
          )
        )(dynamic.binary(1))
      )(dynamic.binary(0))
    )

  /** The points, each with its n and claimed number (`fibonacci_point/3`). */
  val points: Vector[(String, Int, BigInt)] =
    file.rows("fibonacci_point").map(arguments =>
      (
        ProblemData.text(arguments(0)),
        ProblemData.small(arguments(1)),
        ProblemData.integer(arguments(2))
      )
    )

  /** The point's n and claimed number. */
  def point(name: String): (Int, BigInt) =
    points
      .find(_._1 == name)
      .map((_, n, claimed) => (n, claimed))
      .getOrElse(throw IllegalArgumentException(s"$name is no point of contest_merge_fibonacci"))

  /** The point's program. */
  def program(name: String): Term =
    val (n, claimed) = point(name)
    fibonacciTerm(n, claimed)

  /** The intended value of the point's program (`fibonacci_value/2`). */
  def value(name: String): Template =
    val (n, claimed) = point(name)
    ClaimFact.boolean(claimed == referenceFibonacci(n))

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, n, claimed) =>
      val template = value(name)
      val fibonacci = referenceFibonacci(n)
      ClaimFact.headPoint(name, template) :+ ScoredFiniteHead(
        name,
        Vector(template),
        s"fib($n) = $fibonacci, so fib($n) == $claimed is ${ClaimFact.text(template)}: the recursion makes finitely many calls on smaller unary numerals, each one binary addition, and the binary equality compares bit by bit, so the check reaches the Church Boolean of the equation in finitely many head reductions"
      )
    )
