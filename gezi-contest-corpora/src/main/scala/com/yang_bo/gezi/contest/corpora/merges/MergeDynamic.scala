package com.yang_bo.gezi.contest.corpora.merges

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemFamilies

import com.yang_bo.gezi.contest.corpora.claims.Template
import com.yang_bo.gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import com.yang_bo.gezi.contest.corpora.reductions.DynamicReferences
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*

/** The variables a body under `MergeDynamic.withArithmetic` refers to the
  * Booleans and the binary operations by (`names(True, False, Plus,
  * Equality)`).
  */
final case class ArithmeticNames(
    trueValue: ProblemTerm,
    falseValue: ProblemTerm,
    plus: ProblemTerm,
    equality: ProblemTerm
)

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_dynamic.pl`; its data are
  * `problems/merge_dynamic`): dynamic programming in lambda plus choice, with
  * no label (grid paths, subset sum and the longest common subsequence), on
  * Scott Booleans, unary and binary numerals, and the curried binary arithmetic
  * let bound once at the top of a program; and the twin arithmetic, the same
  * functions with their code respelled. The pieces that are facts in the file
  * (the Booleans, the binary constructors, the bodies of equality, grid paths
  * and the longest common subsequence, the symbols) and the tables of points
  * are read from it.
  */
final class MergeDynamic(problems: ProblemFamilies):

  private val file = problems("merge_dynamic")

  /** `\t. \f. t`. */
  def trueTerm: ProblemTerm = file.program("true_term")

  /** `\t. \f. f`. */
  def falseTerm: ProblemTerm = file.program("false_term")

  /** The unary numeral `count`: `\z. \s. z` or `\z. \s. s n` (`unary/2`). */
  def unary(count: Int): ProblemTerm =
    require(count >= 0, s"a numeral is not negative: $count")
    (1 to count).foldLeft(λ(zero => λ(_ => zero)))((predecessor, _) =>
      λ(_ => λ(successor => successor(predecessor)))
    )

  /** The binary numeral `count`, least significant bit outermost: zero
    * `\z. \e. \o. z`, even `\z. \e. \o. e h`, odd `\z. \e. \o. o h`
    * (`binary/2`).
    */
  def binary(count: BigInt): ProblemTerm =
    require(count >= 0, s"a numeral is not negative: $count")
    if count == 0 then file.program("binary_zero")
    else
      val half = binary(count / 2)
      if count % 2 == 0 then file.program("binary_even", half)
      else file.program("binary_odd", half)

  /** The binary zero, `\z. \e. \o. z`. */
  def binaryZero: ProblemTerm = file.program("binary_zero")

  /** The binary numeral `2h`, `\z. \e. \o. e h`, over the half. */
  def binaryEven(half: ProblemTerm): ProblemTerm =
    file.program("binary_even", half)

  /** The binary numeral `2h + 1`, `\z. \e. \o. o h`, over the half. */
  def binaryOdd(half: ProblemTerm): ProblemTerm =
    file.program("binary_odd", half)

  /** `\self. \n. n 1 (\h. odd h) (\h. even (self self h))`. */
  private def incrementBody: ProblemTerm =
    λ(self =>
      λ(n =>
        n(binaryOdd(file.program("binary_zero")))(λ(h => binaryOdd(h)))(
          λ(g => binaryEven(self(self)(g)))
        )
      )
    )

  /** Binary addition with the carry by `increment`. */
  private def plusBody(increment: ProblemTerm): ProblemTerm =
    λ(self =>
      λ(a =>
        λ(b =>
          a(b)(
            λ(h1 =>
              b(a)(λ(k1 => binaryEven(self(self)(h1)(k1))))(
                λ(k2 => binaryOdd(self(self)(h1)(k2)))
              )
            )
          )(
            λ(h2 =>
              b(a)(λ(k3 => binaryOdd(self(self)(h2)(k3))))(
                λ(k4 => binaryEven(increment(self(self)(h2)(k4))))
              )
            )
          )
        )
      )
    )

  /** The binary increment, its body applied to itself. */
  def incrementTerm: ProblemTerm = incrementBody(incrementBody)

  /** Binary addition, its body applied to itself. */
  def plusTerm(increment: ProblemTerm): ProblemTerm =
    plusBody(increment)(plusBody(increment))

  /** Binary equality, its body applied to itself. */
  def equalityTerm(
      trueValue: ProblemTerm,
      falseValue: ProblemTerm
  ): ProblemTerm =
    file.program("equality_body", trueValue, falseValue)(
      file.program("equality_body", trueValue, falseValue)
    )

  /** `(\y. y zero (\_. even y) (\_. even y)) number`, the double of a binary
    * numeral kept canonical.
    */
  private def doubled(zero: ProblemTerm, number: ProblemTerm): ProblemTerm =
    λ(y => y(zero)(λ(_ => binaryEven(y)))(λ(_ => binaryEven(y))))(number)

  /** Binary multiplication by shifting and adding, a times b = 0 when a is 0,
    * double(h b) when a is 2h and b + double(h b) when a is 2h + 1.
    */
  private def timesBody(plus: ProblemTerm, zero: ProblemTerm): ProblemTerm =
    λ(self =>
      λ(a =>
        λ(b =>
          a(zero)(λ(h1 => doubled(zero, self(self)(h1)(b))))(
            λ(h2 => plus(b)(doubled(zero, self(self)(h2)(b))))
          )
        )
      )
    )

  /** Binary multiplication, its body applied to itself (`times_function/3`). */
  def timesFunction(plus: ProblemTerm, zero: ProblemTerm): ProblemTerm =
    timesBody(plus, zero)(timesBody(plus, zero))

  /** The body under the lets of the Booleans and the binary operations
    * (`with_arithmetic/3`).
    */
  def withArithmetic(body: ArithmeticNames => ProblemTerm): ProblemTerm =
    lets(incrementTerm, plusTerm, equalityTerm, body)

  /** The body under the lets of the Booleans and the twin operations
    * (`with_twin_arithmetic/3`).
    */
  def withTwinArithmetic(body: ArithmeticNames => ProblemTerm): ProblemTerm =
    lets(twinIncrementTerm, twinPlusTerm, twinEqualityTerm, body)

  private def lets(
      increment: ProblemTerm,
      plus: ProblemTerm => ProblemTerm,
      equality: (ProblemTerm, ProblemTerm) => ProblemTerm,
      body: ArithmeticNames => ProblemTerm
  ): ProblemTerm =
    λ(trueValue =>
      λ(falseValue =>
        λ(incrementVariable =>
          λ(plusVariable =>
            λ(equalityVariable =>
              body(
                ArithmeticNames(
                  trueValue,
                  falseValue,
                  plusVariable,
                  equalityVariable
                )
              )
            )(equality(trueValue, falseValue))
          )(plus(incrementVariable))
        )(increment)
      )(falseTerm)
    )(trueTerm)

  /** The definitional term of each of the family's APIs, closed, by name
    * (`merge_api_term/2`), which the rule-35 catalogue takes its address from.
    */
  def mergeApiTerm(name: String): ProblemTerm = name match
    case "merge_binary_increment" => incrementTerm
    case "merge_binary_plus"      =>
      λ(increment => plusTerm(increment))(incrementTerm)
    case "merge_binary_equality" =>
      λ(trueValue =>
        λ(falseValue => equalityTerm(trueValue, falseValue))(falseTerm)
      )(trueTerm)
    case "merge_binary_times" =>
      λ(increment =>
        λ(plus => λ(zero => timesFunction(plus, zero))(binary(0)))(
          plusTerm(increment)
        )
      )(
        incrementTerm
      )
    case "merge_symbols_equal" =>
      λ(trueValue =>
        λ(falseValue => symbolsEqualTerm(trueValue, falseValue))(falseTerm)
      )(trueTerm)
    case other =>
      throw IllegalArgumentException(s"$other is no API of the merge family")

  /** The names `merge_api_term/2` answers, in its order. */
  val mergeApiNames: Vector[String] = Vector(
    "merge_binary_increment",
    "merge_binary_plus",
    "merge_binary_equality",
    "merge_binary_times",
    "merge_symbols_equal"
  )

  // ---- the twin arithmetic: the same functions, their code respelled ----

  private def twinIncrementBody: ProblemTerm =
    λ(self =>
      λ(n =>
        n(binaryOdd(file.program("binary_zero")))(λ(h => binaryOdd(h)))(
          λ(g => λ(m => binaryEven(m))(self(self)(g)))
        )
      )
    )

  /** The twin increment, which makes the even of the carried half through a
    * redex.
    */
  def twinIncrementTerm: ProblemTerm = twinIncrementBody(twinIncrementBody)

  /** 2h + 2k = 2(h + k), 2h + 2k + 1 = 2(h + k) + 1 and 2h + 1 + 2k + 1 = 2((h
    * + 1) + k), casing on the second operand first.
    */
  private def twinPlusBody(increment: ProblemTerm): ProblemTerm =
    λ(self =>
      λ(a =>
        λ(b =>
          b(a)(
            λ(k1 =>
              a(b)(λ(h1 => binaryEven(self(self)(h1)(k1))))(
                λ(h2 => binaryOdd(self(self)(h2)(k1)))
              )
            )
          )(
            λ(k2 =>
              a(b)(λ(h3 => binaryOdd(self(self)(h3)(k2))))(
                λ(h4 => binaryEven(self(self)(increment(h4))(k2)))
              )
            )
          )
        )
      )
    )

  /** The twin addition, its body applied to itself. */
  def twinPlusTerm(increment: ProblemTerm): ProblemTerm =
    twinPlusBody(increment)(twinPlusBody(increment))

  /** The twin equality, which cases on its second operand first. */
  def twinEqualityTerm(
      trueValue: ProblemTerm,
      falseValue: ProblemTerm
  ): ProblemTerm =
    file.program("twin_equality_body", trueValue, falseValue)(
      file.program("twin_equality_body", trueValue, falseValue)
    )

  /** a times b = 0 when b is 0, double(a k) when b is 2k and a + double(a k)
    * when b is 2k + 1.
    */
  private def twinTimesBody(plus: ProblemTerm, zero: ProblemTerm): ProblemTerm =
    λ(self =>
      λ(a =>
        λ(b =>
          b(zero)(λ(k1 => doubled(zero, self(self)(a)(k1))))(
            λ(k2 => plus(a)(doubled(zero, self(self)(a)(k2))))
          )
        )
      )
    )

  /** The twin multiplication, its body applied to itself
    * (`twin_times_function/3`).
    */
  def twinTimesFunction(plus: ProblemTerm, zero: ProblemTerm): ProblemTerm =
    twinTimesBody(plus, zero)(twinTimesBody(plus, zero))

  // ---- grid paths ----

  /** `paths(r, c) = paths(r - 1, c) + paths(r, c - 1)`, 1 on an edge, its body
    * applied to itself (`grid_function/3`).
    */
  def gridFunction(plus: ProblemTerm, one: ProblemTerm): ProblemTerm =
    file.program("grid_body", plus, one)(file.program("grid_body", plus, one))

  /** The Church Boolean of `paths(size, size) == claimed` (`grid_term/3`). */
  def gridTerm(size: Int, claimed: BigInt): ProblemTerm =
    withArithmetic(names =>
      λ(one =>
        λ(grid =>
          names.equality(grid(unary(size))(unary(size)))(binary(claimed))
        )(
          gridFunction(names.plus, one)
        )
      )(binary(1))
    )

  /** The grid points, each with its size and claimed count (`grid_point/3`). */
  val gridPoints: Vector[(String, Int, BigInt)] =
    file
      .rows("grid_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          ProblemData.small(arguments(1)),
          ProblemData.integer(arguments(2))
        )
      )

  /** Whether the grid point's claim holds, by the reference. */
  def gridValue(point: String): Template =
    val (_, size, claimed) = gridPoint(point)
    ClaimFact.boolean(
      claimed == DynamicReferences.referenceGridPaths(size, size)
    )

  private def gridPoint(point: String): (String, Int, BigInt) =
    gridPoints
      .find(_._1 == point)
      .getOrElse(throw IllegalArgumentException(s"$point is no grid point"))

  // ---- subset sum ----

  /** The Church Boolean of "some subset of the items sums to the target": the
    * let of each level's search, the last level first, each merging leaving its
    * item out and taking it (`subset_term/3`).
    */
  def subsetTerm(items: Vector[BigInt], target: BigInt): ProblemTerm =
    withArithmetic(names =>
      def level(index: Int, next: ProblemTerm): ProblemTerm =
        val search = λ(accumulated =>
          choice(
            next(accumulated),
            next(names.plus(accumulated)(binary(items(index))))
          )
        )
        if index == 0 then λ(first => first(binary(0)))(search)
        else λ(current => level(index - 1, current))(search)
      val last = λ(accumulated => names.equality(accumulated)(binary(target)))
      if items.isEmpty then λ(first => first(binary(0)))(last)
      else λ(next => level(items.length - 1, next))(last)
    )

  /** The subset points, each with its count of items (`subset_point/2`). */
  val subsetPoints: Vector[(String, Int)] =
    file
      .rows("subset_point")
      .map(arguments =>
        (ProblemData.text(arguments(0)), ProblemData.small(arguments(1)))
      )

  // ---- longest common subsequence ----

  private def symbolTerm(symbol: Char): ProblemTerm =
    file.row("symbol_term", Map(0 -> symbol.toString)) match
      case Vector(_, program) => ProblemData.program(program, Vector.empty)
      case other => throw IllegalArgumentException(s"not a symbol term: $other")

  /** The Scott list of the symbols: `\n. \c. n` or `\n. \c. c h t`
    * (`list_term/2`).
    */
  def listTerm(symbols: Vector[Char]): ProblemTerm =
    symbols.foldRight(λ(empty => λ(_ => empty)))((symbol, tail) =>
      λ(_ => λ(nonEmpty => nonEmpty(symbolTerm(symbol))(tail)))
    )

  /** `\x. \y. x (y true false) (y false true)`. */
  def symbolsEqualTerm(
      trueValue: ProblemTerm,
      falseValue: ProblemTerm
  ): ProblemTerm =
    file.program("symbols_equal_term", trueValue, falseValue)

  private def lcsFunction(
      trueValue: ProblemTerm,
      falseValue: ProblemTerm,
      symbolsEqual: ProblemTerm
  ): ProblemTerm =
    file.program("lcs_body", trueValue, falseValue, symbolsEqual)(
      file.program("lcs_body", trueValue, falseValue, symbolsEqual)
    )

  /** The Church Boolean of "the strings have a common subsequence of length
    * need" (`lcs_term/4`).
    */
  def lcsTerm(left: Vector[Char], right: Vector[Char], need: Int): ProblemTerm =
    withArithmetic(names =>
      λ(symbolsEqual =>
        λ(lcs => lcs(listTerm(left))(listTerm(right))(unary(need)))(
          lcsFunction(names.trueValue, names.falseValue, symbolsEqual)
        )
      )(symbolsEqualTerm(names.trueValue, names.falseValue))
    )

  /** The longest common subsequence points, each with its length
    * (`lcs_point/2`).
    */
  val lcsPoints: Vector[(String, Int)] =
    file
      .rows("lcs_point")
      .map(arguments =>
        (ProblemData.text(arguments(0)), ProblemData.small(arguments(1)))
      )

  // ---- the points and their claims ----

  /** The program of each point of the file, by name. */
  def program(point: String): ProblemTerm =
    gridPoints
      .find(_._1 == point)
      .map((_, size, claimed) => gridTerm(size, claimed))
      .orElse(
        subsetPoints
          .find(_._1 == point)
          .map((_, count) =>
            val items = DynamicReferences.subsetItems(count).map(BigInt(_))
            subsetTerm(items, items.sum)
          )
      )
      .orElse(
        lcsPoints
          .find(_._1 == point)
          .map((_, length) =>
            val (left, right, need) = DynamicReferences.lcsPointStrings(length)
            lcsTerm(left, right, need)
          )
      )
      .getOrElse(
        throw IllegalArgumentException(
          s"$point is no point of contest_merge_dynamic"
        )
      )

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    gridPoints.flatMap((point, size, claimed) =>
      val count = DynamicReferences.referenceGridPaths(size, size)
      val template = gridValue(point)
      ClaimFact.headPoint(point, template) :+ ScoredFiniteHead(
        point,
        Vector(template),
        s"paths($size, $size) = $count, so paths($size, $size) == $claimed is ${ClaimFact.text(template)}: the recursion makes finitely many calls on smaller unary numerals, each one binary addition, and the binary equality compares bit by bit, so the check reaches the Church Boolean of the equation in finitely many head reductions"
      )
    ) ++ subsetPoints.flatMap((point, count) =>
      val items = DynamicReferences.subsetItems(count).map(BigInt(_))
      val target = items.sum
      assert(
        DynamicReferences
          .referenceSubsetSums(items.map(_.toInt))
          .last == target,
        s"the sum of every item of $point is its greatest subset sum"
      )
      ClaimFact.headPoint(point, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        point,
        Vector(ClaimFact.boolean(true)),
        s"$target is the sum of all of the items ${items.mkString("[", ",", "]")}, reached by the branch that takes every item: n finite binary additions, then the binary equality, and choosing that branch at every merge yields the Church true in finitely many head reductions"
      )
    ) ++ lcsPoints.flatMap((point, length) =>
      val (left, right, need) = DynamicReferences.lcsPointStrings(length)
      ClaimFact.headPoint(point, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        point,
        Vector(ClaimFact.boolean(true)),
        s"${MergeDynamic.symbols(left)} and ${MergeDynamic.symbols(right)} have a common subsequence of length $need (the reference's table); following its matches through the three-way merge reaches need zero in at most ${2 * length} finite steps, whose value is the Church true"
      )
    )

/** Writing the strings of the family. */
object MergeDynamic:

  /** The string as the Prolog list of its symbols, `[a,b,a]`. */
  def symbols(string: Vector[Char]): String = string.mkString("[", ",", "]")
