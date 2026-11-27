package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*
import scala.annotation.tailrec

/** A parameter of a repeated variant and the nominal range a seed draws its
  * values from.
  */
final case class NominalParameter(name: String, range: Range.Inclusive)

/** The nominal ranges of a repeated variant: the repetitions R a program may be
  * asked for, and the ranges its function and its inputs are drawn from.
  */
final case class NominalRanges(
    repetitions: Range.Inclusive,
    parameters: Vector[NominalParameter]
)

/** Draws from the linear congruential sequence of the corpora
  * (`DynamicReferences.nextRandom`), an immutable state: each draw returns the
  * value and the draws after it, so the values depend on the seed alone.
  */
final case class Draws(state: Long):

  /** A number of the range, read from bits 16 to 30 of the next state. */
  def number(range: Range.Inclusive): (Int, Draws) =
    require(
      range.nonEmpty && range.size <= Draws.highBitsCount,
      s"no number is drawn from $range"
    )
    val after = Draws(DynamicReferences.nextRandom(state))
    (range.start + ((after.state >> 16) % range.size).toInt * range.step, after)

  /** One of the choices. */
  def chosen[Choice](choices: Vector[Choice]): (Choice, Draws) =
    val (index, after) = number(0 to choices.size - 1)
    (choices(index), after)

  /** `count` distinct values of the draw, in the order drawn; a value drawn
    * again is drawn anew. Throws when 100 draws per value give no new one.
    */
  def distinct[Value](count: Int)(
      draw: Draws => (Value, Draws)
  ): (Vector[Value], Draws) =
    distinctFrom(count, draw, this, Vector.empty, 0)

  @tailrec
  private def distinctFrom[Value](
      count: Int,
      draw: Draws => (Value, Draws),
      draws: Draws,
      found: Vector[Value],
      attempts: Int
  ): (Vector[Value], Draws) =
    if found.size == count then (found, draws)
    else if attempts > 100 * count then
      throw IllegalArgumentException(
        s"$attempts draws gave only ${found.size} of $count distinct values"
      )
    else
      val (value, after) = draw(draws)
      distinctFrom(
        count,
        draw,
        after,
        if found.contains(value) then found else found :+ value,
        attempts + 1
      )

/** The draws from a seed. */
object Draws:

  /** The count of the values bits 16 to 30 of a state take. */
  val highBitsCount: Int = 1 << 15

  /** The draws whose state is the seed modulo 2^31. */
  def fromSeed(seed: Long): Draws = Draws(Math.floorMod(seed, 1L << 31))

  /** The draws of the family whose point names start with the stem: the seed
    * exclusive-or the stem's hash (`stemHash`), mixed by SplitMix64's
    * finalizer, modulo 2^31, so that families read at one seed draw from
    * unrelated states. Every step is arithmetic on the seed and the stem's
    * UTF-8 bytes, the same in every JVM.
    */
  def fromSeedAndStem(seed: Long, stem: String): Draws = fromSeed(
    mixed(seed ^ stemHash(stem))
  )

  /** The 64-bit FNV-1a hash of the stem's UTF-8 bytes. */
  private def stemHash(stem: String): Long =
    stem
      .getBytes(java.nio.charset.StandardCharsets.UTF_8)
      .foldLeft(0xcbf29ce484222325L)((hash, byte) =>
        (hash ^ (byte & 0xff)) * 0x100000001b3L
      )

  /** SplitMix64's finalizer, a bijection of 64-bit values whose output bits
    * each depend on every input bit.
    */
  private def mixed(value: Long): Long =
    val first = (value ^ (value >>> 30)) * 0xbf58476d1ce4e5b9L
    val second = (first ^ (first >>> 27)) * 0x94d049bb133111ebL
    second ^ (second >>> 31)

/** A repeated variant of a problem family
  * ([[com.yang_bo.gezi.contest.corpora.reductions]]): a closed program that applies the
  * family's own function, written once and let bound, to R distinct inputs
  * drawn from a seed, `(\f. [f a1, ..., f aR]) F`, whose answer is the Scott
  * list of the R results (`SetFree.scottList`); and the R single-input programs
  * of the family for the same inputs, as the family's points build them.
  */
trait RepeatedVariant:

  /** The stem of the variant's point names, `family` or `family/spelling` (the
    * judge's `CorpusSources.seededSources` appends `repetitions_R`); the
    * variant's draws start from the seed mixed with it
    * (`Draws.fromSeedAndStem`) unless the variant's `drawStem` says otherwise.
    */
  def stem: String

  /** The ranges a seed draws from. */
  def nominal: NominalRanges

  /** The repeated program of R distinct inputs drawn from the seed. */
  def program(group: ReductionGroup, seed: Long, repetitions: Int): ProblemTerm

  /** The point of the repeated program: by default its reference is
    * tabling(weak_head)'s reading (`Reference.Read`); a family that computes
    * its reference from its draws overrides this, with the same program.
    */
  def point(group: ReductionGroup, seed: Long, repetitions: Int): DrawnPoint =
    DrawnPoint(program(group, seed, repetitions), Reference.Read)

  /** The family's single-input programs of the same inputs, in order. */
  def singlePrograms(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): Vector[ProblemTerm]

  /** What the seed draws, the function's parameters and the inputs, as text. */
  def drawnText(group: ReductionGroup, seed: Long, repetitions: Int): String

/** A repeated variant whose draws are a value of `Drawn`. */
abstract class RepeatedFamily[Drawn] extends RepeatedVariant:

  /** The function's parameters and R distinct inputs, drawn; the group is there
    * for a family whose pool reads the attractors' entries.
    */
  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn

  /** The repeated program of the draws. */
  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm

  /** The single-input programs of the draws. */
  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm]

  /** The stem the draws start from, mixed with the seed. It is the variant's
    * `stem` unless the family overrides it: the direct and the respelled twin
    * of a family draw from the family's name alone, so the pair draws the same
    * functions and data and differs only in spelling.
    */
  def drawStem: String = stem

  /** The draws of the seed for R repetitions. Throws for an R outside the
    * nominal range.
    */
  protected final def drawnOf(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): Drawn =
    require(
      nominal.repetitions.contains(repetitions),
      s"$repetitions repetitions are outside ${nominal.repetitions}"
    )
    drawn(group, Draws.fromSeedAndStem(seed, drawStem), repetitions)

  final def program(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): ProblemTerm =
    repeated(group, drawnOf(group, seed, repetitions))

  final def singlePrograms(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): Vector[ProblemTerm] =
    val programs = singles(group, drawnOf(group, seed, repetitions))
    assert(
      programs.size == repetitions,
      s"${programs.size} single programs for $repetitions repetitions"
    )
    programs

  final def drawnText(
      group: ReductionGroup,
      seed: Long,
      repetitions: Int
  ): String =
    drawnOf(group, seed, repetitions).toString

/** The shape every repeated variant shares. */
object Repetition:

  /** The repetitions a variant may be asked for: one to 256, the largest R a
    * point asks.
    */
  val repetitions: Range.Inclusive = 1 to 256

  /** The repetitions of a variant whose sites take their inputs from `count`
    * distinct values: one to the smaller of 256 and the count, since the inputs
    * of the R sites are pairwise distinct.
    */
  def repetitionsWithin(count: Int): Range.Inclusive =
    1 to math.min(repetitions.end, count)

  /** `(\f. [f a11 ... a1k, ..., f aR1 ... aRk]) Function`: the function let
    * bound once and applied at each site to that site's arguments, the results
    * collected in a Scott list.
    */
  def sites(
      attractors: Attractors,
      function: ProblemTerm,
      arguments: Vector[Vector[ProblemTerm]]
  ): ProblemTerm =
    λ(bound => SetFree.scottList(attractors, arguments.map(applied(bound, _))))(
      function
    )

  /** The parameter's value, drawn from its nominal range. */
  def drawnNumber(
      draws: Draws,
      ranges: NominalRanges,
      name: String
  ): (Int, Draws) =
    draws.number(range(ranges, name))

  /** A natural of b binary digits, b drawn from the parameter's range (from 1
    * to 30, so that the value is an `Int`), its most significant digit one and
    * the others drawn: the program writes it in b digits, while the value, and
    * the work of an arithmetic on it, grows as 2^b.
    */
  def drawnWideNumber(
      draws: Draws,
      ranges: NominalRanges,
      name: String
  ): (Int, Draws) =
    val (digits, afterDigits) = draws.number(range(ranges, name))
    require(
      digits >= 1 && digits <= 30,
      s"no natural of $digits digits is an Int"
    )
    val (low, afterLow) = afterDigits.number(0 to Draws.highBitsCount - 1)
    val (high, afterHigh) = afterLow.number(0 to Draws.highBitsCount - 1)
    val belowTop = (1 << (digits - 1)) - 1
    ((1 << (digits - 1)) | (((high << 15) | low) & belowTop), afterHigh)

  /** The nominal range of the parameter. */
  def range(ranges: NominalRanges, name: String): Range.Inclusive =
    ranges.parameters
      .find(_.name == name)
      .map(_.range)
      .getOrElse(throw IllegalArgumentException(s"no parameter $name"))

  /** Both spellings of the attractors. */
  val spellings: Vector[Spelling] = Vector(Spelling.Direct, Spelling.Respelled)

  /** The spelling's name in a point name. */
  def spellingName(spelling: Spelling): String = spelling match
    case Spelling.Direct    => "direct"
    case Spelling.Respelled => "respelled"

/** `count (upto N True) True` of `ReductionMeanings` at R distinct N.
  *
  * The native solver: the count of the even numbers among 0 .. N - 1, (N + 1) /
  * 2, a unary numeral.
  */
object ReductionMeaningsRepeated
    extends RepeatedFamily[ReductionMeaningsRepeated.Drawn]
    with NativelySolved[ReductionMeaningsRepeated.Drawn]:

  val stem: String = "repeated_reduction_meanings"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.ReductionMeaningsReferenceTest"

  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.numbers.map(number => NativeValue.Unary((number + 1) / 2))

  /** The inputs N. */
  final case class Drawn(numbers: Vector[Int])

  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(64),
    Vector(NominalParameter("number", 1 to 64))
  )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    Drawn(
      draws
        .distinct(repetitions)(Repetition.drawnNumber(_, nominal, "number"))
        ._1
    )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    ReductionMeanings.withDefinitions(definitions =>
      Repetition.sites(
        group.attractors,
        λ(numeral => ReductionMeanings.counted(definitions, numeral)),
        drawn.numbers.map(number =>
          Vector(ReductionMeanings.numeral(definitions, number))
        )
      )
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.numbers.map(ReductionMeanings.countSurface)

/** `eval [] Expression` of `ReductionInterpreter` at R distinct expressions
  * drawn over the language without its amb: numbers, sums, products, variables
  * in scope and lets.
  *
  * The variant draws no amb, while the single-point family keeps its ambs. The
  * repeated variant asks for reuse of the interpreter's code across sites, and
  * ambs at R sites make the reading grow exponentially in R (though every amb
  * `amb(a + b, b + a)` has one value): R sites
  * `Amb(Add(Number(i),Number(1)),Add(Number(1),Number(i)))` took 4,217 steps at
  * R = 8 and 186,975 at R = 14 under tabling(weak_head), against about 155
  * steps a site without the amb (measured 2026-10-31). A large-R point would
  * then measure nondeterministic blow-up rather than reuse, which is the
  * single-point family's question.
  *
  * The native solver: each expression's value by call-by-value evaluation on
  * integers (`ReductionInterpreter.referenceValue`), a binary numeral.
  */
object ReductionInterpreterRepeated
    extends RepeatedFamily[ReductionInterpreterRepeated.Drawn]
    with NativelySolved[ReductionInterpreterRepeated.Drawn]:

  val stem: String = "repeated_reduction_interpreter"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.ReductionInterpreterReferenceTest"

  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.expressions.map(expression =>
      NativeValue.natural(ReductionInterpreter.referenceValue(expression))
    )

  /** The input expressions. */
  final case class Drawn(expressions: Vector[Expression])

  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitions,
    Vector(
      NominalParameter("number", 0 to 15),
      NominalParameter("depth", 0 to 3)
    )
  )

  private enum Shape:
    case Number, Variable, Add, Multiply, Let

  /** The expressions of depth 0 are the 16 numbers, so for more than 16
    * repetitions the depth is drawn from 1 up; for at most 16 the draws are
    * those of the whole range.
    */
  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val depths = Repetition.range(nominal, "depth")
    val numbers = Repetition.range(nominal, "number")
    val (depth, afterDepth) =
      draws.number(if repetitions > numbers.size then
        depths.start + 1 to depths.end
      else depths)
    Drawn(afterDepth.distinct(repetitions)(expression(_, depth, 0))._1)

  /** An expression of at most the depth whose variables are below the scope,
    * the count of the lets around it.
    */
  private def expression(
      draws: Draws,
      depth: Int,
      scope: Int
  ): (Expression, Draws) =
    val shapes =
      Vector(Shape.Number) ++ (if scope > 0 then Vector(Shape.Variable)
                               else Vector.empty) ++
        (if depth > 0 then Vector(Shape.Add, Shape.Multiply, Shape.Let)
         else Vector.empty)
    val (shape, afterShape) = draws.chosen(shapes)
    def pair(
        leftScope: Int,
        rightScope: Int
    ): ((Expression, Expression), Draws) =
      val (left, afterLeft) = expression(afterShape, depth - 1, leftScope)
      val (right, afterRight) = expression(afterLeft, depth - 1, rightScope)
      ((left, right), afterRight)
    shape match
      case Shape.Number =>
        val (value, after) =
          Repetition.drawnNumber(afterShape, nominal, "number")
        (Expression.Number(value), after)
      case Shape.Variable =>
        val (index, after) = afterShape.number(0 to scope - 1)
        (Expression.Variable(index), after)
      case Shape.Add =>
        val ((left, right), after) = pair(scope, scope)
        (Expression.Add(left, right), after)
      case Shape.Multiply =>
        val ((left, right), after) = pair(scope, scope)
        (Expression.Multiply(left, right), after)
      case Shape.Let =>
        val ((bound, body), after) = pair(scope, scope + 1)
        (Expression.Let(bound, body), after)

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    ReductionInterpreter.withEvaluator(group)(evaluate =>
      Repetition.sites(
        group.attractors,
        λ(syntax =>
          ReductionInterpreter.evaluatedInEmptyEnvironment(evaluate, syntax)
        ),
        drawn.expressions.map(expression =>
          Vector(ReductionInterpreter.syntaxTerm(expression))
        )
      )
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.expressions.map(ReductionInterpreter.programSurface(group, _))

/** `Repeat Times Function` of `SetFreePremises`, its function (the rebuild, the
  * complement, the unit law or its near miss), spelling and times drawn, at R
  * distinct binary numerals.
  *
  * The native solver: the rebuild and the unit law give the number; the near
  * miss adds one at each of the times; the complement exchanges every digit, so
  * it gives the number's digits, each exchanged, for odd times and the number
  * for even times.
  */
object SetFreePremisesRepeated
    extends RepeatedFamily[SetFreePremisesRepeated.Drawn]
    with NativelySolved[SetFreePremisesRepeated.Drawn]:

  val stem: String = "repeated_set_free_premises"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.SetFreePremisesReferenceTest"

  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.numbers.map(number =>
      drawn.function match
        case "rebuild" | "unit" => NativeValue.natural(number)
        case "unit_near"  => NativeValue.natural(BigInt(number) + drawn.times)
        case "complement" =>
          val digits =
            Vector.tabulate(BigInt(number).bitLength)(BigInt(number).testBit)
          NativeValue.Binary(if drawn.times % 2 == 1 then digits.map(!_)
          else digits)
        case other => throw IllegalArgumentException(s"no function $other")
    )

  /** The function's parameters and the input numbers. */
  final case class Drawn(
      function: String,
      spelling: Spelling,
      times: Int,
      numbers: Vector[Int]
  )

  /** The functions a seed draws from. */
  private[reductions] val functions: Vector[String] =
    Vector("rebuild", "complement", "unit", "unit_near")

  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitions,
    Vector(
      NominalParameter("times", 1 to 4),
      NominalParameter("number", 0 to 1023)
    )
  )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (function, afterFunction) = draws.chosen(functions)
    val (spelling, afterSpelling) = afterFunction.chosen(Repetition.spellings)
    val (times, afterTimes) =
      Repetition.drawnNumber(afterSpelling, nominal, "times")
    Drawn(
      function,
      spelling,
      times,
      afterTimes
        .distinct(repetitions)(Repetition.drawnNumber(_, nominal, "number"))
        ._1
    )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    Repetition.sites(
      group.attractors,
      SetFreePremises
        .repeatedFunction(group, drawn.function, drawn.spelling, drawn.times),
      drawn.numbers.map(number => Vector(binary(number)))
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.numbers.map(number =>
      SetFreePremises.pointSurface(
        group,
        SetFreePremises.RebuildPoint(
          "repeated",
          drawn.function,
          drawn.spelling,
          drawn.times,
          number
        )
      )
    )

/** The loop of `SetFreeScope`, Fibonacci or its doubling near miss, its
  * spelling drawn, at R distinct counts of steps drawn from the given ranges.
  * The points' variant is `SetFreeScopeRepeated`; another range serves a law
  * that has to read its programs fast (`SetFreeScopeRepeatedTest`).
  *
  * The native solver: fib of the steps, by iteration, as a binary numeral; for
  * the near miss, that many even digits over zero, all false.
  */
class SetFreeScopeRepeatedVariant(val nominal: NominalRanges)
    extends RepeatedFamily[SetFreeScopeRepeatedVariant.Drawn]
    with NativelySolved[SetFreeScopeRepeatedVariant.Drawn]:

  val stem: String = "repeated_set_free_scope"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.SetFreeScopeReferenceTest"

  def solved(drawn: SetFreeScopeRepeatedVariant.Drawn): Vector[NativeValue] =
    drawn.steps.map(count =>
      drawn.loop match
        case "fibonacci" =>
          NativeValue.natural(NativeArithmetic.fibonacci(count))
        case "doubling" => NativeValue.Binary(Vector.fill(count)(false))
        case other      => throw IllegalArgumentException(s"no loop $other")
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): SetFreeScopeRepeatedVariant.Drawn =
    val (loop, afterLoop) = draws.chosen(SetFreeScopeRepeatedVariant.loops)
    val (spelling, afterSpelling) = afterLoop.chosen(Repetition.spellings)
    SetFreeScopeRepeatedVariant.Drawn(
      loop,
      spelling,
      afterSpelling
        .distinct(repetitions)(Repetition.drawnNumber(_, nominal, "steps"))
        ._1
    )

  protected def repeated(
      group: ReductionGroup,
      drawn: SetFreeScopeRepeatedVariant.Drawn
  ): ProblemTerm =
    Repetition.sites(
      group.attractors,
      λ(steps =>
        SetFreeScope.loopApplied(group, drawn.loop, drawn.spelling, steps)
      ),
      drawn.steps.map(count => Vector(unary(count)))
    )

  protected def singles(
      group: ReductionGroup,
      drawn: SetFreeScopeRepeatedVariant.Drawn
  ): Vector[ProblemTerm] =
    drawn.steps.map(count =>
      SetFreeScope.pointSurface(
        group,
        SetFreeScope.ScopePoint("repeated", drawn.loop, drawn.spelling, count)
      )
    )

/** The draws of a `SetFreeScopeRepeatedVariant`. */
object SetFreeScopeRepeatedVariant:

  /** The loop's parameters and the input steps. */
  final case class Drawn(loop: String, spelling: Spelling, steps: Vector[Int])

  /** The loops a seed draws from. */
  private[reductions] val loops: Vector[String] =
    Vector("fibonacci", "doubling")

/** The points' variant of the scope loop: steps from 0 to 63, R at most 64. */
object SetFreeScopeRepeated
    extends SetFreeScopeRepeatedVariant(
      NominalRanges(
        Repetition.repetitionsWithin(64),
        Vector(NominalParameter("steps", 0 to 63))
      )
    )

/** The law of `SetFreeListLaws`, map or its filter near miss, its spelling
  * drawn, at R distinct counts of doublings drawn from the given ranges. Every
  * result of one program is the same Boolean: the family's answer depends on
  * the transformer only. The points' variant is `SetFreeListLawsRepeated`;
  * another range serves a law that has to read its programs fast
  * (`SetFreeListLawsRepeatedTest`).
  *
  * The native solver: the one-element list doubled k times has 2^k elements;
  * map keeps them all and the near miss's filter keeps none, and the answer is
  * whether the transformed length is the length.
  */
class SetFreeListLawsRepeatedVariant(val nominal: NominalRanges)
    extends RepeatedFamily[SetFreeListLawsRepeatedVariant.Drawn]
    with NativelySolved[SetFreeListLawsRepeatedVariant.Drawn]:

  val stem: String = "repeated_set_free_list_laws"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.SetFreeListLawsReferenceTest"

  def solved(drawn: SetFreeListLawsRepeatedVariant.Drawn): Vector[NativeValue] =
    drawn.doublings.map(count =>
      val length = BigInt(1) << count
      val transformedLength = drawn.transformer match
        case "map"    => length
        case "filter" => BigInt(0)
        case other => throw IllegalArgumentException(s"no transformer $other")
      NativeValue.Truth(transformedLength == length)
    )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): SetFreeListLawsRepeatedVariant.Drawn =
    val (transformer, afterTransformer) =
      draws.chosen(SetFreeListLawsRepeatedVariant.transformers)
    val (spelling, afterSpelling) =
      afterTransformer.chosen(Repetition.spellings)
    SetFreeListLawsRepeatedVariant.Drawn(
      transformer,
      spelling,
      afterSpelling
        .distinct(repetitions)(Repetition.drawnNumber(_, nominal, "doublings"))
        ._1
    )

  protected def repeated(
      group: ReductionGroup,
      drawn: SetFreeListLawsRepeatedVariant.Drawn
  ): ProblemTerm =
    Repetition.sites(
      group.attractors,
      λ(doublings =>
        SetFreeListLaws.lawApplied(
          group.attractors,
          drawn.transformer,
          drawn.spelling,
          doublings
        )
      ),
      drawn.doublings.map(count => Vector(unary(count)))
    )

  protected def singles(
      group: ReductionGroup,
      drawn: SetFreeListLawsRepeatedVariant.Drawn
  ): Vector[ProblemTerm] =
    drawn.doublings.map(count =>
      SetFreeListLaws.pointSurface(
        group.attractors,
        SetFreeListLaws.ListLawPoint(
          "repeated",
          drawn.transformer,
          drawn.spelling,
          count
        )
      )
    )

/** The draws of a `SetFreeListLawsRepeatedVariant`. */
object SetFreeListLawsRepeatedVariant:

  /** The law's parameters and the input doublings. */
  final case class Drawn(
      transformer: String,
      spelling: Spelling,
      doublings: Vector[Int]
  )

  /** The transformers a seed draws from. */
  private[reductions] val transformers: Vector[String] = Vector("map", "filter")

/** The points' variant of the list law: doublings from 0 to 12, R at most 13.
  */
object SetFreeListLawsRepeated
    extends SetFreeListLawsRepeatedVariant(
      NominalRanges(
        Repetition.repetitionsWithin(13),
        Vector(NominalParameter("doublings", 0 to 12))
      )
    )

/** The four functions of `ReductionProblems`, each its own variant: fib(n), the
  * product, the paths of a square grid, and the sum in both orders.
  */
object ReductionProblemsRepeated:

  /** fib(n) at R distinct n. The native solver: fib(n) by iteration, a binary
    * numeral.
    */
  object Fibonacci
      extends RepeatedFamily[Vector[Int]]
      with NativelySolved[Vector[Int]]:

    val stem: String = "repeated_reduction_problems_fibonacci"

    val claim: String =
      "com.yang_bo.gezi.contest.corpora.reductions.ReductionProblemsFibonacciReferenceTest"

    def solved(drawn: Vector[Int]): Vector[NativeValue] =
      drawn.map(number =>
        NativeValue.natural(NativeArithmetic.fibonacci(number))
      )

    val nominal: NominalRanges = NominalRanges(
      Repetition.repetitionsWithin(21),
      Vector(NominalParameter("number", 0 to 20))
    )

    protected def drawn(
        group: ReductionGroup,
        draws: Draws,
        repetitions: Int
    ): Vector[Int] =
      draws
        .distinct(repetitions)(Repetition.drawnNumber(_, nominal, "number"))
        ._1

    protected def repeated(
        group: ReductionGroup,
        drawn: Vector[Int]
    ): ProblemTerm =
      ReductionProblems.withFibonacci(group)(function =>
        Repetition.sites(
          group.attractors,
          λ(number => function(number)),
          drawn.map(number => Vector(unary(number)))
        )
      )

    protected def singles(
        group: ReductionGroup,
        drawn: Vector[Int]
    ): Vector[ProblemTerm] =
      drawn.map(ReductionProblems.fibonacciProgram(group, _))

  /** The product of R distinct pairs. The native solver: the integer product, a
    * binary numeral.
    *
    * The operands have 20 to 28 binary digits (`Repetition.drawnWideNumber`),
    * so the work of a site, a shift-and-add product, grows with the square of
    * its digits, which the program writes once. With operands up to 1023 the
    * point of R = 64 took the entries 0.09 to 0.58 s, of which 0.02 to 0.04 s
    * was left when the operands were cut to 0 to 7; at 20 to 28 digits it took
    * 0.77 to 1.16 s, about 97% of it the computation (seed 20261031, the three
    * entries as merged at 97aaa35cf, one reading each, 2026-11-01). weak_head
    * read the family's eight points in 3.8 s and the fastest entry in 6.2 s, so
    * the entries do not yet beat a direct reading here.
    */
  object Products
      extends RepeatedFamily[Vector[(Int, Int)]]
      with NativelySolved[Vector[(Int, Int)]]:

    val stem: String = "repeated_reduction_problems_products"

    val claim: String =
      "com.yang_bo.gezi.contest.corpora.reductions.ReductionProblemsProductsReferenceTest"

    def solved(drawn: Vector[(Int, Int)]): Vector[NativeValue] =
      drawn.map((left, right) => NativeValue.natural(BigInt(left) * right))

    val nominal: NominalRanges =
      NominalRanges(
        Repetition.repetitions,
        Vector(NominalParameter("operand_digits", 20 to 28))
      )

    protected def drawn(
        group: ReductionGroup,
        draws: Draws,
        repetitions: Int
    ): Vector[(Int, Int)] =
      draws.distinct(repetitions)(wideOperands(nominal))._1

    protected def repeated(
        group: ReductionGroup,
        drawn: Vector[(Int, Int)]
    ): ProblemTerm =
      ReductionProblems.withTimes(group)(times =>
        Repetition.sites(
          group.attractors,
          λ(left => λ(right => times(left)(right))),
          drawn.map((left, right) => Vector(binary(left), binary(right)))
        )
      )

    protected def singles(
        group: ReductionGroup,
        drawn: Vector[(Int, Int)]
    ): Vector[ProblemTerm] =
      drawn.map((left, right) =>
        ReductionProblems.productProgram(group, left, right)
      )

  /** The lattice paths of R distinct square grids, their sides drawn from the
    * given ranges. The points' variant is `Grids`; another range serves a law
    * that has to read its programs fast (`ReductionProblemsGridsRepeatedTest`).
    * The native solver: the paths of a square grid of side n, the binomial
    * C(2n, n), a binary numeral.
    */
  class GridsVariant(val nominal: NominalRanges)
      extends RepeatedFamily[Vector[Int]]
      with NativelySolved[Vector[Int]]:

    val stem: String = "repeated_reduction_problems_grids"

    val claim: String =
      "com.yang_bo.gezi.contest.corpora.reductions.ReductionProblemsGridsReferenceTest"

    def solved(drawn: Vector[Int]): Vector[NativeValue] =
      drawn.map(side =>
        NativeValue.natural(ReductionProblems.binomial(2 * side, side))
      )

    protected def drawn(
        group: ReductionGroup,
        draws: Draws,
        repetitions: Int
    ): Vector[Int] =
      draws.distinct(repetitions)(Repetition.drawnNumber(_, nominal, "side"))._1

    protected def repeated(
        group: ReductionGroup,
        drawn: Vector[Int]
    ): ProblemTerm =
      ReductionProblems.withGrid(group)(grid =>
        Repetition.sites(
          group.attractors,
          λ(side => ReductionProblems.squareGridPaths(grid, side)),
          drawn.map(side => Vector(unary(side)))
        )
      )

    protected def singles(
        group: ReductionGroup,
        drawn: Vector[Int]
    ): Vector[ProblemTerm] =
      drawn.map(ReductionProblems.gridProgram(group, _))

  /** The points' variant of the grids: sides from 0 to 9, R at most 10. */
  object Grids
      extends GridsVariant(
        NominalRanges(
          Repetition.repetitionsWithin(10),
          Vector(NominalParameter("side", 0 to 9))
        )
      )

  /** `[a + b, b + a]` of R distinct pairs. The native solver: the integer sum,
    * a binary numeral, the one normal form of both members of the choice.
    */
  object Sums
      extends RepeatedFamily[Vector[(Int, Int)]]
      with NativelySolved[Vector[(Int, Int)]]:

    val stem: String = "repeated_reduction_problems_sums"

    val claim: String =
      "com.yang_bo.gezi.contest.corpora.reductions.ReductionProblemsSumsReferenceTest"

    def solved(drawn: Vector[(Int, Int)]): Vector[NativeValue] =
      drawn.map((left, right) => NativeValue.natural(BigInt(left) + right))

    val nominal: NominalRanges = NominalRanges(
      Repetition.repetitions,
      Vector(NominalParameter("operand", 0 to 1023))
    )

    protected def drawn(
        group: ReductionGroup,
        draws: Draws,
        repetitions: Int
    ): Vector[(Int, Int)] =
      draws.distinct(repetitions)(operands(nominal))._1

    protected def repeated(
        group: ReductionGroup,
        drawn: Vector[(Int, Int)]
    ): ProblemTerm =
      ReductionProblems.withPlus(group)(plus =>
        Repetition.sites(
          group.attractors,
          λ(left =>
            λ(right => ReductionProblems.sumBothOrders(plus, left, right))
          ),
          drawn.map((left, right) => Vector(binary(left), binary(right)))
        )
      )

    protected def singles(
        group: ReductionGroup,
        drawn: Vector[(Int, Int)]
    ): Vector[ProblemTerm] =
      drawn.map((left, right) =>
        ReductionProblems.sumBothOrdersProgram(group, left, right)
      )

  /** Two operands, each drawn from the range `operand`. */
  private def operands(ranges: NominalRanges)(
      draws: Draws
  ): ((Int, Int), Draws) =
    val (left, afterLeft) = Repetition.drawnNumber(draws, ranges, "operand")
    val (right, afterRight) =
      Repetition.drawnNumber(afterLeft, ranges, "operand")
    ((left, right), afterRight)

  /** Two operands, each of a count of digits drawn from the range
    * `operand_digits` (`Repetition.drawnWideNumber`).
    */
  private[reductions] def wideOperands(ranges: NominalRanges)(
      draws: Draws
  ): ((Int, Int), Draws) =
    val (left, afterLeft) =
      Repetition.drawnWideNumber(draws, ranges, "operand_digits")
    val (right, afterRight) =
      Repetition.drawnWideNumber(afterLeft, ranges, "operand_digits")
    ((left, right), afterRight)

/** `Result.equality(Left.operation(Right))` of `ReductionMixinBinary`, its
  * operation drawn, at R distinct equations; an equation holds or its result is
  * off by one to four, each with even odds.
  *
  * The operands are drawn from 0 to 3: under weak_head, `times` with operands
  * up to 15 ran the reference reading out of 20,000,000 steps already at R = 4
  * (seed 20261031, 2026-10-31), and up to 63 at every R. R is at most 80, the
  * count of distinct equations: 16 operand pairs, each with the true result and
  * four results off by one to four.
  *
  * The native solver: whether the integer sum or product of the operands is the
  * result, a Boolean.
  */
object ReductionMixinBinaryRepeated
    extends RepeatedFamily[ReductionMixinBinaryRepeated.Drawn]
    with NativelySolved[ReductionMixinBinaryRepeated.Drawn]:

  val stem: String = "repeated_reduction_mixin_binary"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.ReductionMixinBinaryReferenceTest"

  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.equations.map(equation =>
      val value = drawn.operation match
        case "plus"  => BigInt(equation.left) + equation.right
        case "times" => BigInt(equation.left) * equation.right
        case other   => throw IllegalArgumentException(s"no operation $other")
      NativeValue.Truth(value == equation.result)
    )

  /** An equation `left operation right = result`. */
  final case class Equation(left: Int, right: Int, result: BigInt)

  /** The operation and the input equations. */
  final case class Drawn(operation: String, equations: Vector[Equation])

  /** The operations a seed draws from. */
  private[reductions] val operations: Vector[String] = Vector("plus", "times")

  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4 * 4 * 5),
    Vector(
      NominalParameter("operand", 0 to 3),
      NominalParameter("offset", 0 to 4)
    )
  )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (operation, afterOperation) = draws.chosen(operations)
    Drawn(
      operation,
      afterOperation.distinct(repetitions)(equation(operation, _))._1
    )

  /** An equation of the operation: its operands drawn, and its result the true
    * one or off by one to four, with even odds.
    */
  private[reductions] def equation(
      operation: String,
      draws: Draws
  ): (Equation, Draws) =
    val (left, afterLeft) = Repetition.drawnNumber(draws, nominal, "operand")
    val (right, afterRight) =
      Repetition.drawnNumber(afterLeft, nominal, "operand")
    val (holds, afterHolds) = afterRight.chosen(Vector(true, false))
    val (offset, afterOffset) =
      afterHolds.number(1 to Repetition.range(nominal, "offset").end)
    val value = operation match
      case "plus"  => BigInt(left) + right
      case "times" => BigInt(left) * right
      case other   => throw IllegalArgumentException(s"no operation $other")
    (
      Equation(left, right, if holds then value else value + offset),
      afterOffset
    )

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    val mixins = group.mixins
    ReductionMixinBinary.withBinaryLibrary(mixins)(names =>
      Repetition.sites(
        group.attractors,
        abstractions(
          3,
          {
            case Vector(left, right, result) =>
              ReductionMixinBinary.equationRead(
                mixins,
                drawn.operation,
                left,
                right,
                result
              )
            case other =>
              throw IllegalArgumentException(s"not three operands: $other")
          }
        ),
        drawn.equations.map(equation =>
          Vector(
            mixins.binaryInstance(names, equation.left),
            mixins.binaryInstance(names, equation.right),
            mixins.binaryInstance(names, equation.result)
          )
        )
      )
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.equations.map(equation =>
      ReductionMixinBinary.binaryPointSurface(
        group.mixins,
        drawn.operation,
        equation.left,
        equation.right,
        equation.result
      )
    )

/** The operation of `SetFreeArithmetic`, the sum, the product or the product's
  * near miss, its spelling drawn, at R distinct pairs.
  *
  * The native solver: the integer sum, the integer product, or the near product
  * (`SetFreeArithmetic.nearProduct`), a binary numeral.
  *
  * The operands have 20 to 28 binary digits, as in
  * `ReductionProblemsRepeated.Products`. With operands up to 1023 the point of
  * R = 64 took the entries 0.11 to 0.27 s, of which 0.07 to 0.11 s was left
  * when the operands were cut to 0 to 7; at 20 to 28 digits it took 0.68 to
  * 1.08 s, 85% to 91% of it the computation (seed 20261031, the three entries
  * as merged at 97aaa35cf, one reading each, 2026-11-01). weak_head read the
  * family's eight points in 2.9 s, as fast as the fastest entry (3.0 s).
  */
object SetFreeArithmeticRepeated
    extends RepeatedFamily[SetFreeArithmeticRepeated.Drawn]
    with NativelySolved[SetFreeArithmeticRepeated.Drawn]:

  val stem: String = "repeated_set_free_arithmetic"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.SetFreeArithmeticReferenceTest"

  def solved(drawn: Drawn): Vector[NativeValue] =
    drawn.pairs.map((left, right) =>
      NativeValue.natural(drawn.operation match
        case "merge_binary_plus"  => BigInt(left) + right
        case "merge_binary_times" => BigInt(left) * right
        case "near_times"         => SetFreeArithmetic.nearProduct(left, right)
        case other => throw IllegalArgumentException(s"no operation $other"))
    )

  /** The operation's parameters and the input pairs. */
  final case class Drawn(
      operation: String,
      spelling: Spelling,
      pairs: Vector[(Int, Int)]
  )

  /** The operations a seed draws from. */
  private[reductions] val operations: Vector[String] =
    Vector("merge_binary_plus", "merge_binary_times", "near_times")

  val nominal: NominalRanges = NominalRanges(
    Repetition.repetitions,
    Vector(NominalParameter("operand_digits", 20 to 28))
  )

  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): Drawn =
    val (operation, afterOperation) = draws.chosen(operations)
    val (spelling, afterSpelling) = afterOperation.chosen(Repetition.spellings)
    Drawn(
      operation,
      spelling,
      afterSpelling.distinct(repetitions)(pair(nominal))._1
    )

  /** Two operands, each of a count of digits drawn from the ranges'
    * `operand_digits` (`Repetition.drawnWideNumber`).
    */
  private[reductions] def pair(ranges: NominalRanges)(
      draws: Draws
  ): ((Int, Int), Draws) =
    ReductionProblemsRepeated.wideOperands(ranges)(draws)

  protected def repeated(group: ReductionGroup, drawn: Drawn): ProblemTerm =
    Repetition.sites(
      group.attractors,
      SetFreeArithmetic
        .operationFunction(group, drawn.operation, drawn.spelling),
      drawn.pairs.map((left, right) => Vector(binary(left), binary(right)))
    )

  protected def singles(
      group: ReductionGroup,
      drawn: Drawn
  ): Vector[ProblemTerm] =
    drawn.pairs.map((left, right) =>
      SetFreeArithmetic.pointSurface(
        group,
        SetFreeArithmetic.ArithmeticPoint(
          "repeated",
          drawn.operation,
          drawn.spelling,
          left,
          right
        )
      )
    )
