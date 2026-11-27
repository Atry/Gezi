package gezi.contest.corpora.reductions

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** The hotspot family `repeated_library_hotspots`: a program that is costly
  * both read entirely by an interpreter and compiled entirely, since a few of
  * its functions are hot and most are called once or twice, and the hot ones
  * come one after the other.
  *
  * A site is one problem. It has M distinct functions g_1, ..., g_M from
  * canonical binary naturals to canonical binary naturals
  * (`corpora/standard_library/binary`), each a straight-line program of L steps
  * over the intermediates v_0, ..., v_L, v_0 the input and the result v_L. Step
  * k computes v_k by one of the library's merge_binary_plus, binary_maximum,
  * binary_minimum and binary_bitwise_or: the sum is v_(k-1) plus a constant;
  * the maximum and the bitwise or take an earlier intermediate as the left
  * operand and a constant as the right one; each operand of the minimum is an
  * earlier intermediate or a constant. A sum, a maximum or a bitwise or is at
  * most its intermediate plus its constant, and a minimum at most either of its
  * operands, so v_k is at most the largest earlier intermediate plus the step's
  * constant (zero for a minimum), and a call raises the state by at most the
  * sum of its function's L constants: the state grows linearly with the calls
  * and never doubles. Each constant has b binary digits, b drawn from the range
  * `constant_bits`, its most significant digit one
  * (`Repetition.drawnWideNumber`). The operations, the wiring and the constants
  * are drawn; a function equal to an earlier one of the site is drawn anew, and
  * so is a function whose result does not depend on its input (such a function
  * makes every call before it dead, and an evaluator that reads lazily,
  * weak_head included, would skip all of them).
  *
  * The function g_j has the call count c_j = max(1, floor(C / r_j^alpha)), with
  * r_1, ..., r_M a random permutation of 1, ..., M and C and alpha the single
  * values of the ranges `calls` and `exponent`: a Zipf law, a few functions
  * hot, most called once. The driver takes the functions in a random order and
  * hands the state s, first a drawn natural of b digits, b drawn from the range
  * `initial_bits`, to each in turn, iterated its count of times. The count is a
  * canonical binary natural and the iteration recurses on its digits, never on
  * a unary numeral:
  *
  * {{{
  * iterate = fixpoint (\self. \n. \g. \s.
  *             n s (\m. self m g (self m g s)) (\m. g (self m g (self m g s))))
  * }}}
  *
  * (iterate 0 = s, iterate 2m = iterate m twice, iterate 2m + 1 one more
  * application of g after that). binary_zero, binary_even, binary_odd, the four
  * operations and iterate are let bound once in the site, and every
  * intermediate once in its function, so that the program grows linearly in M *
  * L; the constants and the initial state are written where they are used with
  * the bound constructors, so that the program's text is mostly its wiring
  * rather than inlined constructor bodies. The site's answer is the last state,
  * one canonical binary natural. The sites of a point are drawn distinct and
  * share nothing.
  *
  * The respelled site writes every operation with its two operands exchanged
  * (`merge_binary_plus c v`, `binary_maximum b a`, and so on, each of the four
  * commutative) and applies g first in the odd case of iterate,
  * `self m g (self m g (g s))`; both are g iterated 2m + 1 times.
  *
  * The rungs: a repeated variant's R is the count of its point's sites
  * (`RepeatedFamily.singlePrograms`), so C cannot grow with R; C is a parameter
  * of the variant instead, and each rung of C is a family of its own
  * (`LibraryHotspots.rungs`), as the scaled unshared families are
  * (`LibraryUnsharedDoublings.largeVariants`), the sites of a point being
  * problems of its rung.
  *
  * The calibration variants (`LibraryHotspots.Calibration`): each rung has a
  * cold and a hot variant, which exist only for the calibration of the rungs
  * and are never scored.
  *
  * The native solver (`LibraryHotspots.finalState`) simulates the definition
  * with BigInt: each function's steps in order on the state, iterated its count
  * of times in the driver's order. The claim that it is the program's one
  * normal form: merge_binary_plus, binary_maximum, binary_minimum and
  * binary_bitwise_or compute the sum, the larger, the smaller and the bitwise
  * or of two canonical binary naturals, and build a canonical one (their
  * library files' comments); iterate applies g exactly n times by induction on
  * n's digits; so the site's term is the canonical natural of the simulated
  * state. `LibraryHotspotsReferenceTest` checks it against tabling(weak_head)'s
  * reading on small draws.
  *
  * The shapes (`LibraryHotspots.Shape`): the loop above, a higher-order iterate
  * applied to each function, is the iterated shape, the family's own. Two more
  * families write the loops in other shapes, so that the hot ladder does not
  * have one recursion shape only (2026-11-07): the inlined shape gives each
  * function a first-order loop of its own, and the nested shape runs iterate
  * inside iterate. Both exist for the hot calibration only, at the rungs
  * `LibraryHotspots.shapedRungCalls` (`LibraryHotspots.shaped`). Their draws
  * are the iterated rung's drawing code and native solver, started from their
  * own family names, so that a seed gives each family other problems and other
  * answers (across repetitions only code is reused, never an answer). The claim
  * extends to them: a function's own loop applies it exactly n times by the
  * same induction on n's digits as iterate, and the nested loop applies n times
  * a function that applies g k times, g n * k = c times;
  * `LibraryHotspotsInlinedReferenceTest` and
  * `LibraryHotspotsNestedReferenceTest` check them against tabling(weak_head)'s
  * reading on small draws.
  */
final class LibraryHotspots(
    spelling: Spelling,
    val nominal: NominalRanges,
    val family: String,
    val calibration: LibraryHotspots.Calibration,
    val shape: LibraryHotspots.Shape
) extends StandardLibraryFamily[LibraryHotspots.Drawn](spelling)
    with NativelySolved[LibraryHotspots.Drawn]:

  import LibraryHotspots.Constructors
  import LibraryHotspots.Operand
  import LibraryHotspots.Operation
  import LibraryHotspots.Problem
  import LibraryHotspots.Shape
  import LibraryHotspots.Step
  import LibraryHotspots.StraightLine

  /** The iterated shape's variant. */
  def this(
      spelling: Spelling,
      nominal: NominalRanges,
      family: String,
      calibration: LibraryHotspots.Calibration
  ) =
    this(spelling, nominal, family, calibration, LibraryHotspots.Shape.Iterated)

  val claim: String = shape.claim

  /** The calls C, the one value of the range `calls`. */
  val calls: Int = LibraryHotspots.single(nominal, "calls")

  /** The exponent alpha of the Zipf law, the one value of the range `exponent`.
    */
  val exponent: Int = LibraryHotspots.single(nominal, "exponent")

  /** Each site's last state, a canonical binary natural. */
  def solved(drawn: LibraryHotspots.Drawn): Vector[NativeValue] =
    drawn.sites.map(problem =>
      NativeValue.LibraryNatural(LibraryHotspots.finalState(problem))
    )

  /** The sites drawn as the scored rung draws them, then derived by the
    * calibration, so that the same draws give the scored problems and their
    * cold and hot derivations.
    *
    * FIXME (2026-11-02): a point's draws start from the seed mixed with the
    * https://github.com/Atry/private-overlay/issues/1992 variant's stem
    * (`RepeatedFamily.drawnOf`, `Draws.fromSeedAndStem`), and the stem is the
    * family name, so the cold and hot points of a seed derive other problems
    * than the rung's point of that seed (measured at the seed 0, R = 6, small
    * ranges: the sites' function counts were 4, 4, 2, 6, 5, 6 for the rung, 4,
    * 2, 1, 6, 1, 5 cold, and 4, 4, 4, 1, 2, 2 hot). Only the distributions
    * agree. Candidate fix, outside this family: a stem of the draws that a
    * variant may override, set to the rung's stem here.
    */
  protected def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): LibraryHotspots.Drawn =
    LibraryHotspots.Drawn(
      draws
        .distinct(repetitions)(
          LibraryHotspots.problem(nominal, calls, exponent)
        )
        ._1
        .map(calibration.derived)
    )

  /** The library's term of the operation. */
  private def libraryFunction(
      terms: StandardLibraryTerms,
      operation: Operation
  ): ProblemTerm = operation match
    case Operation.Plus      => terms.binaryPlus
    case Operation.Maximum   => terms.binaryMaximum
    case Operation.Minimum   => terms.binaryMinimum
    case Operation.BitwiseOr => terms.binaryBitwiseOr

  /** The operation, the site's variable bound to its library term (by the
    * operation's ordinal), applied to its two operands in the spelling.
    */
  private def operated(
      operations: Vector[ProblemTerm],
      operation: Operation,
      left: ProblemTerm,
      right: ProblemTerm
  ): ProblemTerm =
    val function = operations(operation.ordinal)
    spelling match
      case Spelling.Direct    => function(left)(right)
      case Spelling.Respelled => function(right)(left)

  /** The canonical binary natural of the value, built with the site's variables
    * bound to binary_zero, binary_even and binary_odd, the least significant
    * bit outermost and no binary_even over binary_zero, as
    * `StandardLibraryTerms.binary` builds it with the library's terms.
    */
  private def constant(constructors: Constructors, value: BigInt): ProblemTerm =
    require(value >= 0, s"a natural is not negative: $value")
    if value == 0 then constructors.zero
    else if value.testBit(0) then
      constructors.odd(constant(constructors, value >> 1))
    else constructors.even(constant(constructors, value >> 1))

  private def operandTerm(
      constructors: Constructors,
      operand: Operand,
      intermediates: Vector[ProblemTerm]
  ): ProblemTerm = operand match
    case Operand.Intermediate(index) => intermediates(index)
    case Operand.Constant(value)     => constant(constructors, value)

  /** The function's body over its input: each intermediate but the result let
    * bound once, `(\v_k. rest) (operation v_i v_j)`, so that the term grows
    * linearly in L whatever the wiring; the last step is the body's value.
    */
  private def straightLine(
      constructors: Constructors,
      operations: Vector[ProblemTerm],
      function: StraightLine
  ): ProblemTerm =
    def from(index: Int, intermediates: Vector[ProblemTerm]): ProblemTerm =
      val step = function.steps(index)
      val value = operated(
        operations,
        step.operation,
        operandTerm(constructors, step.left, intermediates),
        operandTerm(constructors, step.right, intermediates)
      )
      if index == function.steps.size - 1 then value
      else λ(bound => from(index + 1, intermediates :+ bound))(value)
    require(function.steps.nonEmpty, "a function has at least one step")
    λ(input => from(0, Vector(input)))

  /** iterate in the spelling. */
  private def iterate(terms: StandardLibraryTerms): ProblemTerm =
    terms.fixpoint(
      λ(self =>
        λ(count =>
          λ(function =>
            λ(state =>
              val odd = spelling match
                case Spelling.Direct =>
                  λ(half =>
                    function(self(half)(function)(self(half)(function)(state)))
                  )
                case Spelling.Respelled =>
                  λ(half =>
                    self(half)(function)(self(half)(function)(function(state)))
                  )
              count(state)(
                λ(half => self(half)(function)(self(half)(function)(state)))
              )(odd)
            )
          )
        )
      )
    )

  /** The site in the variant's shape. */
  private def site(terms: StandardLibraryTerms, problem: Problem): ProblemTerm =
    shape match
      case Shape.Iterated => iteratedSite(terms, problem)
      case Shape.Inlined  => inlinedSite(terms, problem)
      case Shape.Nested   => nestedSite(terms, problem)

  /** The constructors of the site's first three let variables, bound to
    * binary_zero, binary_even and binary_odd in that order.
    */
  private def constructorsOf(variables: Vector[ProblemTerm]): Constructors =
    variables match
      case Vector(zero, even, odd) => Constructors(zero, even, odd)
      case other                   =>
        throw IllegalStateException(s"three constructor variables, not $other")

  /** The site: binary_zero, binary_even, binary_odd, the four operations and
    * iterate let bound once, in that order, so that the program grows by a few
    * variables at each step and each digit rather than by a library body, and
    * each function in the driver's order iterated its count of times on the
    * state.
    */
  private def iteratedSite(
      terms: StandardLibraryTerms,
      problem: Problem
  ): ProblemTerm =
    val constructorTerms =
      Vector(terms.binaryZero, terms.binaryEven, terms.binaryOdd)
    lets(
      (constructorTerms ++ Operation.values.toVector
        .map(libraryFunction(terms, _))) :+ iterate(terms),
      bound =>
        val (constructorVariables, rest) = bound.splitAt(constructorTerms.size)
        val constructors = constructorsOf(constructorVariables)
        val operations = rest.init
        val iterated = rest.last
        problem.order.foldLeft(constant(constructors, problem.initial))(
          (state, index) =>
            iterated(constant(constructors, problem.calls(index)))(
              straightLine(constructors, operations, problem.functions(index))
            )(state)
        )
    )

  /** The function's own loop in the spelling, built with the site's variable
    * bound to fixpoint: iterate with the function written into its body rather
    * than taken as an argument,
    *
    * {{{
    * fixpoint (\self. \n. \s.
    *   n s (\m. self m (self m s)) (\m. G (self m (self m s))))
    * }}}
    *
    * G the function's straight-line term (`straightLine`), applied where it
    * stands, so that its input is let bound as each intermediate is; the
    * respelled odd case is `\m. self m (self m (G s))`. The loop's state is a
    * natural and its count a natural: it takes no function.
    */
  private def ownLoop(fixed: ProblemTerm, function: ProblemTerm): ProblemTerm =
    fixed(
      λ(self =>
        λ(count =>
          λ(state =>
            val odd = spelling match
              case Spelling.Direct =>
                λ(half => function(self(half)(self(half)(state))))
              case Spelling.Respelled =>
                λ(half => self(half)(self(half)(function(state))))
            count(state)(λ(half => self(half)(self(half)(state))))(odd)
          )
        )
      )
    )

  /** The inlined site: binary_zero, binary_even, binary_odd, the four
    * operations and fixpoint let bound once, in that order, and each function
    * in the driver's order run by its own loop (`ownLoop`) for its count of
    * times on the state.
    */
  private def inlinedSite(
      terms: StandardLibraryTerms,
      problem: Problem
  ): ProblemTerm =
    val constructorTerms =
      Vector(terms.binaryZero, terms.binaryEven, terms.binaryOdd)
    lets(
      (constructorTerms ++ Operation.values.toVector
        .map(libraryFunction(terms, _))) :+ terms.fixpoint,
      bound =>
        val (constructorVariables, rest) = bound.splitAt(constructorTerms.size)
        val constructors = constructorsOf(constructorVariables)
        val operations = rest.init
        val fixed = rest.last
        problem.order.foldLeft(constant(constructors, problem.initial))(
          (state, index) =>
            ownLoop(
              fixed,
              straightLine(constructors, operations, problem.functions(index))
            )(
              constant(constructors, problem.calls(index))
            )(state)
        )
    )

  /** The nested site: the iterated site's lets, and each function in the
    * driver's order run on the state as follows. A function of count 1 is
    * applied once, `G s`. A function of count c > 1, split into c = n * k by
    * `LibraryHotspots.split`, runs `iterate n (\t. iterate k G t) s`: the outer
    * iterate's function is a loop of k applications of G, so G runs n * k = c
    * times.
    */
  private def nestedSite(
      terms: StandardLibraryTerms,
      problem: Problem
  ): ProblemTerm =
    val constructorTerms =
      Vector(terms.binaryZero, terms.binaryEven, terms.binaryOdd)
    lets(
      (constructorTerms ++ Operation.values.toVector
        .map(libraryFunction(terms, _))) :+ iterate(terms),
      bound =>
        val (constructorVariables, rest) = bound.splitAt(constructorTerms.size)
        val constructors = constructorsOf(constructorVariables)
        val operations = rest.init
        val iterated = rest.last
        problem.order.foldLeft(constant(constructors, problem.initial))(
          (state, index) =>
            val function =
              straightLine(constructors, operations, problem.functions(index))
            val count = problem.calls(index)
            require(count >= 1, s"a function is called at least once: $count")
            if count == 1 then function(state)
            else
              val (outer, inner) = LibraryHotspots.split(count)
              iterated(constant(constructors, outer))(
                λ(innerState =>
                  iterated(constant(constructors, inner))(function)(innerState)
                )
              )(state)
        )
    )

  protected def program(
      terms: StandardLibraryTerms,
      drawn: LibraryHotspots.Drawn
  ): ProblemTerm =
    terms.list(drawn.sites.map(site(terms, _)))

  protected def singlePrograms(
      terms: StandardLibraryTerms,
      drawn: LibraryHotspots.Drawn
  ): Vector[ProblemTerm] =
    drawn.sites.map(site(terms, _))

/** The draws, the native solver, the nominal ranges and the rungs of
  * `LibraryHotspots`.
  */
object LibraryHotspots:

  /** The four operations of a step. */
  enum Operation:
    case Plus, Maximum, Minimum, BitwiseOr

  /** An operand of a step: an earlier intermediate, by its index (the input is
    * 0), or a constant.
    */
  enum Operand:
    case Intermediate(index: Int)
    case Constant(value: BigInt)

  /** A step: the operation of its two operands. The left operand of a sum is
    * the previous intermediate and its right one a constant; the left operand
    * of a maximum and of a bitwise or is an earlier intermediate and its right
    * one a constant.
    */
  final case class Step(operation: Operation, left: Operand, right: Operand)

  /** A function's steps, in order. */
  final case class StraightLine(steps: Vector[Step])

  /** A site: the functions, each one's rank in the Zipf law (from 0, the
    * hottest) and call count (by the function's index), the driver's order of
    * the functions' indices, and the initial state.
    */
  final case class Problem(
      functions: Vector[StraightLine],
      ranks: Vector[Int],
      calls: Vector[BigInt],
      order: Vector[Int],
      initial: BigInt
  )

  /** The problems of the sites. */
  final case class Drawn(sites: Vector[Problem])

  /** The site's variables bound to binary_zero, binary_even and binary_odd.
    */
  final case class Constructors(
      zero: ProblemTerm,
      even: ProblemTerm,
      odd: ProblemTerm
  )

  /** The functions a hot variant keeps: the hottest four. */
  val hotFunctions: Int = 4

  /** What a variant makes of the drawn problems. The cold variant exists only
    * for the calibration of the rungs. The hot variant is scored, as a ladder
    * of its own that measures the hot functions alone, its program small enough
    * that reading it costs little against the native time. Their computed
    * references come from the same native solver (`finalState`) as the rung's.
    */
  enum Calibration:

    /** The rung's problem as drawn, its cold functions included. */
    case Scored

    /** The rung's problem with every call count set to 1, everything else
      * identical.
      */
    case Cold

    /** The rung's problem restricted to the `hotFunctions` functions of the
      * largest call counts (the smallest ranks), in the same order among
      * themselves, with the same counts and the same initial state.
      */
    case Hot

    /** The problem this variant makes of the drawn one. */
    def derived(problem: Problem): Problem = this match
      case Scored => problem
      case Cold   => problem.copy(calls = problem.calls.map(_ => BigInt(1)))
      case Hot    =>
        val kept =
          problem.order.filter(index => problem.ranks(index) < hotFunctions)
        Problem(
          kept.map(problem.functions),
          kept.map(problem.ranks),
          kept.map(problem.calls),
          kept.indices.toVector,
          problem.initial
        )

    /** The suffix of the variant's family name after its rung's name. */
    def suffix: String = this match
      case Scored => ""
      case Cold   => "_cold"
      case Hot    => "_hot"

  /** The shape a site's loops are written in; every shape runs each function
    * its count of times, so the shapes of one problem have one answer
    * (`finalState`).
    */
  enum Shape:

    /** A higher-order iterate, let bound once in the site, applied to each
      * function and its count: the family's own shape.
      */
    case Iterated

    /** A first-order loop over the count for each function, the function's
      * straight-line term written into the loop's body.
      */
    case Inlined

    /** iterate over an outer count applied to a function that runs iterate over
      * an inner count on the function, the two counts' product the function's
      * count (`split`); a function of count 1 is applied once.
      */
    case Nested

    /** The part of the family name after `repeated_library_hotspots` and before
      * `_calls_`: nothing for the iterated shape.
      */
    def infix: String = this match
      case Iterated => ""
      case Inlined  => "_inlined"
      case Nested   => "_nested"

    /** The test that checks the shape's computed reference against
      * tabling(weak_head)'s reading on small draws.
      */
    def claim: String = this match
      case Iterated => LibraryHotspots.claim
      case Inlined  =>
        "gezi.contest.corpora.reductions.LibraryHotspotsInlinedReferenceTest"
      case Nested =>
        "gezi.contest.corpora.reductions.LibraryHotspotsNestedReferenceTest"

  /** The count c > 1 split into the outer and the inner count (n, k) of the
    * nested shape, n * k = c: n is the largest divisor of c whose square is at
    * most c, and k = c / n, so n <= k, and both are at least 2 exactly when c
    * is not prime; a prime c splits into (1, c). At the hot rungs' counts,
    * floor(C / r^2) for r = 1 to 4, C = 10^4 splits into (100, 100), (50, 50),
    * (11, 101) and (25, 25).
    */
  def split(count: BigInt): (BigInt, BigInt) =
    require(count > 1, s"only a count above 1 is split: $count")
    val root = BigInt(count.bigInteger.sqrt())
    val outer = (BigInt(1) to root).filter(divisor => count % divisor == 0).last
    (outer, count / outer)

  /** The function's result on the input: its steps in order. */
  def applied(function: StraightLine, input: BigInt): BigInt =
    function.steps
      .foldLeft(Vector(input))((intermediates, step) =>
        def value(operand: Operand): BigInt = operand match
          case Operand.Intermediate(index) => intermediates(index)
          case Operand.Constant(constant)  => constant
        val left = value(step.left)
        val right = value(step.right)
        intermediates :+ (step.operation match
          case Operation.Plus      => left + right
          case Operation.Maximum   => left.max(right)
          case Operation.Minimum   => left.min(right)
          case Operation.BitwiseOr => left | right)
      )
      .last

  /** The function applied `count` times to the state. */
  @tailrec
  def iterated(function: StraightLine, count: BigInt, state: BigInt): BigInt =
    if count == 0 then state
    else iterated(function, count - 1, applied(function, state))

  /** The site's last state, by the definition: from the initial state, each
    * function in the driver's order iterated its count of times.
    */
  def finalState(problem: Problem): BigInt =
    problem.order.foldLeft(problem.initial)((state, index) =>
      iterated(problem.functions(index), problem.calls(index), state)
    )

  /** Whether the function's result depends on its input: whether the input
    * reaches the last intermediate through the operands.
    */
  def dependsOnInput(function: StraightLine): Boolean =
    function.steps
      .foldLeft(Vector(true))((dependent, step) =>
        def reaches(operand: Operand): Boolean = operand match
          case Operand.Intermediate(index) => dependent(index)
          case Operand.Constant(_)         => false
        dependent :+ (reaches(step.left) || reaches(step.right))
      )
      .last

  /** A site: M drawn from `functions`, M distinct functions, the ranks and the
    * driver's order, two random permutations, and the initial state.
    */
  def problem(nominal: NominalRanges, calls: Int, exponent: Int)(
      draws: Draws
  ): (Problem, Draws) =
    val (count, afterCount) =
      Repetition.drawnNumber(draws, nominal, "functions")
    val (functions, afterFunctions) =
      afterCount.distinct(count)(straightLine(nominal))
    val (ranks, afterRanks) = permutation(count, afterFunctions)
    val (order, afterOrder) = permutation(count, afterRanks)
    val (initial, afterInitial) =
      Repetition.drawnWideNumber(afterOrder, nominal, "initial_bits")
    val callCounts = ranks.map(rank =>
      (BigInt(calls) / BigInt(rank + 1).pow(exponent)).max(BigInt(1))
    )
    (
      Problem(functions, ranks, callCounts, order, BigInt(initial)),
      afterInitial
    )

  /** A function of L steps, L drawn from `steps`, drawn anew while its result
    * does not depend on its input. Throws when 100 draws give none that does.
    */
  private def straightLine(nominal: NominalRanges)(
      draws: Draws
  ): (StraightLine, Draws) =
    @tailrec
    def attempt(attempts: Int, draws: Draws): (StraightLine, Draws) =
      if attempts > 100 then
        throw IllegalArgumentException(
          s"$attempts draws gave no function that depends on its input"
        )
      val (length, afterLength) =
        Repetition.drawnNumber(draws, nominal, "steps")
      val (steps, afterSteps) =
        (1 to length).foldLeft((Vector.empty[Step], afterLength))(
          (drawn, index) =>
            val (before, beforeDraws) = drawn
            val (step, afterStep) = drawnStep(nominal, index, beforeDraws)
            (before :+ step, afterStep)
        )
      val function = StraightLine(steps)
      if dependsOnInput(function) then (function, afterSteps)
      else attempt(attempts + 1, afterSteps)
    attempt(1, draws)

  /** The step of the index k (from 1): its operation, then its operands. */
  private def drawnStep(
      nominal: NominalRanges,
      index: Int,
      draws: Draws
  ): (Step, Draws) =
    val (operation, afterOperation) = draws.chosen(Operation.values.toVector)
    operation match
      case Operation.Plus =>
        val (constant, afterConstant) = drawnConstant(nominal, afterOperation)
        (
          Step(operation, Operand.Intermediate(index - 1), constant),
          afterConstant
        )
      case Operation.Maximum | Operation.BitwiseOr =>
        val (earlier, afterEarlier) = afterOperation.number(0 to index - 1)
        val (constant, afterConstant) = drawnConstant(nominal, afterEarlier)
        (
          Step(operation, Operand.Intermediate(earlier), constant),
          afterConstant
        )
      case Operation.Minimum =>
        val (left, afterLeft) = operand(nominal, index, afterOperation)
        val (right, afterRight) = operand(nominal, index, afterLeft)
        (Step(operation, left, right), afterRight)

  /** An earlier intermediate or a constant, with even odds. */
  private def operand(
      nominal: NominalRanges,
      index: Int,
      draws: Draws
  ): (Operand, Draws) =
    val (intermediate, afterKind) = draws.chosen(Vector(true, false))
    if intermediate then
      val (earlier, afterEarlier) = afterKind.number(0 to index - 1)
      (Operand.Intermediate(earlier), afterEarlier)
    else drawnConstant(nominal, afterKind)

  /** A constant of b binary digits, b drawn from `constant_bits`. */
  private def drawnConstant(
      nominal: NominalRanges,
      draws: Draws
  ): (Operand, Draws) =
    val (constant, afterConstant) =
      Repetition.drawnWideNumber(draws, nominal, "constant_bits")
    (Operand.Constant(BigInt(constant)), afterConstant)

  /** A random permutation of 0, ..., count - 1, by Fisher and Yates's shuffle
    * from the last position down.
    */
  private def permutation(count: Int, draws: Draws): (Vector[Int], Draws) =
    (count - 1 to 1 by -1).foldLeft((Vector.range(0, count), draws))(
      (drawn, position) =>
        val (before, beforeDraws) = drawn
        val (other, afterOther) = beforeDraws.number(0 to position)
        (
          before
            .updated(position, before(other))
            .updated(other, before(position)),
          afterOther
        )
    )

  /** The one value of the parameter's range. */
  def single(nominal: NominalRanges, name: String): Int =
    val range = Repetition.range(nominal, name)
    require(range.size == 1 && range.start >= 1, s"one positive $name: $range")
    range.start

  /** The family's name, the prefix of each rung's name. */
  val name: String = "repeated_library_hotspots"

  /** The name of the rung of C calls. */
  def rungName(calls: Int): String = s"${name}_calls_$calls"

  /** The family name of the rung's variant of the calibration: the rung's name,
    * then `_cold` or `_hot` for a calibration variant.
    */
  def familyName(calls: Int, calibration: Calibration): String =
    rungName(calls) + calibration.suffix

  /** The family name of the shape's variant of the rung's calibration:
    * `familyName` with the shape's infix after the family's name.
    */
  def shapedFamilyName(
      shape: Shape,
      calls: Int,
      calibration: Calibration
  ): String =
    s"$name${shape.infix}_calls_$calls${calibration.suffix}"

  /** The test that checks the computed reference against tabling(weak_head)'s
    * reading on small draws.
    */
  val claim: String =
    "gezi.contest.corpora.reductions.LibraryHotspotsReferenceTest"

  /** The C of the rungs, from 10^3 to 10^6: the starting sizes 10^3 to 10^5,
    * and 10^6, at which a reading of about 1 ms per call needs about 1,000 s,
    * so that only a hot loop run without interpreter steps per call answers
    * within a rung's budget.
    */
  val rungCalls: Vector[Int] = Vector(1000, 10000, 100000, 1000000)

  /** The nominal ranges of the rung of C calls, the starting sizes: M from 64
    * to 256, L from 16 to 32, constants of 8 to 12 binary digits and an initial
    * state of 20 to 28, alpha = 2, at R up to 4, a point's sites the four
    * problems of a rung.
    */
  def nominal(calls: Int): NominalRanges = NominalRanges(
    Repetition.repetitionsWithin(4),
    Vector(
      NominalParameter("functions", 64 to 256),
      NominalParameter("steps", 16 to 32),
      NominalParameter("constant_bits", 8 to 12),
      NominalParameter("initial_bits", 20 to 28),
      NominalParameter("calls", calls to calls),
      NominalParameter("exponent", 2 to 2)
    )
  )

  /** The rung of C calls in the spelling, the scored variant. */
  def rung(spelling: Spelling, calls: Int): LibraryHotspots =
    calibrated(spelling, calls, Calibration.Scored)

  /** The rung's variant of the calibration in the spelling. */
  def calibrated(
      spelling: Spelling,
      calls: Int,
      calibration: Calibration
  ): LibraryHotspots =
    LibraryHotspots(
      spelling,
      nominal(calls),
      familyName(calls, calibration),
      calibration
    )

  /** Each rung in both spellings, in increasing C. */
  val rungs: Vector[Vector[LibraryHotspots]] =
    rungCalls.map(calls => Repetition.spellings.map(rung(_, calls)))

  /** The cold and the hot variant of each rung in both spellings, in increasing
    * C; the cold ones for the calibration only, the hot ones scored
    * (`Calibration`).
    */
  val calibrations: Vector[Vector[LibraryHotspots]] =
    for
      calls <- rungCalls
      calibration <- Vector(Calibration.Cold, Calibration.Hot)
    yield Repetition.spellings.map(calibrated(_, calls, calibration))

  /** The shapes other than the family's own, each a family of its own at every
    * shaped rung.
    */
  val otherShapes: Vector[Shape] = Vector(Shape.Inlined, Shape.Nested)

  /** The C of the shaped rungs: the hot ladder's scored rungs since round 20,
    * 10^4 to 10^6.
    */
  val shapedRungCalls: Vector[Int] = Vector(10000, 100000, 1000000)

  /** The shape's variant of the hot rung of C calls in the spelling, drawn from
    * its own family name.
    */
  def shaped(spelling: Spelling, calls: Int, shape: Shape): LibraryHotspots =
    LibraryHotspots(
      spelling,
      nominal(calls),
      shapedFamilyName(shape, calls, Calibration.Hot),
      Calibration.Hot,
      shape
    )

  /** Each other shape's hot rung in both spellings, by shape and in increasing
    * C.
    */
  val shapedRungs: Vector[Vector[LibraryHotspots]] =
    for
      shape <- otherShapes
      calls <- shapedRungCalls
    yield Repetition.spellings.map(shaped(_, calls, shape))
