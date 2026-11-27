package gezi.contest.corpora.reductions

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term
import gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** A rung of a CSES family's ladder: its name, the last part of the family's
  * name, and the ranges its sites are drawn from. Each rung is a family of its
  * own, as the hotspots' rungs are (`LibraryHotspots.rungs`): the twins of a
  * family draw the same data, which variants of several sizes would not.
  */
final case class CsesRung(
    name: String,
    nominal: NominalRanges,
    input: RungInput = RungInput.Written
)

/** How a rung writes its sites' data into a program. */
enum RungInput:

  /** Each datum written out, its size the input's. */
  case Written

  /** A call of a generator of the problems' tree on a seed and sizes
    * (`CsesProblems.seededInput`), so that a program's size does not grow with
    * its input; for a top rung, whose input is as large as CSES's.
    */
  case Seeded

/** A repeated family of the CSES port: the function of a problem of
  * `problems/cses`, written by its definition (`CsesProblems`), applied to R
  * distinct inputs drawn from a seed. The repeated part is the function,
  * written once and let bound, `(λf. [f a1, …, f aR]) F`, and not marked; the
  * non-repeated part is the data of the sites, distinct at every site, so that
  * across sites only code can be reused, never an answer
  * ([[gezi.contest.corpora.reductions]]). A single program is the function
  * applied to one site's data.
  *
  * Both twins draw their data from the family's name (`drawStem`); the state
  * after the data is the respelled twin's, from which it draws the β-expansions
  * of the function (`CsesSpelling`), so that the pair differs only in spelling.
  * The inputs are written as the problem files' headers give their encodings
  * (`CsesEncodings`), never respelled.
  *
  * The ladder ([[gezi.contest.corpora.reductions]]): the bottom rungs are sized
  * by the reference reading, tabling(weak_head), which reads the definition's
  * exponential or polynomial program within its budget there; the top rung is
  * CSES's constraint for the problem, where only the best known algorithm on
  * native representations answers.
  *
  * The native solver: each family's `solved` is the best known algorithm on the
  * family's `Drawn` (`CsesSolutions`), from which a point's reference is
  * computed (`NativelySolved.point`).
  *
  * The traps ([[gezi.contest.corpora.reductions]]): the answers of common wrong
  * solutions, each applied at every site (`wrongAnswers`), so that a candidate
  * is the list a wrong solution would print (`trapCandidates`). A point carries
  * them, computed from the answers of `solved` (`NativelySolved.drawnPoint`,
  * `DrawnPoint.trapCandidates`), to the judge's points writer, which offers
  * them as traps before the second instance's normal forms
  * (`PointsFile.written` in contest-judge). The writer offers traps only to a
  * pure program (`ProgramPurity.pureInstruction`), which every program of these
  * families below their top rungs is, both twins (`CsesPurityLawTest` in
  * contest-judge).
  */
abstract class CsesFamily[Site](val spelling: Spelling, val rung: CsesRung)
    extends RepeatedFamily[CsesFamily.Drawn[Site]]
    with NativelySolved[CsesFamily.Drawn[Site]]:

  /** The problem's name: the name of its file and of its point table. */
  def problem: String

  /** The directory under `problems` that holds the problem's point table,
    * `cses/<problem>` for a problem of `problems/cses`.
    */
  def directory: String = s"${CsesProblems.directory}/$problem"

  /** The corpus name the judge registers the problem's point table under
    * (`CsesPointTable`).
    */
  def corpus: String = s"contest_cses_$problem"

  /** The family's name, the first part of its stem: `repeated_cses_`, the
    * problem and the rung for a problem of `problems/cses`.
    */
  def family: String = CsesFamily.familyName(problem, rung.name)

  final def stem: String = s"$family/${Repetition.spellingName(spelling)}"

  /** The family's name alone: the twins draw the same data. */
  final override def drawStem: String = family

  final def nominal: NominalRanges = rung.nominal

  /** A site drawn from the rung's ranges. */
  protected def site(draws: Draws): (Site, Draws)

  /** The function of the problem, as its file exports it. */
  protected def function(problems: CsesProblems): Configured[NoFacts.type]

  /** The site's data, the function's arguments in order, each a closed term in
    * the encoding the problem's header gives (`CsesEncodings`), or, at a seeded
    * top rung, a call of a generator the problems' tree exports
    * (`CsesProblems.seededInput`), which computes that data from the site's
    * seed and sizes.
    */
  def arguments(problems: CsesProblems, site: Site): Vector[ProblemTerm]

  /** The answers of the common wrong solutions at the site whose right answer
    * is given, each a solution's answer; a wrong solution whose answer is the
    * right one at the site gives the right one.
    */
  def wrongAnswers(site: Site, answer: NativeValue): Vector[NativeValue]

  /** The trap candidates of the draws whose right answers are given: for each
    * common wrong solution, the list of its answers at the sites, when it
    * differs from the list of the right answers at some site.
    */
  final override def trapCandidates(
      drawn: CsesFamily.Drawn[Site],
      answers: Vector[NativeValue]
  ): Vector[DeBruijnTerm] =
    require(
      answers.size == drawn.sites.size,
      s"${answers.size} answers for ${drawn.sites.size} sites"
    )
    val perSite = drawn.sites.zip(answers).map(wrongAnswers.tupled)
    val solutions = perSite.map(_.size).distinct match
      case Vector(count) => count
      case other         =>
        throw IllegalStateException(
          s"the sites have different counts of wrong solutions: $other"
        )
    (0 until solutions).toVector
      .map(solution => perSite.map(_(solution)))
      .filter(_ != answers)
      .map(wrong => NativeValue.Elements(wrong).normalForm)
      .distinct

  protected final def drawn(
      group: ReductionGroup,
      draws: Draws,
      repetitions: Int
  ): CsesFamily.Drawn[Site] =
    val (sites, after) = draws.distinct(repetitions)(site)
    CsesFamily.Drawn(sites, after.state)

  /** A site drawn from the draws, for the tests' laws. */
  private[reductions] def drawnSite(draws: Draws): (Site, Draws) = site(draws)

  /** The function in the spelling, respelled from the state after the data. */
  private def spelledFunction(
      group: ReductionGroup,
      drawn: CsesFamily.Drawn[Site]
  ): ProblemTerm =
    CsesSpelling
      .spelled(function(group.cses), spelling, Draws(drawn.spellingState))
      ._1

  protected final def repeated(
      group: ReductionGroup,
      drawn: CsesFamily.Drawn[Site]
  ): ProblemTerm =
    CsesEncodings.sites(
      spelledFunction(group, drawn),
      drawn.sites.map(arguments(group.cses, _))
    )

  /** The direct single program of the site, the function as the problem's file
    * exports it applied to the site's data, whatever the family's spelling and
    * rung: what the problem's point table (`CsesPoints`) reads.
    */
  final def directProgram(group: ReductionGroup, site: Site): ProblemTerm =
    applied(Term.closed(function(group.cses)), arguments(group.cses, site))

  protected final def singles(
      group: ReductionGroup,
      drawn: CsesFamily.Drawn[Site]
  ): Vector[ProblemTerm] =
    val function = spelledFunction(group, drawn)
    drawn.sites.map(site => applied(function, arguments(group.cses, site)))

/** The draws, the names and the draw helpers of the CSES families. */
object CsesFamily:

  /** The sites, and the state of the draws after them, from which the respelled
    * twin draws its spelling.
    */
  final case class Drawn[Site](sites: Vector[Site], spellingState: Long)

  /** The family of the problem's rung. */
  def familyName(problem: String, rung: String): String =
    s"repeated_cses_${problem}_$rung"

  /** CSES's modulus of counts and powers, 10^9 + 7. */
  val modulus: Int = 1000000007

  /** The seeds a seeded site draws, 1 to 2^30: a Park–Miller state is positive,
    * and 0 would stay 0.
    */
  val seeds: Range.Inclusive = 1 to (1 << 30)

  /** A site's numbers drawn from the ranges: n from `count`, then, written,
    * each number from `value`, or, seeded, a seed (`seeds`) and the range
    * `value`.
    */
  def drawnNumbers(
      draws: Draws,
      ranges: NominalRanges,
      input: RungInput,
      count: String,
      value: String
  ): (NumbersSite, Draws) =
    val (size, afterSize) = drawnParameter(draws, ranges, count)
    input match
      case RungInput.Written =>
        val (written, after) =
          drawnValues(size, afterSize)(drawnParameter(_, ranges, value))
        (NumbersSite(SeededInput.Input.Written(written)), after)
      case RungInput.Seeded =>
        val (seed, after) = between(afterSize, seeds)
        val range = Repetition.range(ranges, value)
        (
          NumbersSite(
            SeededInput.Input.Seeded(
              SeededInput.Numbers(seed, size, range.start, range.end)
            )
          ),
          after
        )

  /** A site whose data is one list of numbers, written or seeded. */
  final case class NumbersSite(input: SeededInput.Input[Vector[Int]]):

    /** The numbers. */
    def numbers: Vector[Int] = input.data

    /** The argument: the list written out, or the generator's call. */
    def argument(problems: CsesProblems): ProblemTerm =
      input.argument(problems, writtenNumbers)

    override def toString: String = s"Site(${input.described(_.toString)})"

  /** A grid of Booleans written out, a list of rows. */
  def writtenGrid(rows: Vector[Vector[Boolean]]): ProblemTerm =
    CsesEncodings.list(
      rows.map(row =>
        CsesEncodings.list(
          row.map(square =>
            if square then CsesEncodings.trueValue else CsesEncodings.falseValue
          )
        )
      )
    )

  /** A list of numbers written out, each converted once
    * (`CsesEncodings.naturals`).
    */
  def writtenNumbers(numbers: Vector[Int]): ProblemTerm =
    val naturals = CsesEncodings.naturals(numbers)
    CsesEncodings.list(numbers.map(naturals))

  /** A number of the range, of any size an `Int` range has: drawn whole when
    * the range has at most 2^15 values (`Draws.number`), otherwise from two
    * draws of 15 bits, reduced to the range.
    */
  def between(draws: Draws, range: Range.Inclusive): (Int, Draws) =
    require(
      range.nonEmpty && range.step == 1,
      s"no number is drawn from $range"
    )
    if range.size <= Draws.highBitsCount then draws.number(range)
    else
      val (high, afterHigh) = draws.number(0 to Draws.highBitsCount - 1)
      val (low, afterLow) = afterHigh.number(0 to Draws.highBitsCount - 1)
      ((range.start + ((high.toLong << 15) | low) % range.size).toInt, afterLow)

  /** The parameter's value, drawn from its nominal range (`between`). */
  def drawnParameter(
      draws: Draws,
      ranges: NominalRanges,
      name: String
  ): (Int, Draws) = between(draws, Repetition.range(ranges, name))

  /** `count` values of the draw, in the order drawn, repeats allowed. */
  def drawnValues[Value](count: Int, draws: Draws)(
      draw: Draws => (Value, Draws)
  ): (Vector[Value], Draws) =
    (1 to count).foldLeft((Vector.empty[Value], draws)) {
      case ((found, current), _) =>
        val (value, after) = draw(current)
        (found :+ value, after)
    }

  /** The values in an order drawn by the Fisher–Yates shuffle, each index drawn
    * by `between`, so that a list longer than 2^15 is shuffled too.
    */
  def shuffled[Value](
      values: Vector[Value],
      draws: Draws
  ): (Vector[Value], Draws) =
    (values.size - 1 to 1 by -1).foldLeft((values, draws)) {
      case ((current, before), last) =>
        val (chosen, next) = between(before, 0 to last)
        (
          current.updated(last, current(chosen)).updated(chosen, current(last)),
          next
        )
    }

  /** Each natural of a list answer plus one, the answer of a solution off by
    * one at every element.
    */
  def eachOffByOne(answer: NativeValue): NativeValue = answer match
    case NativeValue.Elements(values) =>
      NativeValue.Elements(values.map {
        case NativeValue.Binary(digits) =>
          NativeValue.natural(naturalOf(digits) + 1)
        case other => throw IllegalArgumentException(s"no natural: $other")
      })
    case other => throw IllegalArgumentException(s"no list: $other")

  /** Each rung's family in both spellings. */
  def families[Family](
      rungs: Vector[CsesRung],
      make: (Spelling, CsesRung) => Family
  ): Vector[Vector[Family]] =
    rungs.map(rung => Repetition.spellings.map(make(_, rung)))

  /** A natural answer plus one modulo 10^9 + 7, the answer of a solution off by
    * one.
    */
  def offByOne(answer: NativeValue): NativeValue = answer match
    case NativeValue.Binary(digits) =>
      NativeValue.natural((naturalOf(digits) + 1) % modulus)
    case other => throw IllegalArgumentException(s"no natural: $other")

  /** The natural of a canonical numeral's digits, the least significant first.
    */
  def naturalOf(digits: Vector[Boolean]): BigInt = digits.foldRight(BigInt(0))(
    (digit, above) => above * 2 + (if digit then 1 else 0)
  )

/** CSES 1633, Dice Combinations, `dice_combinations n`: the ways to throw dice
  * so that their faces sum to n, modulo 10^9 + 7. A site is n, drawn from the
  * rung's parameter `sum`.
  */
final class DiceCombinations(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[DiceCombinations.Site](spelling, rung):

  val problem: String = "dice_combinations"

  val claim: String =
    "gezi.contest.corpora.reductions.DiceCombinationsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[DiceCombinations.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.diceCombinations(site.sum))
    )

  protected def site(draws: Draws): (DiceCombinations.Site, Draws) =
    val (sum, after) = CsesFamily.drawnParameter(draws, nominal, "sum")
    (DiceCombinations.Site(sum), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.diceCombinations

  def arguments(
      problems: CsesProblems,
      site: DiceCombinations.Site
  ): Vector[ProblemTerm] = Vector(CsesEncodings.natural(site.sum))

  /** A solution off by one in its count. */
  def wrongAnswers(
      site: DiceCombinations.Site,
      answer: NativeValue
  ): Vector[NativeValue] = Vector(CsesFamily.offByOne(answer))

/** The sites and the ladder of `DiceCombinations`. */
object DiceCombinations:

  /** The sum n of a site. */
  final case class Site(sum: Int)

  /** The ladder: sums up to 4 and up to 6, read by the reference reading, and
    * CSES's constraint, 1 ≤ n ≤ 10^6, the sums drawn from its upper half, at
    * most four sites, each as large as a CSES input. MEASURED 2026-11-21 on the
    * programs of bb6ba0942 (binary_subtract writes no top, the constants are
    * Scott numerals), the respelled twins with their literals' spines kept
    * whole (`CsesSpelling`), by a scratch probe in contest-corpora's tests
    * (CPUs 0, 1, 8 and 9 of contest.slice, nice 10, the 1-minute load about 8),
    * tabling(weak_head) knowing top (`ReadingState.knowingTop`) within
    * 20,000,000 steps and 400,000 tables, each reading one normal form: the
    * single program of n (the function as its file exports it, applied to the
    * site's data) took, for n from 1 to 7, 2,202, 3,383, 5,256, 9,487, 16,903,
    * 32,947 and 61,791 steps and 1,051, 1,564, 2,357, 4,163, 7,313, 14,089 and
    * 26,292 tables, about 1.75 times more a unit of n (the sequences are built
    * and counted); the repeated program of the seed 20261031 at sum_4 and R = 4
    * took 13,518 steps and 5,772 tables (respelled 21,167 and 8,641), at sum_6
    * and R = 6 50,624 and 21,157 (respelled 99,911 and 40,572), within the
    * reference reading's 50,000 tables (`ReadingState.defaultTableLimit`); a
    * sum of 7 at every site would pass them.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "sum_4",
      NominalRanges(
        Repetition.repetitionsWithin(4),
        Vector(NominalParameter("sum", 1 to 4))
      )
    ),
    CsesRung(
      "sum_6",
      NominalRanges(
        Repetition.repetitionsWithin(6),
        Vector(NominalParameter("sum", 1 to 6))
      )
    ),
    CsesRung(
      "sum_1000000",
      NominalRanges(1 to 4, Vector(NominalParameter("sum", 500000 to 1000000)))
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[DiceCombinations]] =
    CsesFamily.families(rungs, DiceCombinations(_, _))

/** CSES 1634, Minimizing Coins, `minimizing_coins coins x`: the fewest coins of
  * the values, each usable any number of times, that sum to x, or none. A site
  * is k distinct coin values drawn from 1 to the parameter `value`'s end, k
  * from the parameter `coins`, in the order drawn, and x from the parameter
  * `target`.
  */
final class MinimizingCoins(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[MinimizingCoins.Site](spelling, rung):

  val problem: String = "minimizing_coins"

  val claim: String =
    "gezi.contest.corpora.reductions.MinimizingCoinsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[MinimizingCoins.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.Optional(
        CsesSolutions
          .minimizingCoins(site.coins, site.target)
          .map(NativeValue.natural)
      )
    )

  protected def site(draws: Draws): (MinimizingCoins.Site, Draws) =
    val (count, afterCount) = CsesFamily.drawnParameter(draws, nominal, "coins")
    val values = Repetition.range(nominal, "value")
    val (coins, afterCoins) = afterCount.distinct(math.min(count, values.size))(
      CsesFamily.between(_, values)
    )
    val (target, afterTarget) =
      CsesFamily.drawnParameter(afterCoins, nominal, "target")
    (MinimizingCoins.Site(coins, target), afterTarget)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.minimizingCoins

  def arguments(
      problems: CsesProblems,
      site: MinimizingCoins.Site
  ): Vector[ProblemTerm] =
    Vector(
      CsesEncodings.list(site.coins.map(coin => CsesEncodings.natural(coin))),
      CsesEncodings.natural(site.target)
    )

  /** A solution off by one in its count of coins, and one that answers zero
    * coins where no coins sum to x (its table started at zero, never marked
    * unreachable).
    */
  def wrongAnswers(
      site: MinimizingCoins.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Optional(Some(NativeValue.Binary(digits))) =>
      Vector(
        NativeValue.Optional(
          Some(NativeValue.natural(CsesFamily.naturalOf(digits) + 1))
        ),
        answer
      )
    case NativeValue.Optional(None) =>
      Vector(answer, NativeValue.Optional(Some(NativeValue.natural(0))))
    case other =>
      throw IllegalArgumentException(s"no option of a natural: $other")

/** The sites and the ladder of `MinimizingCoins`. */
object MinimizingCoins:

  /** The coin values and the target x of a site. */
  final case class Site(coins: Vector[Int], target: Int)

  /** The ladder: small coins and targets read by the reference reading, and
    * CSES's constraints, 1 ≤ n ≤ 100 coins, 1 ≤ x ≤ 10^6 and 1 ≤ c ≤ 10^6, the
    * counts and the targets drawn from their upper halves, at most four sites,
    * each as large as a CSES input. MEASURED 2026-11-21 by the probe of
    * `DiceCombinations.rungs`, on the same programs: the single program of the
    * coins (1, 2) took 4,644 steps and 2,126 tables at x = 4, 10,780 and 4,758
    * at 6, 27,525 and 11,914 at 8, and of (1, 2, 3) at 8 59,316 and 25,310
    * (every sequence of coins is built); the repeated program of the seed
    * 20261031 at target_6 and R = 24 took 27,718 steps and 11,726 tables
    * (respelled 45,047 and 18,360), at target_8 and R = 4 3,746 and 1,720
    * (respelled 6,539 and 2,868) and at R = 64 160,304 and 66,317 (respelled
    * 316,861 and 126,942), past the reference reading's 50,000 tables at that
    * R, which the points do not need (`NativelySolved`).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "target_6",
      NominalRanges(
        Repetition.repetitionsWithin(24),
        Vector(
          NominalParameter("coins", 1 to 2),
          NominalParameter("value", 1 to 4),
          NominalParameter("target", 1 to 6)
        )
      )
    ),
    CsesRung(
      "target_8",
      NominalRanges(
        Repetition.repetitionsWithin(64),
        Vector(
          NominalParameter("coins", 1 to 3),
          NominalParameter("value", 1 to 4),
          NominalParameter("target", 1 to 8)
        )
      )
    ),
    CsesRung(
      "target_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("coins", 50 to 100),
          NominalParameter("value", 1 to 1000000),
          NominalParameter("target", 500000 to 1000000)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[MinimizingCoins]] =
    CsesFamily.families(rungs, MinimizingCoins(_, _))

/** CSES 1667, Message Route, `message_route n connections`: the fewest
  * computers on a route from computer 1 to computer n over the undirected
  * connections, or none. A site is n, drawn from the parameter `computers`, and
  * m distinct connections between distinct computers, m drawn from the
  * parameter `connections` and at most the pairs there are, each written in an
  * order drawn, in the order drawn. At the top rung the connections are
  * generated from a seed (`SeededInput.Connections`): each joins two distinct
  * computers, and two of them may join the same pair, which CSES's input
  * excludes and the problem's definition, a walk's recursion, does not depend
  * on.
  */
final class MessageRoute(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[MessageRoute.Site](spelling, rung):

  val problem: String = "message_route"

  val claim: String =
    "gezi.contest.corpora.reductions.MessageRouteReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[MessageRoute.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.Optional(
        CsesSolutions
          .messageRoute(site.computers, site.connections)
          .map(NativeValue.natural)
      )
    )

  protected def site(draws: Draws): (MessageRoute.Site, Draws) =
    val (computers, afterComputers) =
      CsesFamily.drawnParameter(draws, nominal, "computers")
    val (wanted, afterWanted) =
      CsesFamily.drawnParameter(afterComputers, nominal, "connections")
    rung.input match
      case RungInput.Written =>
        val pairs = computers.toLong * (computers - 1) / 2
        val count = math.min(wanted.toLong, pairs).toInt
        val (connections, after) =
          MessageRoute.connections(computers, count, afterWanted)
        (
          MessageRoute.Site(computers, SeededInput.Input.Written(connections)),
          after
        )
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterWanted, CsesFamily.seeds)
        (
          MessageRoute.Site(
            computers,
            SeededInput.Input.Seeded(
              SeededInput.Connections(seed, wanted, computers)
            )
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.messageRoute

  def arguments(
      problems: CsesProblems,
      site: MessageRoute.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(connections) =>
        val computers = CsesEncodings.naturals(
          site.computers +: connections.flatMap((from, to) => Vector(from, to))
        )
        Vector(
          computers(site.computers),
          CsesEncodings.list(
            connections.map((from, to) =>
              CsesEncodings.pair(computers(from), computers(to))
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(
          CsesEncodings.natural(site.computers),
          generator.argument(problems)
        )

  /** A solution that counts the connections of a shortest route instead of its
    * computers, and one that answers zero where no route exists.
    */
  def wrongAnswers(
      site: MessageRoute.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Optional(Some(NativeValue.Binary(digits))) =>
      Vector(
        NativeValue.Optional(
          Some(NativeValue.natural(CsesFamily.naturalOf(digits) - 1))
        ),
        answer
      )
    case NativeValue.Optional(None) =>
      Vector(answer, NativeValue.Optional(Some(NativeValue.natural(0))))
    case other =>
      throw IllegalArgumentException(s"no option of a natural: $other")

/** The sites, the drawing of connections and the ladder of `MessageRoute`. */
object MessageRoute:

  /** The count of computers and the connections of a site, each a pair of
    * distinct computers from 1 to n, written or seeded.
    */
  final case class Site(
      computers: Int,
      input: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The connections. */
    def connections: Vector[(Int, Int)] = input.data

    override def toString: String =
      s"Site($computers,${input.described(_.toString)})"

  /** `count` distinct connections among the computers, in an order drawn, each
    * written from either end with even odds: drawn whole by a shuffle of every
    * pair when the pairs are at most four times as many as the count, otherwise
    * drawn one at a time, a pair drawn again drawn anew.
    */
  def connections(
      computers: Int,
      count: Int,
      draws: Draws
  ): (Vector[(Int, Int)], Draws) =
    val pairs = computers.toLong * (computers - 1) / 2
    val (unordered, afterPairs) =
      if pairs <= 4L * count then
        val every = for
          from <- (1 to computers).toVector
          to <- (from + 1 to computers).toVector
        yield (from, to)
        val (shuffled, after) =
          (every.size - 1 to 1 by -1).foldLeft((every, draws)) {
            case ((current, before), last) =>
              val (chosen, next) = before.number(0 to last)
              (
                current
                  .updated(last, current(chosen))
                  .updated(chosen, current(last)),
                next
              )
          }
        (shuffled.take(count), after)
      else drawnApart(computers, count, draws, Vector.empty, Set.empty)
    unordered.foldLeft((Vector.empty[(Int, Int)], afterPairs)) {
      case ((found, current), (from, to)) =>
        val (flipped, after) = current.chosen(Vector(false, true))
        (found :+ (if flipped then (to, from) else (from, to)), after)
    }

  /** `count` distinct connections drawn one at a time, a pair drawn again drawn
    * anew, the pairs found kept in a set as well, so that a CSES-sized graph is
    * drawn in time linear in its connections (`Draws.distinct` looks a value up
    * in the values found, quadratic at 2 · 10^5).
    */
  @scala.annotation.tailrec
  private def drawnApart(
      computers: Int,
      count: Int,
      draws: Draws,
      found: Vector[(Int, Int)],
      seen: Set[(Int, Int)]
  ): (Vector[(Int, Int)], Draws) =
    if found.size == count then (found, draws)
    else
      val (first, afterFirst) = CsesFamily.between(draws, 1 to computers)
      val (second, afterSecond) =
        CsesFamily.between(afterFirst, 1 to computers - 1)
      val other = if second >= first then second + 1 else second
      val connection = (math.min(first, other), math.max(first, other))
      if seen.contains(connection) then
        drawnApart(computers, count, afterSecond, found, seen)
      else
        drawnApart(
          computers,
          count,
          afterSecond,
          found :+ connection,
          seen + connection
        )

  /** The ladder: small graphs read by the reference reading, and CSES's
    * constraints, 2 ≤ n ≤ 10^5 and 1 ≤ m ≤ 2 · 10^5, drawn from their upper
    * halves, at most four sites, each as large as a CSES input. MEASURED
    * 2026-11-21 by the probe of `DiceCombinations.rungs`, on the same programs:
    * the single program of the path 1, 2, …, 8 with the chords (1, 4), (3, 6)
    * and (5, 8) (10 connections) took 6,796 steps and 3,084 tables; the
    * repeated program of the seed 20261031 at computers_5 and R = 64 took
    * 28,725 steps and 12,722 tables (respelled 41,966 and 17,807), at
    * computers_8 and R = 4 7,580 and 3,487 (respelled 13,638 and 6,012) and at
    * R = 256 283,145 and 126,155 (respelled 494,168 and 212,450), past the
    * reference reading's 50,000 tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "computers_5",
      NominalRanges(
        Repetition.repetitionsWithin(64),
        Vector(
          NominalParameter("computers", 2 to 5),
          NominalParameter("connections", 1 to 6)
        )
      )
    ),
    CsesRung(
      "computers_8",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("computers", 2 to 8),
          NominalParameter("connections", 1 to 12)
        )
      )
    ),
    CsesRung(
      "computers_100000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("computers", 50000 to 100000),
          NominalParameter("connections", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[MessageRoute]] =
    CsesFamily.families(rungs, MessageRoute(_, _))

/** CSES 1192, Counting Rooms, `counting_rooms map`: the rooms of a map of floor
  * (true) and wall (false), a room a largest set of floor squares joined by
  * steps left, right, up and down. A site is a map of r rows and c columns, r
  * and c drawn from the parameters `rows` and `columns`, each square floor or
  * wall with even odds, generated from a seed at the top rung
  * (`SeededInput.Grid`, odds 2).
  */
final class CountingRooms(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[CountingRooms.Site](spelling, rung):

  val problem: String = "counting_rooms"

  val claim: String =
    "gezi.contest.corpora.reductions.CountingRoomsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[CountingRooms.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.countingRooms(site.rows))
    )

  protected def site(draws: Draws): (CountingRooms.Site, Draws) =
    val (rows, afterRows) = CsesFamily.drawnParameter(draws, nominal, "rows")
    val (columns, afterColumns) =
      CsesFamily.drawnParameter(afterRows, nominal, "columns")
    rung.input match
      case RungInput.Written =>
        val (squares, after) =
          (1 to rows).foldLeft((Vector.empty[Vector[Boolean]], afterColumns)) {
            case ((found, current), _) =>
              val (row, next) =
                (1 to columns).foldLeft((Vector.empty[Boolean], current)) {
                  case ((cells, before), _) =>
                    val (floor, afterFloor) = before.chosen(Vector(true, false))
                    (cells :+ floor, afterFloor)
                }
              (found :+ row, next)
          }
        (CountingRooms.Site(SeededInput.Input.Written(squares)), after)
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterColumns, CsesFamily.seeds)
        (
          CountingRooms.Site(
            SeededInput.Input.Seeded(
              SeededInput
                .Grid(seed, rows, columns, 2, SeededInput.Corner.Neither)
            )
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.countingRooms

  def arguments(
      problems: CsesProblems,
      site: CountingRooms.Site
  ): Vector[ProblemTerm] =
    Vector(site.input.argument(problems, CsesFamily.writtenGrid))

  /** A solution off by one in its count of rooms. */
  def wrongAnswers(
      site: CountingRooms.Site,
      answer: NativeValue
  ): Vector[NativeValue] = Vector(CsesFamily.offByOne(answer))

/** The sites and the ladder of `CountingRooms`. */
object CountingRooms:

  /** The rows of a site's map, true for floor; written one row a line, `.` for
    * floor and `#` for wall, as CSES writes a map.
    */
  final case class Site(input: SeededInput.Input[Vector[Vector[Boolean]]]):

    /** The rows. */
    def rows: Vector[Vector[Boolean]] = input.data

    override def toString: String =
      input.described(
        _.map(_.map(floor => if floor then '.' else '#').mkString)
          .mkString("Site(", "/", ")")
      )

  /** The ladder: small maps read by the reference reading, and CSES's
    * constraint, 1 ≤ n, m ≤ 1000, drawn from the upper half, at most four
    * sites, each as large as a CSES input. MEASURED 2026-11-21 by the probe of
    * `DiceCombinations.rungs`, on the same programs: the single program of a
    * map all floor of 2 × 2 squares took 3,773 steps and 1,746 tables, 3 × 3
    * 13,543 and 5,733, 3 × 4 34,048 and 13,747 and 4 × 4 74,936 and 29,597
    * (about f^3 for f floor squares); the repeated program of the seed 20261031
    * at squares_9 and R = 4 took 5,037 steps and 2,285 tables (respelled 8,804
    * and 3,817) and at R = 256 382,851 and 157,056 (respelled 581,451 and
    * 231,264), at squares_16 and R = 4 2,969 and 1,395 (respelled 3,890 and
    * 1,759), and at R = 256 both twins stopped at the probe's 400,000 tables
    * (direct after 1,000,116 steps, respelled 964,185), past the reference
    * reading's 50,000, which the points do not need (`NativelySolved`).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "squares_9",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("rows", 1 to 3),
          NominalParameter("columns", 1 to 3)
        )
      )
    ),
    CsesRung(
      "squares_16",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("rows", 1 to 4),
          NominalParameter("columns", 1 to 4)
        )
      )
    ),
    CsesRung(
      "squares_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("rows", 500 to 1000),
          NominalParameter("columns", 500 to 1000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[CountingRooms]] =
    CsesFamily.families(rungs, CountingRooms(_, _))

/** CSES 1095, Exponentiation, `exponentiation a b`: a^b modulo 10^9 + 7, 0^0
  * being 1. A site is a and b, drawn from the parameters `base` and `exponent`.
  */
final class Exponentiation(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[Exponentiation.Site](spelling, rung):

  val problem: String = "exponentiation"

  val claim: String =
    "gezi.contest.corpora.reductions.ExponentiationReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[Exponentiation.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.exponentiation(site.base, site.exponent)
      )
    )

  protected def site(draws: Draws): (Exponentiation.Site, Draws) =
    val (base, afterBase) = CsesFamily.drawnParameter(draws, nominal, "base")
    val (exponent, afterExponent) =
      CsesFamily.drawnParameter(afterBase, nominal, "exponent")
    (Exponentiation.Site(base, exponent), afterExponent)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.exponentiation

  def arguments(
      problems: CsesProblems,
      site: Exponentiation.Site
  ): Vector[ProblemTerm] =
    Vector(
      CsesEncodings.natural(site.base),
      CsesEncodings.natural(site.exponent)
    )

  /** A solution off by one in its power, one that takes 0^0 for 0, and one that
    * forgets the modulus, a^b exactly, where a^b has at most
    * `Exponentiation.unreducedBits` bits (a larger one is no trap a judgment
    * point could carry), the right answer otherwise.
    */
  def wrongAnswers(
      site: Exponentiation.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    val zeroPower = if site.base == 0 && site.exponent == 0 then
      NativeValue.natural(0)
    else answer
    val bits = BigInt(site.base).bitLength.toLong * site.exponent
    val unreduced = if bits <= Exponentiation.unreducedBits then
      NativeValue.natural(BigInt(site.base).pow(site.exponent))
    else answer
    Vector(CsesFamily.offByOne(answer), zeroPower, unreduced)

/** The sites and the ladder of `Exponentiation`. */
object Exponentiation:

  /** The base a and the exponent b of a site. */
  final case class Site(base: Int, exponent: Int)

  /** The most bits of an unreduced power written as a trap. */
  val unreducedBits: Long = 4096

  /** The ladder: small powers read by the reference reading, and CSES's
    * constraint, 0 ≤ a, b ≤ 10^9. CSES asks up to 2 · 10^5 powers in one input,
    * more than the 256 sites of a point (`Repetition.repetitions`). MEASURED
    * 2026-11-21 by the probe of `DiceCombinations.rungs`, on the same programs:
    * the single program of 0^0 took 1,418 steps and 711 tables, 2^4 2,917 and
    * 1,384, 3^8 7,767 and 3,500, 7^8 16,402 and 7,131, 7^12 37,428 and 16,308,
    * 2^30 25,374 and 10,869, and 15^16 115,768 and 50,783, past the reference
    * reading's 50,000 tables (b products of numbers of up to b log a bits); the
    * repeated program of the seed 20261031 at exponent_4 and R = 20 took 9,877
    * steps and 4,303 tables (respelled 16,689 and 7,061), at exponent_8 and R =
    * 4 18,788 and 8,218 (respelled 34,365 and 14,503) and at R = 72 149,054 and
    * 62,692 (respelled 225,311 and 92,209), past the reference reading's 50,000
    * tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "exponent_4",
      NominalRanges(
        Repetition.repetitionsWithin(20),
        Vector(
          NominalParameter("base", 0 to 3),
          NominalParameter("exponent", 0 to 4)
        )
      )
    ),
    CsesRung(
      "exponent_8",
      NominalRanges(
        Repetition.repetitionsWithin(72),
        Vector(
          NominalParameter("base", 0 to 7),
          NominalParameter("exponent", 0 to 8)
        )
      )
    ),
    CsesRung(
      "exponent_1000000000",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("base", 0 to 1000000000),
          NominalParameter("exponent", 0 to 1000000000)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[Exponentiation]] =
    CsesFamily.families(rungs, Exponentiation(_, _))

/** Every CSES family, each rung in both spellings. */
object CsesFamilies:

  /** Each problem's rungs, each in both spellings: the first batch, then the
    * second (`CsesFamiliesSecondBatch.scala`), then the third
    * (`CsesFamiliesThirdBatch.scala`), then the fourth
    * (`CsesFamiliesFourthBatch.scala`), then the two subfamilies of
    * `problems/speculative_untabling`'s weighted paths
    * (`SpeculativeUntabling.scala`), built as CSES families are.
    */
  private val problems: Vector[Vector[Vector[CsesFamily[?]]]] = Vector(
    DiceCombinations.families,
    MinimizingCoins.families,
    MessageRoute.families,
    CountingRooms.families,
    Exponentiation.families,
    CoinCombinationsOrdered.families,
    CoinCombinationsUnordered.families,
    RemovingDigits.families,
    GridPaths.families,
    BookShop.families,
    ShortestRoutesSingleSource.families,
    ShortestRoutesQueries.families,
    CountingDivisors.families,
    BinomialCoefficients.families,
    DistinctNumbers.families,
    MoneySums.families,
    RectangleCutting.families,
    IncreasingSubsequence.families,
    ArrayDescription.families,
    BuildingRoads.families,
    RoadReparation.families,
    GameRoutes.families,
    StaticRangeSums.families,
    TrailingZeros.families,
    SumOfDivisors.families,
    ExponentiationTwo.families,
    FerrisWheel.families,
    MissingNumber.families,
    Repetitions.families,
    StaticRangeMinimums.families,
    StringMatching.families,
    SubarraySums.families,
    SumOfTwoValues.families,
    TreeDiameter.families,
    TreeMatching.families,
    WeightedPaths.distinctFamilies,
    WeightedPaths.recurringFamilies
  )

  val all: Vector[Vector[CsesFamily[?]]] = problems.flatten

  /** The variants of each problem's top rung, CSES's constraint, whose programs
    * a law that builds programs of every variant leaves out: a site there is a
    * CSES input, up to 2 · 10^5 connections, flights or roads, 10^6 squares,
    * letters or text, 10^5 queries or 2 · 10^5 numbers or nodes, or a graph of
    * weighted paths of up to 10^5 nodes.
    */
  val atConstraints: Vector[CsesFamily[?]] =
    problems.flatMap(_.lastOption.toVector.flatten)
