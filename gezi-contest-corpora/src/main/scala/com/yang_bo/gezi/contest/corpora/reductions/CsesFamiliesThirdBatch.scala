package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.ir.{Configured, NoFacts}
import com.yang_bo.gezi.frontend.Term

// The CSES families of the third batch, built as the first batch's are (`CsesFamily`, `CsesFamilies.scala`), each
// rung in both spellings.

/** CSES 1745, Money Sums, `money_sums coins`: the sums that a nonempty set of
  * the coins makes, each once, summed. A site is n coins, n from the parameter
  * `coins`, each value from the parameter `value`, a value repeated allowed, as
  * CSES allows it.
  */
final class MoneySums(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[MoneySums.Site](spelling, rung):

  val problem: String = "money_sums"

  val claim: String = "com.yang_bo.gezi.contest.corpora.reductions.MoneySumsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[MoneySums.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.moneySums(IArray.from(site.coins)))
    )

  protected def site(draws: Draws): (MoneySums.Site, Draws) =
    val (count, afterCount) = CsesFamily.drawnParameter(draws, nominal, "coins")
    val (coins, after) = CsesFamily.drawnValues(count, afterCount)(
      CsesFamily.drawnParameter(_, nominal, "value")
    )
    (MoneySums.Site(coins), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.moneySums

  def arguments(
      problems: CsesProblems,
      site: MoneySums.Site
  ): Vector[ProblemTerm] =
    val naturals = CsesEncodings.naturals(site.coins)
    Vector(CsesEncodings.list(site.coins.map(naturals)))

  /** A solution that sums every non-empty subset's sum, a sum made by several
    * subsets counted once for each: each coin is in half of the subsets, so the
    * sum of the coins times 2^(n − 1).
    */
  def wrongAnswers(
      site: MoneySums.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        site.coins.map(BigInt(_)).sum * BigInt(2).pow(
          math.max(0, site.coins.size - 1)
        )
      )
    )

/** The sites and the ladder of `MoneySums`. */
object MoneySums:

  /** The coin values of a site. */
  final case class Site(coins: Vector[Int])

  /** The ladder: up to 4 coins, and up to 6, the most whose single program the
    * reference reading reads within its 50,000 tables, 7 coins passing them
    * (measured when the problem was written), and CSES's constraints, 1 ≤ n ≤
    * 100 and 1 ≤ x ≤ 1000, the counts drawn from the upper half, at most four
    * sites. MEASURED 2026-11-22 on f0edb710a with the rungs as they are here,
    * by a scratch probe in contest-corpora's tests (CPUs 4 and 5 of
    * contest.slice, nice 10, the 1-minute load about 30), tabling(weak_head)
    * knowing top (`ReadingState.knowingTop`) within 20,000,000 steps and
    * 200,000 tables, each reading one normal form: of the repeated programs of
    * the seeds 0 to 99 at R = 1 and 2 at the bottom rung, the most tables were
    * 9,740 (direct, 23,218 steps) and 17,822 (respelled, 42,798); of the single
    * programs of the seeds 0 to 29 at the middle rung, 37,761 (direct, 92,369
    * steps) and 68,045 (respelled, 170,143 steps; 5 of the 30 past the
    * reference reading's 50,000 tables). The repeated program of the seed
    * 20261031 at coins_6 and R = 4 took 27,547 tables (respelled 64,862) and at
    * R = 16 143,479 (the respelled twin stopped at the probe's 200,000), past
    * the reference reading's 50,000 at those R, which the points do not need
    * (`NativelySolved`).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "coins_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("coins", 1 to 4),
          NominalParameter("value", 1 to 8)
        )
      )
    ),
    CsesRung(
      "coins_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("coins", 1 to 6),
          NominalParameter("value", 1 to 8)
        )
      )
    ),
    CsesRung(
      "coins_100",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("coins", 50 to 100),
          NominalParameter("value", 1 to 1000)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[MoneySums]] =
    CsesFamily.families(rungs, MoneySums(_, _))

/** CSES 1744, Rectangle Cutting, `rectangle_cutting a b`: the fewest cuts, each
  * along a line between units from edge to edge of one piece, after which every
  * piece of an a by b rectangle is a square. A site is a and b, drawn from the
  * parameters `first` and `second`, each at least 1 as the problem's premise
  * asks.
  */
final class RectangleCutting(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[RectangleCutting.Site](spelling, rung):

  val problem: String = "rectangle_cutting"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.RectangleCuttingReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[RectangleCutting.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.rectangleCutting(site.first, site.second)
      )
    )

  protected def site(draws: Draws): (RectangleCutting.Site, Draws) =
    val (first, afterFirst) = CsesFamily.drawnParameter(draws, nominal, "first")
    val (second, after) =
      CsesFamily.drawnParameter(afterFirst, nominal, "second")
    (RectangleCutting.Site(first, second), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.rectangleCutting

  def arguments(
      problems: CsesProblems,
      site: RectangleCutting.Site
  ): Vector[ProblemTerm] =
    Vector(
      CsesEncodings.natural(site.first),
      CsesEncodings.natural(site.second)
    )

  /** The greedy solution that cuts off the largest square it can, again and
    * again (`RectangleCutting.greedyCuts`).
    */
  def wrongAnswers(
      site: RectangleCutting.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(RectangleCutting.greedyCuts(site.first, site.second))
    )

/** The sites, the greedy count and the ladder of `RectangleCutting`. */
object RectangleCutting:

  /** The sides a and b of a site. */
  final case class Site(first: Int, second: Int)

  /** The cuts of the greedy solution, which cuts the largest square off the
    * rectangle and goes on with the rest: the squares it cuts are the quotients
    * of Euclid's algorithm on the sides, summed, and the cuts are one fewer
    * than the squares.
    */
  def greedyCuts(first: Int, second: Int): BigInt =
    @scala.annotation.tailrec
    def squares(larger: Int, smaller: Int, found: Long): Long =
      if smaller == 0 then found
      else squares(smaller, larger % smaller, found + larger / smaller)
    BigInt(squares(math.max(first, second), math.min(first, second), 0L) - 1)

  /** The ladder: rectangles of up to 3 by 4, and up to 4 by 5, the largest
    * whose single program the reference reading reads within its 50,000 tables,
    * 4 by 6 passing them (measured when the problem was written), and CSES's
    * constraint, 1 ≤ a, b ≤ 500, the sides drawn from its upper half, at most
    * four sites. MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the
    * repeated programs at the bottom rung, the most tables were 9,896 (direct,
    * 23,337 steps) and 25,984 (respelled, 63,760 steps; 6 of the 200 above
    * 20,000); of the single programs at the middle rung, 37,554 (direct, 89,699
    * steps) and 92,816 (respelled, 231,512 steps; 1 of the 30 past 50,000). The
    * bottom rung was first sides up to 4 by 4, where the respelled programs of
    * the seeds 0 to 59 read up to 34,574 tables, 10 of the 120 above 20,000.
    * The greedy solution's first wrong count is at 5 by 6, so no site below the
    * top rung offers its trap: by the same probe, none of the seeds 0 to 399 at
    * R = 1 of either lower rung offers one, and each of the seeds 0 to 2 of the
    * top rung does.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "sides_3_by_4",
      NominalRanges(
        Repetition.repetitionsWithin(12),
        Vector(
          NominalParameter("first", 1 to 3),
          NominalParameter("second", 1 to 4)
        )
      )
    ),
    CsesRung(
      "sides_4_by_5",
      NominalRanges(
        Repetition.repetitionsWithin(20),
        Vector(
          NominalParameter("first", 1 to 4),
          NominalParameter("second", 1 to 5)
        )
      )
    ),
    CsesRung(
      "sides_500_by_500",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("first", 250 to 500),
          NominalParameter("second", 250 to 500)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[RectangleCutting]] =
    CsesFamily.families(rungs, RectangleCutting(_, _))

/** CSES 1145, Increasing Subsequence, `increasing_subsequence numbers`: the
  * length of the longest strictly increasing subsequence. A site is n numbers,
  * n from the parameter `numbers`, each from the parameter `value`, whose range
  * is small enough at every rung that values repeat.
  */
final class IncreasingSubsequence(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[IncreasingSubsequence.Site](spelling, rung):

  val problem: String = "increasing_subsequence"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.IncreasingSubsequenceReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[IncreasingSubsequence.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.increasingSubsequence(IArray.from(site.numbers))
      )
    )

  protected def site(draws: Draws): (IncreasingSubsequence.Site, Draws) =
    CsesFamily.drawnNumbers(draws, nominal, rung.input, "numbers", "value")

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.increasingSubsequence

  def arguments(
      problems: CsesProblems,
      site: IncreasingSubsequence.Site
  ): Vector[ProblemTerm] = Vector(site.argument(problems))

  /** A solution that takes the longest non-decreasing subsequence, which
    * differs only where the list repeats a value.
    */
  def wrongAnswers(
      site: IncreasingSubsequence.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        IncreasingSubsequence.longestNonDecreasing(site.numbers)
      )
    )

/** The sites, the non-decreasing length and the ladder of
  * `IncreasingSubsequence`.
  */
object IncreasingSubsequence:

  /** The numbers of a site, written or seeded. */
  type Site = CsesFamily.NumbersSite

  /** The length of the longest non-decreasing subsequence, by patience sorting
    * that places a number after every end equal to it: for each length, the
    * least number that ends a non-decreasing subsequence of that length, the
    * place of a number the first end above it, found by binary search, in O(n
    * log n) comparisons.
    */
  def longestNonDecreasing(numbers: Vector[Int]): BigInt =
    @scala.annotation.tailrec
    def place(ends: Vector[Int], value: Int, low: Int, high: Int): Int =
      if low >= high then low
      else
        val middle = (low + high) >>> 1
        if ends(middle) <= value then place(ends, value, middle + 1, high)
        else place(ends, value, low, middle)
    val ends = numbers.foldLeft(Vector.empty[Int]) { (before, value) =>
      val found = place(before, value, 0, before.size)
      if found == before.size then before :+ value
      else before.updated(found, value)
    }
    BigInt(ends.size)

  /** The ladder: up to 6 numbers, and up to 10, the most whose single program
    * the reference reading reads within its 50,000 tables, 11 numbers passing
    * them (measured when the problem was written), each of few values, so that
    * values repeat; and CSES's constraints, 1 ≤ n ≤ 2 · 10^5 and 1 ≤ x ≤ 10^9,
    * the counts drawn from the upper half, at most four sites, the values drawn
    * from 1 to 10^5 so that they repeat there too: with values drawn from 1 to
    * 10^9, none of the seeds 0 to 2 of the top rung offered the trap, and with
    * values to 10^5 each of them does (by the same probe). MEASURED 2026-11-22
    * by the probe of `MoneySums.rungs`: of the repeated programs at the bottom
    * rung, the most tables were 6,001 (direct, 13,879 steps) and 13,820
    * (respelled, 32,300 steps); of the single programs at the middle rung,
    * 37,170 (direct, 87,457 steps) and 94,331 (respelled, 218,542 steps; 3 of
    * the 30 past 50,000).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "numbers_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 6),
          NominalParameter("value", 1 to 8)
        )
      )
    ),
    CsesRung(
      "numbers_10",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 10),
          NominalParameter("value", 1 to 16)
        )
      )
    ),
    CsesRung(
      "numbers_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("numbers", 100000 to 200000),
          NominalParameter("value", 1 to 100000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[IncreasingSubsequence]] =
    CsesFamily.families(rungs, IncreasingSubsequence(_, _))

/** CSES 1746, Array Description, `array_description m entries`: the ways to
  * give each unknown entry (0) a value from 1 to m so that every two neighbours
  * differ by at most 1, modulo 10^9 + 7. A site is m, from the parameter
  * `bound`, and n entries, n from the parameter `entries`: a walk of values
  * from 1 to m whose first value is drawn and each next one is the one before
  * it, one more or one less, kept within 1 to m, each entry then hidden
  * (written 0) with even odds. So m ≥ 1, the array is not empty and every known
  * entry is from 1 to m, as the problem's premise asks, and every array has at
  * least one filling, the walk.
  */
final class ArrayDescription(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[ArrayDescription.Site](spelling, rung):

  val problem: String = "array_description"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.ArrayDescriptionReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[ArrayDescription.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.arrayDescription(site.upper, IArray.from(site.entries))
      )
    )

  protected def site(draws: Draws): (ArrayDescription.Site, Draws) =
    val (upper, afterUpper) = CsesFamily.drawnParameter(draws, nominal, "bound")
    val (count, afterCount) =
      CsesFamily.drawnParameter(afterUpper, nominal, "entries")
    rung.input match
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterCount, CsesFamily.seeds)
        (
          ArrayDescription.Site(
            upper,
            SeededInput.Input.Seeded(SeededInput.Walk(seed, count, upper))
          ),
          after
        )
      case RungInput.Written =>
        val (first, afterFirst) = CsesFamily.between(afterCount, 1 to upper)
        val (walk, afterWalk) =
          (2 to count).foldLeft((Vector(first), afterFirst)) {
            case ((found, current), _) =>
              val (step, next) = CsesFamily.between(current, -1 to 1)
              (found :+ math.min(upper, math.max(1, found.last + step)), next)
          }
        val (entries, after) = walk.foldLeft((Vector.empty[Int], afterWalk)) {
          case ((found, current), value) =>
            val (hidden, next) = current.chosen(Vector(true, false))
            (found :+ (if hidden then 0 else value), next)
        }
        (
          ArrayDescription.Site(upper, SeededInput.Input.Written(entries)),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.arrayDescription

  def arguments(
      problems: CsesProblems,
      site: ArrayDescription.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(site.upper +: written)
        Vector(naturals(site.upper), CsesEncodings.list(written.map(naturals)))
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.upper), generator.argument(problems))

  /** A solution whose table lets an unknown entry take 0 and m + 1 as well
    * (`ArrayDescription.unboundedFillings`).
    */
  def wrongAnswers(
      site: ArrayDescription.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        ArrayDescription.unboundedFillings(site.upper, site.entries)
      )
    )

/** The sites, the unbounded count and the ladder of `ArrayDescription`. */
object ArrayDescription:

  /** The bound m and the entries of a site, 0 for an unknown entry. */
  final case class Site(upper: Int, input: SeededInput.Input[Vector[Int]]):

    /** The entries. */
    def entries: Vector[Int] = input.data

    override def toString: String =
      s"Site($upper,${input.described(_.toString)})"

  /** The fillings, modulo 10^9 + 7, when an unknown entry may take any value
    * from 0 to m + 1, by the table ways(position, value) = ways(position - 1,
    * value - 1) + ways(position - 1, value) + ways(position - 1, value + 1)
    * over those values, in O(n m) time.
    */
  def unboundedFillings(upper: Int, entries: Vector[Int]): BigInt =
    val values = 0 to upper + 1
    def allowed(entry: Int, value: Int): Boolean = entry == 0 || entry == value
    def at(table: Vector[Long], value: Int): Long =
      if value < 0 || value > upper + 1 then 0L else table(value)
    val first = values.toVector.map(value =>
      if allowed(entries.head, value) then 1L else 0L
    )
    val last = entries.tail.foldLeft(first) { (before, entry) =>
      values.toVector.map(value =>
        if !allowed(entry, value) then 0L
        else
          (at(before, value - 1) + at(before, value) + at(
            before,
            value + 1
          )) % CsesFamily.modulus
      )
    }
    BigInt(last.foldLeft(0L)(_ + _) % CsesFamily.modulus)

  /** The ladder: arrays of up to 4 entries, and up to 6, of m up to 3, so that
    * at most 6 entries are unknown, the most whose single program the reference
    * reading reads within its 50,000 tables at m = 3, 7 unknown entries passing
    * them (measured when the problem was written), and CSES's constraints, 1 ≤
    * n ≤ 10^5 and 1 ≤ m ≤ 100, drawn from their upper halves, at most four
    * sites. MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the
    * repeated programs at the bottom rung, the most tables were 3,873 (direct,
    * 8,906 steps) and 5,807 (respelled, 13,627 steps); of the single programs
    * at the middle rung, 7,352 (direct, 17,153 steps) and 18,453 (respelled,
    * 42,477 steps).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "entries_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("bound", 1 to 3),
          NominalParameter("entries", 1 to 4)
        )
      )
    ),
    CsesRung(
      "entries_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("bound", 1 to 3),
          NominalParameter("entries", 1 to 6)
        )
      )
    ),
    CsesRung(
      "entries_100000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("bound", 50 to 100),
          NominalParameter("entries", 50000 to 100000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[ArrayDescription]] =
    CsesFamily.families(rungs, ArrayDescription(_, _))

/** CSES 1666, Building Roads, `building_roads n roads`: the fewest new roads
  * that make every city reachable from every other (CSES also lists the roads;
  * the problem's file takes their count only). A site is n cities, n from the
  * parameter `cities`, and m roads, m from the parameter `roads`, each joining
  * any two cities, a city to itself included.
  */
final class BuildingRoads(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[BuildingRoads.Site](spelling, rung):

  val problem: String = "building_roads"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.BuildingRoadsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[BuildingRoads.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.buildingRoads(site.cities, site.roads))
    )

  protected def site(draws: Draws): (BuildingRoads.Site, Draws) =
    val (cities, afterCities) =
      CsesFamily.drawnParameter(draws, nominal, "cities")
    val (count, afterCount) =
      CsesFamily.drawnParameter(afterCities, nominal, "roads")
    rung.input match
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterCount, CsesFamily.seeds)
        (
          BuildingRoads.Site(
            cities,
            SeededInput.Input.Seeded(
              SeededInput.Connections(seed, count, cities)
            )
          ),
          after
        )
      case RungInput.Written =>
        val (roads, after) =
          CsesFamily.drawnValues(count, afterCount)(current =>
            val (first, afterFirst) = CsesFamily.between(current, 1 to cities)
            val (second, afterSecond) =
              CsesFamily.between(afterFirst, 1 to cities)
            ((first, second), afterSecond)
          )
        (BuildingRoads.Site(cities, SeededInput.Input.Written(roads)), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.buildingRoads

  def arguments(
      problems: CsesProblems,
      site: BuildingRoads.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(
          site.cities +: written.flatMap((first, second) =>
            Vector(first, second)
          )
        )
        Vector(
          naturals(site.cities),
          CsesEncodings.list(
            written.map((first, second) =>
              CsesEncodings.pair(naturals(first), naturals(second))
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.cities), generator.argument(problems))

  /** A solution that answers n - 1 - m, or 0 when the roads are as many as the
    * cities, as if no road were repeated or closed a cycle.
    */
  def wrongAnswers(
      site: BuildingRoads.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(math.max(0, site.cities - 1 - site.roads.size)))

/** The sites and the ladder of `BuildingRoads`. */
object BuildingRoads:

  /** The count of cities and the roads of a site, each `(first, second)`, the
    * cities from 1 to n.
    */
  final case class Site(
      cities: Int,
      input: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The roads. */
    def roads: Vector[(Int, Int)] = input.data

    override def toString: String =
      s"Site($cities,${input.described(_.toString)})"

  /** The ladder: graphs of up to 5 cities, and up to 10, the most whose single
    * program the reference reading reads within its 50,000 tables, 11 cities
    * passing them (measured when the problem was written), and CSES's
    * constraints, 1 ≤ n ≤ 10^5 and 1 ≤ m ≤ 2 · 10^5, drawn from their upper
    * halves, at most four sites. MEASURED 2026-11-22 by the probe of
    * `MoneySums.rungs`: of the repeated programs at the bottom rung, the most
    * tables were 5,612 (direct, 12,918 steps) and 12,113 (respelled, 29,125
    * steps); of the single programs at the middle rung, 40,192 (direct, 96,713
    * steps) and 52,421 (respelled, 127,677 steps; 1 of the 30 past 50,000).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "cities_5",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 5),
          NominalParameter("roads", 0 to 5)
        )
      )
    ),
    CsesRung(
      "cities_10",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 10),
          NominalParameter("roads", 0 to 12)
        )
      )
    ),
    CsesRung(
      "cities_100000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("cities", 50000 to 100000),
          NominalParameter("roads", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[BuildingRoads]] =
    CsesFamily.families(rungs, BuildingRoads(_, _))

/** CSES 1675, Road Reparation, `road_reparation n roads`: the least total cost
  * of roads that connect every city. A site is n cities, n from the parameter
  * `cities`, and m roads, m from the parameter `roads` and at least n - 1, each
  * cost from the parameter `cost`: the problem's premise, which its file's
  * program needs, is that the roads connect the cities (its program answers the
  * total cost of all roads for a graph they do not connect, no answer of CSES,
  * which answers IMPOSSIBLE). So n - 1 of the roads join each city to city 1 or
  * to a city joined before it, the cities taken in an order drawn, and the
  * others join any two cities, a city to itself included; each road's ends are
  * written in an order drawn, and the roads are then shuffled.
  */
final class RoadReparation(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[RoadReparation.Site](spelling, rung):

  val problem: String = "road_reparation"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.RoadReparationReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[RoadReparation.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.roadReparation(site.cities, site.roads))
    )

  protected def site(draws: Draws): (RoadReparation.Site, Draws) =
    val (cities, afterCities) =
      CsesFamily.drawnParameter(draws, nominal, "cities")
    val (wanted, afterWanted) =
      CsesFamily.drawnParameter(afterCities, nominal, "roads")
    val costs = Repetition.range(nominal, "cost")
    rung.input match
      case RungInput.Seeded =>
        val (treeSeed, afterTreeSeed) =
          CsesFamily.between(afterWanted, CsesFamily.seeds)
        val (roadSeed, after) =
          CsesFamily.between(afterTreeSeed, CsesFamily.seeds)
        val extra = math.max(wanted, cities - 1) - (cities - 1)
        (
          RoadReparation.Site(
            cities,
            SeededInput.Input.Seeded(
              SeededInput.Flights(
                treeSeed,
                roadSeed,
                cities,
                extra,
                costs.start,
                costs.end
              )
            )
          ),
          after
        )
      case RungInput.Written =>
        val (order, afterOrder) =
          CsesFamily.shuffled((2 to cities).toVector, afterWanted)
        val (spanning, afterSpanning) =
          order.zipWithIndex.foldLeft((Vector.empty[(Int, Int)], afterOrder)) {
            case ((found, current), (city, index)) =>
              val (earlier, afterEarlier) =
                CsesFamily.between(current, 0 to index)
              (
                found :+ ((
                  if earlier == 0 then 1 else order(earlier - 1),
                  city
                )),
                afterEarlier
              )
          }
        val (others, afterOthers) = CsesFamily.drawnValues(
          math.max(wanted, cities - 1) - (cities - 1),
          afterSpanning
        )(current =>
          val (first, afterFirst) = CsesFamily.between(current, 1 to cities)
          val (second, afterSecond) =
            CsesFamily.between(afterFirst, 1 to cities)
          ((first, second), afterSecond)
        )
        val (roads, afterRoads) = (spanning ++ others).foldLeft(
          (Vector.empty[(Int, Int, Long)], afterOthers)
        ) { case ((found, current), (first, second)) =>
          val (flipped, afterFlipped) = current.chosen(Vector(false, true))
          val (cost, afterCost) = CsesFamily.between(afterFlipped, costs)
          (
            found :+ (if flipped then (second, first, cost.toLong)
                      else (first, second, cost.toLong)),
            afterCost
          )
        }
        val (shuffled, after) = CsesFamily.shuffled(roads, afterRoads)
        (
          RoadReparation.Site(cities, SeededInput.Input.Written(shuffled)),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.roadReparation

  def arguments(
      problems: CsesProblems,
      site: RoadReparation.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(
          site.cities +: written.flatMap((first, second, cost) =>
            Vector(first, second, Math.toIntExact(cost))
          )
        )
        Vector(
          naturals(site.cities),
          CsesEncodings.list(
            written.map((first, second, cost) =>
              CsesEncodings.triple(
                naturals,
                first,
                second,
                Math.toIntExact(cost)
              )
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.cities), generator.argument(problems))

  /** A solution that sums the n - 1 cheapest roads, whether or not they connect
    * the cities, which differs where a cheap road closes a cycle.
    */
  def wrongAnswers(
      site: RoadReparation.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(site.roads.map(_._3).sorted.take(site.cities - 1).sum)
    )

/** The sites and the ladder of `RoadReparation`. */
object RoadReparation:

  /** The count of cities and the roads of a site, each `(first, second, cost)`,
    * the cities from 1 to n.
    */
  final case class Site(
      cities: Int,
      input: SeededInput.Input[Vector[(Int, Int, Long)]]
  ):

    /** The roads. */
    def roads: Vector[(Int, Int, Long)] = input.data

    override def toString: String =
      s"Site($cities,${input.described(_.toString)})"

  /** The ladder: up to 4 roads, and up to 6, the most whose single program the
    * reference reading reads within its 50,000 tables, a cycle of 6 cities
    * reading and 7 roads passing them (measured when the problem was written),
    * of small costs, and CSES's constraints, 1 ≤ n ≤ 10^5, 1 ≤ m ≤ 2 · 10^5 and
    * 1 ≤ c ≤ 10^9, the counts drawn from their upper halves, at most four
    * sites. MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the
    * repeated programs at the bottom rung, the most tables were 8,913 (direct,
    * 19,880 steps) and 16,638 (respelled, 39,027 steps); of the single programs
    * at the middle rung, 34,386 (direct, 78,355 steps) and 80,761 (respelled,
    * 182,632 steps; 1 of the 30 past 50,000).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "roads_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 4),
          NominalParameter("roads", 0 to 4),
          NominalParameter("cost", 1 to 3)
        )
      )
    ),
    CsesRung(
      "roads_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 6),
          NominalParameter("roads", 0 to 6),
          NominalParameter("cost", 1 to 4)
        )
      )
    ),
    CsesRung(
      "roads_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("cities", 50000 to 100000),
          NominalParameter("roads", 100000 to 200000),
          NominalParameter("cost", 1 to 1000000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[RoadReparation]] =
    CsesFamily.families(rungs, RoadReparation(_, _))

/** CSES 1681, Game Routes, `game_routes n flights`: the routes from level 1 to
  * level n over one-way flights, modulo 10^9 + 7, two routes different when
  * they use different flights. A site is n levels, n from the parameter
  * `levels`, and m flights, m from the parameter `flights`: the problem's
  * premise, which its file's program needs to end, is that the flights have no
  * cycle. So the levels are put in an order drawn, level 1 first and level n
  * last, and each flight goes from a level to a later one in that order, both
  * drawn, parallel flights included (a flight drawn again is a flight of its
  * own); a site of one level has no flight.
  */
final class GameRoutes(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[GameRoutes.Site](spelling, rung):

  val problem: String = "game_routes"

  val claim: String = "com.yang_bo.gezi.contest.corpora.reductions.GameRoutesReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[GameRoutes.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.gameRoutes(site.levels, site.flights))
    )

  protected def site(draws: Draws): (GameRoutes.Site, Draws) =
    val (levels, afterLevels) =
      CsesFamily.drawnParameter(draws, nominal, "levels")
    val (wanted, afterWanted) =
      CsesFamily.drawnParameter(afterLevels, nominal, "flights")
    rung.input match
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterWanted, CsesFamily.seeds)
        (
          GameRoutes.Site(
            levels,
            SeededInput.Input.Seeded(
              SeededInput.OrderedConnections(seed, wanted, levels)
            )
          ),
          after
        )
      case RungInput.Written =>
        val (middle, afterMiddle) =
          CsesFamily.shuffled((2 to levels - 1).toVector, afterWanted)
        val order = if levels == 1 then Vector(1) else (1 +: middle) :+ levels
        val (flights, after) = CsesFamily.drawnValues(
          if levels == 1 then 0 else wanted,
          afterMiddle
        )(current =>
          val (from, afterFrom) = CsesFamily.between(current, 0 to levels - 2)
          val (to, afterTo) =
            CsesFamily.between(afterFrom, from + 1 to levels - 1)
          ((order(from), order(to)), afterTo)
        )
        (GameRoutes.Site(levels, SeededInput.Input.Written(flights)), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.gameRoutes

  def arguments(
      problems: CsesProblems,
      site: GameRoutes.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(written) =>
        val naturals = CsesEncodings.naturals(
          site.levels +: written.flatMap((from, to) => Vector(from, to))
        )
        Vector(
          naturals(site.levels),
          CsesEncodings.list(
            written.map((from, to) =>
              CsesEncodings.pair(naturals(from), naturals(to))
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.levels), generator.argument(problems))

  /** A solution that counts parallel flights once, the routes over the distinct
    * flights.
    */
  def wrongAnswers(
      site: GameRoutes.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        CsesSolutions.gameRoutes(site.levels, site.flights.distinct)
      )
    )

/** The sites and the ladder of `GameRoutes`. */
object GameRoutes:

  /** The count of levels and the flights of a site, each `(from, to)`, the
    * levels from 1 to n.
    */
  final case class Site(
      levels: Int,
      input: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The flights. */
    def flights: Vector[(Int, Int)] = input.data

    override def toString: String =
      s"Site($levels,${input.described(_.toString)})"

  /** The ladder: up to 5 levels and 6 flights, and up to 15 levels and 20
    * flights, 15 levels the most read within the reference reading's 50,000
    * tables (measured when the problem was written), and CSES's constraints, 1
    * ≤ n ≤ 10^5 and 1 ≤ m ≤ 2 · 10^5, drawn from their upper halves, at most
    * four sites. MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the
    * repeated programs at the bottom rung, the most tables were 1,816 (direct,
    * 3,933 steps) and 2,975 (respelled, 6,754 steps); of the single programs at
    * the middle rung, 5,201 (direct, 12,111 steps) and 8,653 (respelled, 19,595
    * steps): the drawn flights make few routes. Parallel flights on a route are
    * rarer at the top rung, where one of the seeds 0 to 2 offers the trap.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "levels_5",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("levels", 1 to 5),
          NominalParameter("flights", 0 to 6)
        )
      )
    ),
    CsesRung(
      "levels_15",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("levels", 1 to 15),
          NominalParameter("flights", 0 to 20)
        )
      )
    ),
    CsesRung(
      "levels_100000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("levels", 50000 to 100000),
          NominalParameter("flights", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[GameRoutes]] =
    CsesFamily.families(rungs, GameRoutes(_, _))

/** CSES 1646, Static Range Sum Queries, `static_range_sums values queries`: for
  * each query (a, b), the sum of the values from place a to place b, both
  * included and counted from 1, the list of the sums. A site is n values, n
  * from the parameter `length`, each from the parameter `value`, and q queries,
  * q from the parameter `queries`, each a drawn from 1 to n and b from a to n,
  * so that 1 ≤ a ≤ b ≤ n, as the problem's premise asks.
  */
final class StaticRangeSums(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[StaticRangeSums.Site](spelling, rung):

  val problem: String = "static_range_sums"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.StaticRangeSumsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[StaticRangeSums.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.staticRangeSums(
          IArray.from(site.values.map(_.toLong)),
          site.queries
        )
      )
    )

  protected def site(draws: Draws): (StaticRangeSums.Site, Draws) =
    val (length, afterLength) =
      CsesFamily.drawnParameter(draws, nominal, "length")
    rung.input match
      case RungInput.Written =>
        val (values, afterValues) = CsesFamily.drawnValues(length, afterLength)(
          CsesFamily.drawnParameter(_, nominal, "value")
        )
        val (count, afterCount) =
          CsesFamily.drawnParameter(afterValues, nominal, "queries")
        val (queries, after) =
          CsesFamily.drawnValues(count, afterCount)(current =>
            val (first, afterFirst) = CsesFamily.between(current, 1 to length)
            val (last, afterLast) =
              CsesFamily.between(afterFirst, first to length)
            ((first, last), afterLast)
          )
        (
          StaticRangeSums.Site(
            SeededInput.Input.Written(values),
            SeededInput.Input.Written(queries)
          ),
          after
        )
      case RungInput.Seeded =>
        val (count, afterCount) =
          CsesFamily.drawnParameter(afterLength, nominal, "queries")
        val (valueSeed, afterValueSeed) =
          CsesFamily.between(afterCount, CsesFamily.seeds)
        val (querySeed, after) =
          CsesFamily.between(afterValueSeed, CsesFamily.seeds)
        val range = Repetition.range(nominal, "value")
        val values =
          SeededInput.Numbers(valueSeed, length, range.start, range.end)
        val queries = SeededInput.Ranges(querySeed, count, 1, length)
        (
          StaticRangeSums.Site(
            SeededInput.Input.Seeded(values),
            SeededInput.Input.Seeded(queries)
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.staticRangeSums

  def arguments(
      problems: CsesProblems,
      site: StaticRangeSums.Site
  ): Vector[ProblemTerm] =
    (site.valuesInput, site.queriesInput) match
      case (
            SeededInput.Input.Written(values),
            SeededInput.Input.Written(queries)
          ) =>
        val naturals = CsesEncodings.naturals(
          values ++ queries.flatMap((first, last) => Vector(first, last))
        )
        Vector(
          CsesEncodings.list(values.map(naturals)),
          CsesEncodings.list(
            queries.map((first, last) =>
              CsesEncodings.pair(naturals(first), naturals(last))
            )
          )
        )
      case (
            SeededInput.Input.Seeded(values),
            SeededInput.Input.Seeded(queries)
          ) =>
        Vector(values.argument(problems), queries.argument(problems))
      case _ =>
        throw IllegalStateException(
          s"a site's values and queries are both written or both seeded: $site"
        )

  /** A solution that answers prefix(b) - prefix(a) instead of prefix(b) -
    * prefix(a - 1), leaving out the value at place a, at every query, summed;
    * every value is at least 1, so it differs from the answer when a site has a
    * query.
    */
  def wrongAnswers(
      site: StaticRangeSums.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    val prefixes = site.values.scanLeft(BigInt(0))(_ + _)
    Vector(
      NativeValue.natural(
        site.queries.map((first, last) => prefixes(last) - prefixes(first)).sum
      )
    )

/** The sites and the ladder of `StaticRangeSums`. */
object StaticRangeSums:

  /** The values of a site and its queries, each `(a, b)` with 1 ≤ a ≤ b ≤ n.
    */
  final case class Site(
      valuesInput: SeededInput.Input[Vector[Int]],
      queriesInput: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The values. */
    def values: Vector[Int] = valuesInput.data

    /** The queries. */
    def queries: Vector[(Int, Int)] = queriesInput.data

    override def toString: String =
      s"Site(${valuesInput.described(_.toString)},${queriesInput.described(_.toString)})"

  /** The ladder: lists of up to 16 values, and up to 160, the most whose single
    * program with 3 queries the reference reading reads within its 50,000
    * tables, 240 passing them (measured when the problem was written), with up
    * to 3 queries, and CSES's constraints, 1 ≤ n, q ≤ 2 · 10^5 and 1 ≤ x ≤
    * 10^9, the counts drawn from their upper halves, at most four sites.
    * MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the repeated
    * programs at the bottom rung, the most tables were 5,430 (direct, 12,209
    * steps) and 8,234 (respelled, 19,180 steps); of the single programs at the
    * middle rung, 38,735 (direct, 87,921 steps) and 66,100 (respelled, 156,181
    * steps; 4 of the 30 past 50,000).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "length_16",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("length", 1 to 16),
          NominalParameter("value", 1 to 16),
          NominalParameter("queries", 1 to 3)
        )
      )
    ),
    CsesRung(
      "length_160",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("length", 1 to 160),
          NominalParameter("value", 1 to 1000),
          NominalParameter("queries", 1 to 3)
        )
      )
    ),
    CsesRung(
      "length_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("length", 100000 to 200000),
          NominalParameter("value", 1 to 1000000000),
          NominalParameter("queries", 100000 to 200000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[StaticRangeSums]] =
    CsesFamily.families(rungs, StaticRangeSums(_, _))

/** CSES 1618, Trailing Zeros, `trailing_zeros n`: the zeros that end n! written
  * in decimal. A site is n, drawn from the parameter `number`, at least 1 as
  * the problem's premise asks.
  */
final class TrailingZeros(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[TrailingZeros.Site](spelling, rung):

  val problem: String = "trailing_zeros"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.TrailingZerosReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[TrailingZeros.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.trailingZeros(site.number.toLong))
    )

  protected def site(draws: Draws): (TrailingZeros.Site, Draws) =
    val (number, after) = CsesFamily.drawnParameter(draws, nominal, "number")
    (TrailingZeros.Site(number), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.trailingZeros

  def arguments(
      problems: CsesProblems,
      site: TrailingZeros.Site
  ): Vector[ProblemTerm] = Vector(CsesEncodings.natural(site.number))

  /** A solution that counts the multiples of 5 alone, floor(n / 5), which
    * differs from n = 25 on.
    */
  def wrongAnswers(
      site: TrailingZeros.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(site.number / 5))

/** The sites and the ladder of `TrailingZeros`. */
object TrailingZeros:

  /** The number n of a site. */
  final case class Site(number: Int)

  /** The ladder: numbers up to 8, and up to 20, the most whose single program
    * the reference reading reads within its 50,000 tables, 25 passing them
    * (measured when the problem was written), and CSES's constraint, 1 ≤ n ≤
    * 10^9, the numbers drawn from its upper half, at most four sites. MEASURED
    * 2026-11-22 by the probe of `MoneySums.rungs`: of the repeated programs at
    * the bottom rung, the most tables were 5,792 (direct, 13,048 steps) and
    * 11,212 (respelled, 25,989 steps); of the single programs at the middle
    * rung, 40,645 (direct, 93,092 steps) and 82,266 (respelled, 194,596 steps;
    * 2 of the 30 past 50,000). The bottom rung was first numbers up to 12,
    * where the respelled programs of the seeds 0 to 59 read up to 34,992
    * tables, 11 of the 120 above 20,000. floor(n / 5) is first wrong at 25, so
    * no site below the top rung offers the trap: by the same probe none of the
    * seeds 0 to 399 at R = 1 of either lower rung does, and each of the seeds 0
    * to 2 of the top rung does.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "number_8",
      NominalRanges(
        Repetition.repetitionsWithin(8),
        Vector(NominalParameter("number", 1 to 8))
      )
    ),
    CsesRung(
      "number_20",
      NominalRanges(
        Repetition.repetitionsWithin(20),
        Vector(NominalParameter("number", 1 to 20))
      )
    ),
    CsesRung(
      "number_1000000000",
      NominalRanges(
        1 to 4,
        Vector(NominalParameter("number", 500000000 to 1000000000))
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[TrailingZeros]] =
    CsesFamily.families(rungs, TrailingZeros(_, _))

/** CSES 1082, Sum of Divisors, `sum_of_divisors n`: the sum over i from 1 to n
  * of the sum of the divisors of i, modulo 10^9 + 7. A site is n, at least 1 as
  * the problem's premise asks, drawn as two parts, its millions from the
  * parameter `millions` and the rest from the parameter `units`, n = millions ·
  * 10^6 + units, since CSES's n goes up to 10^12, past the `Int` ranges a
  * rung's parameters are.
  */
final class SumOfDivisors(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[SumOfDivisors.Site](spelling, rung):

  val problem: String = "sum_of_divisors"

  val claim: String =
    "com.yang_bo.gezi.contest.corpora.reductions.SumOfDivisorsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[SumOfDivisors.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.sumOfDivisors(site.number))
    )

  protected def site(draws: Draws): (SumOfDivisors.Site, Draws) =
    val (millions, afterMillions) =
      CsesFamily.drawnParameter(draws, nominal, "millions")
    val (units, after) =
      CsesFamily.drawnParameter(afterMillions, nominal, "units")
    (SumOfDivisors.Site(millions.toLong * SumOfDivisors.million + units), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.sumOfDivisors

  def arguments(
      problems: CsesProblems,
      site: SumOfDivisors.Site
  ): Vector[ProblemTerm] = Vector(CsesEncodings.natural(site.number))

  /** A solution off by one in its range, the sum over i from 1 to n - 1. */
  def wrongAnswers(
      site: SumOfDivisors.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(if site.number == 1 then BigInt(0)
    else CsesSolutions.sumOfDivisors(site.number - 1)))

/** The sites and the ladder of `SumOfDivisors`. */
object SumOfDivisors:

  /** The number n of a site. */
  final case class Site(number: Long)

  /** The unit of the parameter `millions`. */
  val million: Long = 1000000L

  /** The ladder: numbers up to 10, and up to 25, the most whose single program
    * the reference reading reads within its 50,000 tables, 30 passing them
    * (measured when the problem was written), and CSES's constraint, 1 ≤ n ≤
    * 10^12, the numbers drawn from 5 · 10^11 to 10^12 - 1, at most four sites.
    * MEASURED 2026-11-22 by the probe of `MoneySums.rungs`: of the repeated
    * programs at the bottom rung, the most tables were 9,164 (direct, 21,299
    * steps) and 21,797 (respelled, 52,622 steps; 4 of the 200 above 20,000); of
    * the single programs at the middle rung, 34,907 (direct, 82,519 steps) and
    * 64,636 (respelled, 153,839 steps; 5 of the 30 past 50,000). The bottom
    * rung was first numbers up to 16, where the respelled programs of the seeds
    * 0 to 59 read up to 46,776 tables, 47 of the 120 above 20,000.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "number_10",
      NominalRanges(
        Repetition.repetitionsWithin(10),
        Vector(
          NominalParameter("millions", 0 to 0),
          NominalParameter("units", 1 to 10)
        )
      )
    ),
    CsesRung(
      "number_25",
      NominalRanges(
        Repetition.repetitionsWithin(25),
        Vector(
          NominalParameter("millions", 0 to 0),
          NominalParameter("units", 1 to 25)
        )
      )
    ),
    CsesRung(
      "number_1000000000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("millions", 500000 to 999999),
          NominalParameter("units", 0 to 999999)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[SumOfDivisors]] =
    CsesFamily.families(rungs, SumOfDivisors(_, _))
