package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result

/** The answers of the CSES problems of the second batch by their
  * definitions, computed in the tests at the small sizes of the families'
  * bottom rungs and of the point tables, as `CsesDefinitions` computes the
  * first batch's: each follows the problem's statement as its file's header
  * words it, not the best known algorithm. The coin sequences and the coin
  * multisets are counted by their running sums, the step sequences of
  * removing digits, the paths of a grid and the subsets of the books and of
  * a set are enumerated, the least cost of a trip is the least over the
  * walks of at most n - 1 flights or roads, the divisors are counted by
  * trial of every number up to the value, and a distinct number is one no
  * earlier number equals.
  */
object CsesSecondBatchDefinitions:

  private val modulus: BigInt = BigInt(CsesFamily.modulus)

  /** The sequences of coins that sum to x, modulo 10^9 + 7. */
  def coinCombinationsOrdered(site: CoinCombinations.Site): NativeValue =
    def from(sum: Int): BigInt =
      if sum == site.target then 1 else site.coins.filter(sum + _ <= site.target).map(coin => from(sum + coin)).sum
    NativeValue.natural(from(0) % modulus)

  /** The multisets of coins that sum to x, modulo 10^9 + 7: the sequences
    * whose coins' positions in the list never decrease.
    */
  def coinCombinationsUnordered(site: CoinCombinations.Site): NativeValue =
    def from(position: Int, sum: Int): BigInt =
      if sum == site.target then 1
      else (position until site.coins.size).filter(next => sum + site.coins(next) <= site.target).map(next => from(next, sum + site.coins(next))).sum
    NativeValue.natural(from(0, 0) % modulus)

  /** The fewest steps that take n to 0, a step subtracting a nonzero
    * decimal digit, the least over every sequence of steps.
    */
  def removingDigits(site: RemovingDigits.Site): NativeValue =
    def fewest(number: Int): Int =
      if number == 0 then 0 else 1 + number.toString.map(_.asDigit).filter(_ != 0).distinct.map(digit => fewest(number - digit)).min
    NativeValue.natural(fewest(site.number))

  /** The paths right and down from the top left square to the bottom
    * right one over free squares, modulo 10^9 + 7.
    */
  def gridPaths(site: GridPaths.Site): NativeValue =
    val lastRow = site.rows.size - 1
    val lastColumn = site.rows.headOption.fold(0)(_.size) - 1
    def free(row: Int, column: Int): Boolean = row <= lastRow && column <= lastColumn && site.rows(row)(column)
    def from(row: Int, column: Int): BigInt =
      if !free(row, column) then 0
      else if row == lastRow && column == lastColumn then 1
      else from(row + 1, column) + from(row, column + 1)
    NativeValue.natural(from(0, 0) % modulus)

  /** The most pages of a subset of the books whose prices sum to at most x. */
  def bookShop(site: BookShop.Site): NativeValue =
    val subsets = site.books.foldLeft(Vector((0, 0)))((found, book) => found ++ found.map((price, pages) => (price + book._1, pages + book._2)))
    NativeValue.natural(subsets.filter(_._1 <= site.budget).map(_._2).max)

  /** The least cost of a walk of at most n - 1 of the edges from the
    * source to each city, none where no walk reaches it.
    */
  private def leastCosts(cities: Int, edges: Vector[(Int, Int, Long)], source: Int): Map[Int, Long] =
    val walks = Vector.iterate(Map(source -> 0L), cities)(shorter =>
      edges.foldLeft(shorter) { case (found, (from, to, cost)) =>
        shorter.get(from).fold(found)(before => found.updated(to, found.get(to).fold(before + cost)(_.min(before + cost))))
      }
    )
    walks.last

  /** The least cost of a trip from city 1 to each city, the total cost of
    * the flights plus one where none reaches it, as the problem's program
    * answers.
    */
  def shortestRoutesSingleSource(site: ShortestRoutesSingleSource.Site): NativeValue =
    val least = leastCosts(site.cities, site.flights, 1)
    val total = site.flights.map(_._3).sum
    NativeValue.Elements((1 to site.cities).toVector.map(city => NativeValue.natural(least.getOrElse(city, total + 1))))

  /** For each query, the least cost of a trip over the two-way roads, or
    * none.
    */
  def shortestRoutesQueries(site: ShortestRoutesQueries.Site): NativeValue =
    val edges = site.roads.flatMap((first, second, cost) => Vector((first, second, cost), (second, first, cost)))
    NativeValue.Elements(site.queries.map((source, destination) =>
      NativeValue.Optional(leastCosts(site.cities, edges, source).get(destination).map(NativeValue.natural(_)))
    ))

  /** The numbers from 1 to x that divide x, for each x. */
  def countingDivisors(site: CountingDivisors.Site): NativeValue =
    NativeValue.Elements(site.numbers.map(number => NativeValue.natural((1 to number).count(number % _ == 0))))

  /** The subsets of b of a elements, for each query, modulo 10^9 + 7:
    * those without the last element and those with it.
    */
  def binomialCoefficients(site: BinomialCoefficients.Site): NativeValue =
    def subsets(whole: Int, chosen: Int): BigInt =
      if chosen == 0 then 1 else if whole == 0 then 0 else subsets(whole - 1, chosen) + subsets(whole - 1, chosen - 1)
    NativeValue.Elements(site.queries.map((whole, chosen) => NativeValue.natural(subsets(whole, chosen) % modulus)))

  /** The numbers that equal no number before them. */
  def distinctNumbers(site: DistinctNumbers.Site): NativeValue =
    NativeValue.natural(site.numbers.indices.count(index => !site.numbers.take(index).contains(site.numbers(index))))

class CoinCombinationsOrderedReferenceTest
    extends CsesFamilySuite(
      CoinCombinationsOrdered(Spelling.Direct, CoinCombinationsOrdered.rungs.head),
      CoinCombinationsOrdered(Spelling.Respelled, CoinCombinationsOrdered.rungs.head),
      CsesSecondBatchDefinitions.coinCombinationsOrdered,
      "cses_coin_combinations_ordered"
    )

class CoinCombinationsUnorderedReferenceTest
    extends CsesFamilySuite(
      CoinCombinationsUnordered(Spelling.Direct, CoinCombinationsUnordered.rungs.head),
      CoinCombinationsUnordered(Spelling.Respelled, CoinCombinationsUnordered.rungs.head),
      CsesSecondBatchDefinitions.coinCombinationsUnordered,
      "cses_coin_combinations_unordered"
    )

class RemovingDigitsReferenceTest
    extends CsesFamilySuite(
      RemovingDigits(Spelling.Direct, RemovingDigits.rungs.head),
      RemovingDigits(Spelling.Respelled, RemovingDigits.rungs.head),
      CsesSecondBatchDefinitions.removingDigits,
      "cses_removing_digits"
    )

class GridPathsReferenceTest
    extends CsesFamilySuite(
      GridPaths(Spelling.Direct, GridPaths.rungs.head),
      GridPaths(Spelling.Respelled, GridPaths.rungs.head),
      CsesSecondBatchDefinitions.gridPaths,
      "cses_grid_paths"
    ):

  private def answerOf(site: GridPaths.Site): NativeValue = NativeValue.natural(CsesSolutions.gridPaths(site.rows))

  private def blockedEndpoint(site: GridPaths.Site): Boolean = !site.rows.head.head || !site.rows.last.last

  /** Purpose: catch a draw or a wrong table that offers no trap for a
    * blocked start or end square, or offers one where the wrong table is
    * right. On generated seeds, at the two small rungs, a
    * grid with a trap at its start or end square has the answer 0, and a
    * grid with neither is answered by the wrong table as by the definition.
    */
  property("the wrong table differs from the answer only at a blocked start or end square", _.copy(testLimit = 200)) {
    for
      seed <- Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1)).forAll
      rung <- Gen.element1(GridPaths.rungs.head, GridPaths.rungs(1)).forAll
    yield
      val family = GridPaths(Spelling.Direct, rung)
      val sites = family.drawnAt(ReductionTesting.group, seed, 1).sites
      Result.all(sites.toList.map(site =>
        val answer = answerOf(site)
        val wrong = family.wrongAnswers(site, answer)
        if blockedEndpoint(site) then Result.diff(answer, NativeValue.natural(0))(_ == _)
        else Result.diff(wrong, Vector(answer))(_ == _)
      )).log(site(seed, rung))
  }

  private def site(seed: Long, rung: CsesRung): String = s"seed $seed, ${rung.name}"

  /** Purpose: catch a share of blocked start or end squares that is lost,
    * so that no trap is ever offered. Over the seeds 0 to 399 at each small
    * rung, and the seeds 0 to 29 at the top rung, whose grids are large, the
    * grids with a blocked start or end square are at least one in four (at
    * the top rung one in ten) and some seed offers a trap candidate.
    */
  test("a fixed share of the grids has a blocked start or end square") {
    GridPaths.rungs.zip(Vector(400L, 400L, 30L)).foreach { (rung, seeds) =>
      val family = GridPaths(Spelling.Direct, rung)
      val drawn = (0L until seeds).map(seed => family.drawnAt(ReductionTesting.group, seed, 1))
      val sites = drawn.flatMap(_.sites)
      val blocked = sites.count(blockedEndpoint)
      val denominator = if rung == GridPaths.rungs.last then 10 else 4
      assert(blocked * denominator >= sites.size, s"${rung.name}: $blocked of ${sites.size} grids have a blocked start or end square")
      assert(
        drawn.exists(single => family.trapCandidates(single, single.sites.map(answerOf)).nonEmpty),
        s"${rung.name}: no seed offers a trap"
      )
    }
  }

class BookShopReferenceTest
    extends CsesFamilySuite(
      BookShop(Spelling.Direct, BookShop.rungs.head),
      BookShop(Spelling.Respelled, BookShop.rungs.head),
      CsesSecondBatchDefinitions.bookShop,
      "cses_book_shop"
    )

class ShortestRoutesSingleSourceReferenceTest
    extends CsesFamilySuite(
      ShortestRoutesSingleSource(Spelling.Direct, ShortestRoutesSingleSource.rungs.head),
      ShortestRoutesSingleSource(Spelling.Respelled, ShortestRoutesSingleSource.rungs.head),
      CsesSecondBatchDefinitions.shortestRoutesSingleSource,
      "cses_shortest_routes_single_source"
    )

class ShortestRoutesQueriesReferenceTest
    extends CsesFamilySuite(
      ShortestRoutesQueries(Spelling.Direct, ShortestRoutesQueries.rungs.head),
      ShortestRoutesQueries(Spelling.Respelled, ShortestRoutesQueries.rungs.head),
      CsesSecondBatchDefinitions.shortestRoutesQueries,
      "cses_shortest_routes_queries"
    )

class CountingDivisorsReferenceTest
    extends CsesFamilySuite(
      CountingDivisors(Spelling.Direct, CountingDivisors.rungs.head),
      CountingDivisors(Spelling.Respelled, CountingDivisors.rungs.head),
      CsesSecondBatchDefinitions.countingDivisors,
      "cses_counting_divisors"
    )

class BinomialCoefficientsReferenceTest
    extends CsesFamilySuite(
      BinomialCoefficients(Spelling.Direct, BinomialCoefficients.rungs.head),
      BinomialCoefficients(Spelling.Respelled, BinomialCoefficients.rungs.head),
      CsesSecondBatchDefinitions.binomialCoefficients,
      "cses_binomial_coefficients"
    )

class DistinctNumbersReferenceTest
    extends CsesFamilySuite(
      DistinctNumbers(Spelling.Direct, DistinctNumbers.rungs.head),
      DistinctNumbers(Spelling.Respelled, DistinctNumbers.rungs.head),
      CsesSecondBatchDefinitions.distinctNumbers,
      "cses_distinct_numbers"
    )
