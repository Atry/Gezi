package com.yang_bo.gezi.contest.corpora.reductions

/** The answers of the CSES problems of the third batch by their definitions,
  * computed in the tests at the small sizes of the families' bottom rungs and
  * of the point tables, as `CsesDefinitions` computes the first batch's: each
  * follows the problem's statement as its file's header words it, not the best
  * known algorithm. The subsets of the coins, of the roads and the subsequences
  * of a list are enumerated, the fewest cuts are the least over every first cut
  * by recursion, the fillings of an array are enumerated, the components of a
  * graph are the cities that no smaller city reaches, the routes are enumerated
  * by the flights out of each level, a range sum adds the values of its places,
  * n! is multiplied out and its decimal zeros counted, and the divisors of each
  * i are found by trial.
  */
object CsesThirdBatchDefinitions:

  private val modulus: BigInt = BigInt(CsesFamily.modulus)

  /** The sums of the nonempty subsets of the coins, each once, summed. */
  def moneySums(site: MoneySums.Site): NativeValue =
    val subsets = site.coins.foldLeft(Vector(Vector.empty[Int]))(
      (found, coin) => found ++ found.map(_ :+ coin)
    )
    NativeValue.natural(
      subsets.filter(_.nonEmpty).map(_.sum).distinct.map(BigInt(_)).sum
    )

  /** The fewest cuts: none for a square, otherwise one more than the least,
    * over every first cut across either side, of the cuts of the two pieces.
    */
  def rectangleCutting(site: RectangleCutting.Site): NativeValue =
    def cuts(first: Int, second: Int): Int =
      if first == second then 0
      else
        1 + ((1 until first).map(cut =>
          cuts(cut, second) + cuts(first - cut, second)
        ) ++
          (1 until second).map(cut =>
            cuts(first, cut) + cuts(first, second - cut)
          )).min
    NativeValue.natural(cuts(site.first, site.second))

  /** The greatest length of a subsequence whose numbers strictly increase. */
  def increasingSubsequence(site: IncreasingSubsequence.Site): NativeValue =
    val subsequences = site.numbers.foldLeft(Vector(Vector.empty[Int]))(
      (found, number) => found ++ found.map(_ :+ number)
    )
    NativeValue.natural(
      subsequences
        .filter(subsequence =>
          subsequence.zip(subsequence.drop(1)).forall(_ < _)
        )
        .map(_.size)
        .max
    )

  /** The fillings of the unknown entries with values from 1 to m whose
    * neighbours differ by at most 1, modulo 10^9 + 7.
    */
  def arrayDescription(site: ArrayDescription.Site): NativeValue =
    val fillings =
      site.entries.foldLeft(Vector(Vector.empty[Int]))((found, entry) =>
        found.flatMap(filling =>
          (if entry == 0 then (1 to site.upper).toVector else Vector(entry))
            .map(filling :+ _)
        )
      )
    val smooth = fillings.count(filling =>
      filling
        .zip(filling.drop(1))
        .forall((left, right) => math.abs(left - right) <= 1)
    )
    NativeValue.natural(BigInt(smooth) % modulus)

  /** The cities that the roads reach from a city, the city included. */
  private def reached(roads: Vector[(Int, Int)], from: Int): Set[Int] =
    @scala.annotation.tailrec
    def grown(found: Set[Int]): Set[Int] =
      val next = found ++ roads.flatMap((first, second) =>
        (if found.contains(first) then Vector(second)
         else
           Vector.empty
        ) ++ (if found.contains(second) then Vector(first) else Vector.empty)
      )
      if next == found then found else grown(next)
    grown(Set(from))

  /** The components, each counted at its smallest city, less one. */
  def buildingRoads(site: BuildingRoads.Site): NativeValue =
    val firsts = (1 to site.cities).count(city =>
      !(1 until city).exists(smaller =>
        reached(site.roads, smaller).contains(city)
      )
    )
    NativeValue.natural(firsts - 1)

  /** The least total cost of a subset of the roads that connects every city.
    */
  def roadReparation(site: RoadReparation.Site): NativeValue =
    val subsets = site.roads.foldLeft(Vector(Vector.empty[(Int, Int, Long)]))(
      (found, road) => found ++ found.map(_ :+ road)
    )
    val connecting = subsets.filter(subset =>
      reached(
        subset.map((first, second, _) => (first, second)),
        1
      ).size == site.cities
    )
    NativeValue.natural(connecting.map(_.map(_._3).sum).min)

  /** The routes from level 1 to level n, each the empty route at n and
    * otherwise a flight out of the level followed by a route from its end,
    * modulo 10^9 + 7.
    */
  def gameRoutes(site: GameRoutes.Site): NativeValue =
    def routes(level: Int): BigInt =
      if level == site.levels then 1
      else site.flights.filter(_._1 == level).map((_, to) => routes(to)).sum
    NativeValue.natural(routes(1) % modulus)

  /** The sum of the values at the places from a to b, summed over the queries.
    */
  def staticRangeSums(site: StaticRangeSums.Site): NativeValue =
    NativeValue.natural(
      site.queries
        .map((first, last) =>
          site.values.slice(first - 1, last).map(BigInt(_)).sum
        )
        .sum
    )

  /** The zeros that end the decimal digits of 1 · 2 · … · n. */
  def trailingZeros(site: TrailingZeros.Site): NativeValue =
    val factorial = (1 to site.number).foldLeft(BigInt(1))(_ * _)
    NativeValue.natural(factorial.toString.reverse.takeWhile(_ == '0').length)

  /** The sum over i from 1 to n of the numbers from 1 to i that divide i,
    * modulo 10^9 + 7.
    */
  def sumOfDivisors(site: SumOfDivisors.Site): NativeValue =
    val limit = Math.toIntExact(site.number)
    NativeValue.natural(
      (1 to limit)
        .map(number => BigInt((1 to number).filter(number % _ == 0).sum))
        .sum % modulus
    )

class MoneySumsReferenceTest
    extends CsesFamilySuite(
      MoneySums(Spelling.Direct, MoneySums.rungs.head),
      MoneySums(Spelling.Respelled, MoneySums.rungs.head),
      CsesThirdBatchDefinitions.moneySums,
      "cses_money_sums"
    )

class RectangleCuttingReferenceTest
    extends CsesFamilySuite(
      RectangleCutting(Spelling.Direct, RectangleCutting.rungs.head),
      RectangleCutting(Spelling.Respelled, RectangleCutting.rungs.head),
      CsesThirdBatchDefinitions.rectangleCutting,
      "cses_rectangle_cutting"
    )

class IncreasingSubsequenceReferenceTest
    extends CsesFamilySuite(
      IncreasingSubsequence(Spelling.Direct, IncreasingSubsequence.rungs.head),
      IncreasingSubsequence(
        Spelling.Respelled,
        IncreasingSubsequence.rungs.head
      ),
      CsesThirdBatchDefinitions.increasingSubsequence,
      "cses_increasing_subsequence"
    )

class ArrayDescriptionReferenceTest
    extends CsesFamilySuite(
      ArrayDescription(Spelling.Direct, ArrayDescription.rungs.head),
      ArrayDescription(Spelling.Respelled, ArrayDescription.rungs.head),
      CsesThirdBatchDefinitions.arrayDescription,
      "cses_array_description"
    )

class BuildingRoadsReferenceTest
    extends CsesFamilySuite(
      BuildingRoads(Spelling.Direct, BuildingRoads.rungs.head),
      BuildingRoads(Spelling.Respelled, BuildingRoads.rungs.head),
      CsesThirdBatchDefinitions.buildingRoads,
      "cses_building_roads"
    )

class RoadReparationReferenceTest
    extends CsesFamilySuite(
      RoadReparation(Spelling.Direct, RoadReparation.rungs.head),
      RoadReparation(Spelling.Respelled, RoadReparation.rungs.head),
      CsesThirdBatchDefinitions.roadReparation,
      "cses_road_reparation"
    )

class GameRoutesReferenceTest
    extends CsesFamilySuite(
      GameRoutes(Spelling.Direct, GameRoutes.rungs.head),
      GameRoutes(Spelling.Respelled, GameRoutes.rungs.head),
      CsesThirdBatchDefinitions.gameRoutes,
      "cses_game_routes"
    )

class StaticRangeSumsReferenceTest
    extends CsesFamilySuite(
      StaticRangeSums(Spelling.Direct, StaticRangeSums.rungs.head),
      StaticRangeSums(Spelling.Respelled, StaticRangeSums.rungs.head),
      CsesThirdBatchDefinitions.staticRangeSums,
      "cses_static_range_sums"
    )

class TrailingZerosReferenceTest
    extends CsesFamilySuite(
      TrailingZeros(Spelling.Direct, TrailingZeros.rungs.head),
      TrailingZeros(Spelling.Respelled, TrailingZeros.rungs.head),
      CsesThirdBatchDefinitions.trailingZeros,
      "cses_trailing_zeros"
    )

class SumOfDivisorsReferenceTest
    extends CsesFamilySuite(
      SumOfDivisors(Spelling.Direct, SumOfDivisors.rungs.head),
      SumOfDivisors(Spelling.Respelled, SumOfDivisors.rungs.head),
      CsesThirdBatchDefinitions.sumOfDivisors,
      "cses_sum_of_divisors"
    )
