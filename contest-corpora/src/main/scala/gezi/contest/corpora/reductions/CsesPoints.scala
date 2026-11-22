package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

/** A row of a CSES point table: the point's name, the site its inputs
  * write, decoded to the family's site, and its Result.
  */
final case class CsesPoint[Site](point: String, site: Site, result: NativeValue)

/** The point table of a CSES problem, `problems/cses/<problem>/<problem>_point`,
  * read as the single-point family `contest_cses_<problem>`, or of a problem
  * built as a CSES family is, in the directory and under the corpus name its
  * family gives (`CsesFamily.directory`, `CsesFamily.corpus`). Each row is the constructor
  * `λ_p. _p Point Inputs… Result` of its fields (`ProblemFamily.rows`), read
  * by structure: the name is a text, a number the library's Scott integer, a
  * list the prelude's Scott list, a pair the prelude's pair and an option the
  * attractors' option, read by position (`ProblemData`), so the host reads no
  * string key. `row` decodes a row's fields to the family's site and the
  * Result, and throws for a row it does not match.
  *
  * A point's program is the family's direct single program of the site
  * (`CsesFamily.directProgram`), the problem's function applied to the site's
  * data as `CsesEncodings` writes it, and its reference is the row's Result
  * (`Reference.Computed`), which the test `claim` names checks against the
  * native solver and against tabling(weak_head)'s reading of the program,
  * `CsesPointsReferenceTest` for a CSES problem. The family is the
  * problem's bottom rung in the direct spelling: neither the program nor the
  * answer depends on the rung or on the spelling.
  */
final case class CsesPointTable[Site](
    family: CsesFamily[Site],
    row: PartialFunction[Vector[ProblemField], CsesPoint[Site]],
    claim: String = CsesPoints.claim
):

  /** The table's file, `<problem>_point`. */
  def table: String = s"${family.problem}_point"

  /** The corpus name the judge registers the table's points under. */
  def corpus: String = family.corpus

  /** The rows of the table, in the order of the file. */
  def rows(group: ReductionGroup): Vector[CsesPoint[Site]] =
    group.problems(family.directory).rows(table).map(fields =>
      row.applyOrElse(fields, other => throw IllegalArgumentException(s"not a row of $table: ${other.size} fields"))
    )

  /** The points of the table, each the direct single program of its site with
    * the row's Result as its reference.
    */
  def points(group: ReductionGroup): Vector[CorpusPoint] =
    rows(group).map(row =>
      CorpusPoint(
        row.point,
        DrawnPoint(family.directProgram(group, row.site), Reference.Computed(Vector(row.result.normalForm), claim))
      )
    )

/** The point tables of the CSES problems of `problems/cses`, the five of
  * the first batch and the ten of the second, with the decoders of their
  * fields.
  */
object CsesPoints:

  /** The test that checks the CSES tables' references. */
  val claim: String = "gezi.contest.corpora.reductions.CsesPointsReferenceTest"

  /** The natural a Result writes, the library's Scott integer. */
  private def natural(field: ProblemField): NativeValue = NativeValue.natural(ProblemData.integer(field))

  /** The option a Result writes, of corpora/library/attractors/option: none
    * `λn s. n` (the first alternative) or some k `λn s. s k` (the second),
    * k a natural.
    */
  private def optionalNatural(field: ProblemField): NativeValue = ProblemData.alternative(field, 2) match
    case (0, Vector())      => NativeValue.Optional(None)
    case (1, Vector(value)) => NativeValue.Optional(Some(natural(value)))
    case (position, fields) => throw IllegalArgumentException(s"no option: alternative $position with ${fields.size} fields")

  /** The pair of small integers a connection writes, of
    * corpora/library/prelude/pair, `λp. p l r`.
    */
  private def connection(field: ProblemField): (Int, Int) = ProblemData.alternative(field, 1) match
    case (0, Vector(from, to)) => (ProblemData.small(from), ProblemData.small(to))
    case (position, fields)    => throw IllegalArgumentException(s"no pair: alternative $position with ${fields.size} fields")

  /** The squares of a map's row, `.` floor (true) and `#` wall (false), as
    * CSES writes a map.
    */
  private def squares(row: String): Vector[Boolean] =
    row.toVector.map {
      case '.'   => true
      case '#'   => false
      case other => throw IllegalArgumentException(s"no square $other in the row $row")
    }

  /** `dice_combinations_point(Point, Sum, Result)`. */
  val diceCombinations: CsesPointTable[DiceCombinations.Site] =
    CsesPointTable(
      DiceCombinations(Spelling.Direct, DiceCombinations.rungs.head),
      { case Vector(point, sum, result) =>
        CsesPoint(ProblemData.text(point), DiceCombinations.Site(ProblemData.small(sum)), natural(result))
      }
    )

  /** `minimizing_coins_point(Point, Coins, Target, Result)`. */
  val minimizingCoins: CsesPointTable[MinimizingCoins.Site] =
    CsesPointTable(
      MinimizingCoins(Spelling.Direct, MinimizingCoins.rungs.head),
      { case Vector(point, coins, target, result) =>
        CsesPoint(ProblemData.text(point), MinimizingCoins.Site(ProblemData.smalls(coins), ProblemData.small(target)), optionalNatural(result))
      }
    )

  /** `message_route_point(Point, Computers, Connections, Result)`. */
  val messageRoute: CsesPointTable[MessageRoute.Site] =
    CsesPointTable(
      MessageRoute(Spelling.Direct, MessageRoute.rungs.head),
      { case Vector(point, computers, connections, result) =>
        CsesPoint(
          ProblemData.text(point),
          MessageRoute.Site(ProblemData.small(computers), ProblemData.list(connections).map(connection)),
          optionalNatural(result)
        )
      }
    )

  /** `counting_rooms_point(Point, Map, Result)`. */
  val countingRooms: CsesPointTable[CountingRooms.Site] =
    CsesPointTable(
      CountingRooms(Spelling.Direct, CountingRooms.rungs.head),
      { case Vector(point, map, result) =>
        CsesPoint(ProblemData.text(point), CountingRooms.Site(ProblemData.texts(map).map(squares)), natural(result))
      }
    )

  /** `exponentiation_point(Point, Base, Exponent, Result)`. */
  val exponentiation: CsesPointTable[Exponentiation.Site] =
    CsesPointTable(
      Exponentiation(Spelling.Direct, Exponentiation.rungs.head),
      { case Vector(point, base, exponent, result) =>
        CsesPoint(ProblemData.text(point), Exponentiation.Site(ProblemData.small(base), ProblemData.small(exponent)), natural(result))
      }
    )

  /** The five tables of the first batch. */
  val firstBatch: Vector[CsesPointTable[?]] = Vector(diceCombinations, minimizingCoins, messageRoute, countingRooms, exponentiation)

  // The second batch.

  /** The pair of small integers a pair of the prelude writes,
    * corpora/library/prelude/pair, `λp. p l r`.
    */
  private def smallPair(field: ProblemField): (Int, Int) = ProblemData.alternative(field, 1) match
    case (0, Vector(left, right)) => (ProblemData.small(left), ProblemData.small(right))
    case (position, fields)       => throw IllegalArgumentException(s"no pair: alternative $position with ${fields.size} fields")

  /** The triple `pair from (pair to cost)` of a flight or a road, the cost
    * a `Long`, as the native solvers take it (`CsesSolutions`).
    */
  private def triple(field: ProblemField): (Int, Int, Long) = ProblemData.alternative(field, 1) match
    case (0, Vector(from, rest)) =>
      val (to, cost) = smallPair(rest)
      (ProblemData.small(from), to, cost.toLong)
    case (position, fields) => throw IllegalArgumentException(s"no triple: alternative $position with ${fields.size} fields")

  /** A list of naturals a Result writes, each the library's Scott integer. */
  private def naturals(field: ProblemField): NativeValue = NativeValue.Elements(ProblemData.list(field).map(natural))

  /** `coin_combinations_ordered_point(Point, Coins, Sum, Result)`. */
  val coinCombinationsOrdered: CsesPointTable[CoinCombinations.Site] =
    CsesPointTable(
      CoinCombinationsOrdered(Spelling.Direct, CoinCombinationsOrdered.rungs.head),
      { case Vector(point, coins, sum, result) =>
        CsesPoint(ProblemData.text(point), CoinCombinations.Site(ProblemData.smalls(coins), ProblemData.small(sum)), natural(result))
      }
    )

  /** `coin_combinations_unordered_point(Point, Coins, Sum, Result)`. */
  val coinCombinationsUnordered: CsesPointTable[CoinCombinations.Site] =
    CsesPointTable(
      CoinCombinationsUnordered(Spelling.Direct, CoinCombinationsUnordered.rungs.head),
      { case Vector(point, coins, sum, result) =>
        CsesPoint(ProblemData.text(point), CoinCombinations.Site(ProblemData.smalls(coins), ProblemData.small(sum)), natural(result))
      }
    )

  /** `removing_digits_point(Point, Number, Result)`. */
  val removingDigits: CsesPointTable[RemovingDigits.Site] =
    CsesPointTable(
      RemovingDigits(Spelling.Direct, RemovingDigits.rungs.head),
      { case Vector(point, number, result) =>
        CsesPoint(ProblemData.text(point), RemovingDigits.Site(ProblemData.small(number)), natural(result))
      }
    )

  /** `grid_paths_point(Point, Grid, Result)`, each square a Scott boolean,
    * true for free.
    */
  val gridPaths: CsesPointTable[GridPaths.Site] =
    CsesPointTable(
      GridPaths(Spelling.Direct, GridPaths.rungs.head),
      { case Vector(point, grid, result) =>
        CsesPoint(
          ProblemData.text(point),
          GridPaths.Site(ProblemData.list(grid).map(row => ProblemData.list(row).map(ProblemData.truth))),
          natural(result)
        )
      }
    )

  /** `book_shop_point(Point, Books, Budget, Result)`, each book a pair of
    * its price and its pages.
    */
  val bookShop: CsesPointTable[BookShop.Site] =
    CsesPointTable(
      BookShop(Spelling.Direct, BookShop.rungs.head),
      { case Vector(point, books, budget, result) =>
        CsesPoint(ProblemData.text(point), BookShop.Site(ProblemData.list(books).map(smallPair), ProblemData.small(budget)), natural(result))
      }
    )

  /** `shortest_routes_single_source_point(Point, Cities, Flights, Result)`. */
  val shortestRoutesSingleSource: CsesPointTable[ShortestRoutesSingleSource.Site] =
    CsesPointTable(
      ShortestRoutesSingleSource(Spelling.Direct, ShortestRoutesSingleSource.rungs.head),
      { case Vector(point, cities, flights, result) =>
        CsesPoint(
          ProblemData.text(point),
          ShortestRoutesSingleSource.Site(ProblemData.small(cities), ProblemData.list(flights).map(triple)),
          naturals(result)
        )
      }
    )

  /** `shortest_routes_queries_point(Point, Cities, Roads, Queries, Result)`. */
  val shortestRoutesQueries: CsesPointTable[ShortestRoutesQueries.Site] =
    CsesPointTable(
      ShortestRoutesQueries(Spelling.Direct, ShortestRoutesQueries.rungs.head),
      { case Vector(point, cities, roads, queries, result) =>
        CsesPoint(
          ProblemData.text(point),
          ShortestRoutesQueries.Site(ProblemData.small(cities), ProblemData.list(roads).map(triple), ProblemData.list(queries).map(smallPair)),
          NativeValue.Elements(ProblemData.list(result).map(optionalNatural))
        )
      }
    )

  /** `counting_divisors_point(Point, Numbers, Result)`. */
  val countingDivisors: CsesPointTable[CountingDivisors.Site] =
    CsesPointTable(
      CountingDivisors(Spelling.Direct, CountingDivisors.rungs.head),
      { case Vector(point, numbers, result) =>
        CsesPoint(ProblemData.text(point), CountingDivisors.Site(ProblemData.smalls(numbers)), naturals(result))
      }
    )

  /** `binomial_coefficients_point(Point, Queries, Result)`, each query a pair
    * of a and b.
    */
  val binomialCoefficients: CsesPointTable[BinomialCoefficients.Site] =
    CsesPointTable(
      BinomialCoefficients(Spelling.Direct, BinomialCoefficients.rungs.head),
      { case Vector(point, queries, result) =>
        CsesPoint(ProblemData.text(point), BinomialCoefficients.Site(ProblemData.list(queries).map(smallPair)), naturals(result))
      }
    )

  /** `distinct_numbers_point(Point, Numbers, Result)`. */
  val distinctNumbers: CsesPointTable[DistinctNumbers.Site] =
    CsesPointTable(
      DistinctNumbers(Spelling.Direct, DistinctNumbers.rungs.head),
      { case Vector(point, numbers, result) =>
        CsesPoint(ProblemData.text(point), DistinctNumbers.Site(ProblemData.smalls(numbers)), natural(result))
      }
    )

  /** The ten tables of the second batch. */
  val secondBatch: Vector[CsesPointTable[?]] = Vector(
    coinCombinationsOrdered,
    coinCombinationsUnordered,
    removingDigits,
    gridPaths,
    bookShop,
    shortestRoutesSingleSource,
    shortestRoutesQueries,
    countingDivisors,
    binomialCoefficients,
    distinctNumbers
  )

  // The problems built as CSES families are, outside problems/cses.

  /** The graph a root writes, each node `λk. k seed successors` of
    * corpora/library/prelude/pair's shape, the seed an integer and the
    * successors a Scott list of nodes: the seed of each node and its
    * successors, numbered by the reverse of a depth-first post-order from the
    * root, so that the root is node 0 and every successor a later node. A
    * node reached along several paths, one term, is one node: fields are
    * equal when their instructions are (`ProblemField`).
    */
  private def weightedGraph(root: ProblemField): (Vector[Int], Vector[Vector[Int]]) =
    def node(field: ProblemField): (Int, Vector[ProblemField]) = ProblemData.alternative(field, 1) match
      case (0, Vector(seed, successors)) => (ProblemData.small(seed), ProblemData.list(successors))
      case (position, fields)            => throw IllegalArgumentException(s"no node: alternative $position with ${fields.size} fields")
    def visited(field: ProblemField, before: (Map[ProblemField, (Int, Vector[ProblemField])], Vector[ProblemField])): (
        Map[ProblemField, (Int, Vector[ProblemField])],
        Vector[ProblemField]
    ) =
      val (read, finished) = before
      if read.contains(field) then before
      else
        val decoded = node(field)
        val (afterSuccessors, finishedSuccessors) = decoded._2.foldLeft((read.updated(field, decoded), finished))((current, successor) =>
          visited(successor, current)
        )
        (afterSuccessors, finishedSuccessors :+ field)
    val (read, postOrder) = visited(root, (Map.empty, Vector.empty))
    val order = postOrder.reverse
    val index = order.zipWithIndex.toMap
    (order.map(read(_)._1), order.map(field => read(field)._2.map(index)))

  /** `weighted_paths_point(Point, Steps, Root, Result)` of
    * `problems/speculative_untabling` (`WeightedPaths`), read as the family
    * of `distinct`'s bottom rung.
    */
  val weightedPaths: CsesPointTable[WeightedPaths.Site] =
    CsesPointTable(
      WeightedPaths(Spelling.Direct, WeightedPaths.distinctRungs.head, WeightedPaths.Seeds.Distinct),
      { case Vector(point, steps, root, result) =>
        val (seeds, successors) = weightedGraph(root)
        CsesPoint(ProblemData.text(point), WeightedPaths.Site(ProblemData.small(steps), seeds, successors), natural(result))
      },
      "gezi.contest.corpora.reductions.WeightedPathsPointsReferenceTest"
    )

  /** The tables of the problems of `problems/speculative_untabling`. */
  val speculativeUntabling: Vector[CsesPointTable[?]] = Vector(weightedPaths)

  /** Every table of the CSES problems. */
  val all: Vector[CsesPointTable[?]] = firstBatch ++ secondBatch
