package gezi.contest.corpora.reductions

import gezi.ir.{Configured, NoFacts}
import gezi.frontend.Term

// The CSES families of the second batch, built as the first batch's are (`CsesFamily`, `CsesFamilies.scala`), each
// rung in both spellings.

/** CSES 1635, Coin Combinations I, `coin_combinations_ordered coins x`: the
  * ordered sequences of coins, each value usable any number of times, that sum
  * to x, modulo 10^9 + 7. A site is k distinct coin values drawn from the
  * parameter `value`, k from the parameter `coins`, in the order drawn, and x
  * from the parameter `target`.
  */
final class CoinCombinationsOrdered(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[CoinCombinations.Site](spelling, rung):

  val problem: String = "coin_combinations_ordered"

  val claim: String =
    "gezi.contest.corpora.reductions.CoinCombinationsOrderedReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[CoinCombinations.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.coinCombinationsOrdered(site.coins, site.target)
      )
    )

  protected def site(draws: Draws): (CoinCombinations.Site, Draws) =
    CoinCombinations.site(draws, nominal)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.coinCombinationsOrdered

  def arguments(
      problems: CsesProblems,
      site: CoinCombinations.Site
  ): Vector[ProblemTerm] = CoinCombinations.arguments(site)

  /** A solution that counts the multisets of coins instead of their sequences,
    * the answer of Coin Combinations II.
    */
  def wrongAnswers(
      site: CoinCombinations.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        CsesSolutions.coinCombinationsUnordered(site.coins, site.target)
      )
    )

/** The ladder of `CoinCombinationsOrdered`. */
object CoinCombinationsOrdered:

  /** The ladder: few small coins and small targets read by the reference
    * reading, and CSES's constraints, 1 ≤ n ≤ 100 coins, 1 ≤ x ≤ 10^6 and 1 ≤ c
    * ≤ 10^6, the counts and the targets drawn from their upper halves, at most
    * four sites, each as large as a CSES input. MEASURED 2026-11-21 on
    * 236b88682 by a scratch probe in contest-corpora's tests (CPUs 0 to 3 of
    * contest.slice, nice 10, the 1-minute load about 9), tabling(weak_head)
    * knowing top (`ReadingState.knowingTop`) within 20,000,000 steps and
    * 200,000 tables, each reading one normal form: the single program of the
    * coins (1, 2, 3) (the function as its file exports it, applied to the
    * site's data) took, for x from 1 to 9, 1,907, 2,685, 3,876, 6,194, 10,154,
    * 18,282, 31,849, 59,879 and 107,559 steps and 933, 1,277, 1,786, 2,780,
    * 4,481, 7,937, 13,719, 25,630 and 45,886 tables, about 1.8 times more a
    * unit of x (the sequences are built and counted), and of (1, 2, 4) at 8
    * 47,489 and 20,434; the repeated program of the seed 20261031 at target_5
    * and R = 2 took 5,059 steps and 2,311 tables (respelled 7,006 and 3,116)
    * and at R = 24 27,066 and 11,256 (respelled 44,159 and 18,097), at target_8
    * and R = 4 4,464 and 2,058 (respelled 8,139 and 3,466) and at R = 64
    * 239,184 and 98,042 (respelled 456,903 and 186,215), past the reference
    * reading's 50,000 tables at that R, which the points do not need
    * (`NativelySolved`).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "target_5",
      NominalRanges(
        Repetition.repetitionsWithin(24),
        Vector(
          NominalParameter("coins", 1 to 3),
          NominalParameter("value", 1 to 3),
          NominalParameter("target", 1 to 5)
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
    CoinCombinations.atConstraint
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[CoinCombinationsOrdered]] =
    CsesFamily.families(rungs, CoinCombinationsOrdered(_, _))

/** CSES 1636, Coin Combinations II, `coin_combinations_unordered coins x`: the
  * multisets of coins, each value usable any number of times, that sum to x,
  * modulo 10^9 + 7, the coins counted by their positions in the list. A site is
  * drawn as `CoinCombinationsOrdered` draws one, the coin values distinct, as
  * CSES's are and as the problem's file asks.
  */
final class CoinCombinationsUnordered(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[CoinCombinations.Site](spelling, rung):

  val problem: String = "coin_combinations_unordered"

  val claim: String =
    "gezi.contest.corpora.reductions.CoinCombinationsUnorderedReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[CoinCombinations.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.coinCombinationsUnordered(site.coins, site.target)
      )
    )

  protected def site(draws: Draws): (CoinCombinations.Site, Draws) =
    CoinCombinations.site(draws, nominal)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.coinCombinationsUnordered

  def arguments(
      problems: CsesProblems,
      site: CoinCombinations.Site
  ): Vector[ProblemTerm] = CoinCombinations.arguments(site)

  /** A solution that counts the sequences of coins instead of their multisets,
    * the answer of Coin Combinations I.
    */
  def wrongAnswers(
      site: CoinCombinations.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(
      NativeValue.natural(
        CsesSolutions.coinCombinationsOrdered(site.coins, site.target)
      )
    )

/** The ladder of `CoinCombinationsUnordered`. */
object CoinCombinationsUnordered:

  /** The ladder: few small coins and small targets read by the reference
    * reading, and CSES's constraints, as `CoinCombinationsOrdered`'s. MEASURED
    * 2026-11-21 by the probe of `CoinCombinationsOrdered.rungs`: the single
    * program of the coins (1, 2, 3) took, for x of 5, 10, 13, 16 and 19, 6,187,
    * 20,721, 35,469, 58,408 and 86,564 steps and 2,808, 9,100, 15,500, 25,408
    * and 37,628 tables, of (1, 2, 4) at 16 52,327 and 22,749, and of (4, 2, 1)
    * at 16 43,075 and 18,725; the repeated program of the seed 20261031 at
    * target_10 and R = 2 took 2,890 steps and 1,370 tables (respelled 4,049 and
    * 1,844) and at R = 24 31,144 and 13,217 (respelled 55,656 and 22,805), at
    * target_16 and R = 4 20,603 and 9,004 (respelled 33,860 and 14,330) and at
    * R = 64 231,021 and 97,065 (respelled 361,082 and 147,926), past the
    * reference reading's 50,000 tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "target_10",
      NominalRanges(
        Repetition.repetitionsWithin(24),
        Vector(
          NominalParameter("coins", 1 to 3),
          NominalParameter("value", 1 to 4),
          NominalParameter("target", 1 to 10)
        )
      )
    ),
    CsesRung(
      "target_16",
      NominalRanges(
        Repetition.repetitionsWithin(64),
        Vector(
          NominalParameter("coins", 1 to 3),
          NominalParameter("value", 1 to 4),
          NominalParameter("target", 1 to 16)
        )
      )
    ),
    CoinCombinations.atConstraint
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[CoinCombinationsUnordered]] =
    CsesFamily.families(rungs, CoinCombinationsUnordered(_, _))

/** The sites, the drawing and the top rung of the two coin combination
  * families, whose inputs are one shape.
  */
object CoinCombinations:

  /** The coin values and the target x of a site. */
  final case class Site(coins: Vector[Int], target: Int)

  /** k distinct coin values drawn from 1 to the parameter `value`'s end, k from
    * the parameter `coins`, in the order drawn, and x from the parameter
    * `target`, as `MinimizingCoins` draws a site.
    */
  def site(draws: Draws, nominal: NominalRanges): (Site, Draws) =
    val (count, afterCount) = CsesFamily.drawnParameter(draws, nominal, "coins")
    val values = Repetition.range(nominal, "value")
    val (coins, afterCoins) = afterCount.distinct(math.min(count, values.size))(
      CsesFamily.between(_, values)
    )
    val (target, afterTarget) =
      CsesFamily.drawnParameter(afterCoins, nominal, "target")
    (Site(coins, target), afterTarget)

  /** The coins, a list of naturals, and the target, a natural. */
  def arguments(site: Site): Vector[ProblemTerm] =
    Vector(
      CsesEncodings.list(site.coins.map(coin => CsesEncodings.natural(coin))),
      CsesEncodings.natural(site.target)
    )

  /** CSES's constraints, 1 ≤ n ≤ 100, 1 ≤ x ≤ 10^6 and 1 ≤ c ≤ 10^6, the counts
    * and the targets drawn from their upper halves, at most four sites.
    */
  val atConstraint: CsesRung = CsesRung(
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

/** CSES 1637, Removing Digits, `removing_digits n`: the fewest steps that take
  * n to 0, a step subtracting a nonzero decimal digit of the number. A site is
  * n, drawn from the parameter `number`.
  */
final class RemovingDigits(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[RemovingDigits.Site](spelling, rung):

  val problem: String = "removing_digits"

  val claim: String =
    "gezi.contest.corpora.reductions.RemovingDigitsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[RemovingDigits.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.removingDigits(site.number))
    )

  protected def site(draws: Draws): (RemovingDigits.Site, Draws) =
    val (number, after) = CsesFamily.drawnParameter(draws, nominal, "number")
    (RemovingDigits.Site(number), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.removingDigits

  def arguments(
      problems: CsesProblems,
      site: RemovingDigits.Site
  ): Vector[ProblemTerm] = Vector(CsesEncodings.natural(site.number))

  /** No wrong solution's answer differs here. The one proposed, the greedy
    * solution that always subtracts the largest digit, was to be a candidate
    * only where it takes more steps than the fewest, and it never does within
    * CSES's constraint: MEASURED 2026-11-21 by a scratch Python script, the
    * greedy count and the recurrence of `CsesSolutions.removingDigits` agree at
    * every n from 0 to 10^6.
    */
  def wrongAnswers(
      site: RemovingDigits.Site,
      answer: NativeValue
  ): Vector[NativeValue] = Vector.empty

/** The sites and the ladder of `RemovingDigits`. */
object RemovingDigits:

  /** The number n of a site. */
  final case class Site(number: Int)

  /** The ladder: numbers up to 15 and up to 30, read by the reference reading,
    * and CSES's constraint, 1 ≤ n ≤ 10^6, the numbers drawn from its upper
    * half, at most four sites. MEASURED 2026-11-21 by the probe of
    * `CoinCombinationsOrdered.rungs`: the single program of n took, for n of 9,
    * 10, 15, 19, 20, 25, 29 and 30, 2,353, 3,435, 12,780, 21,726, 20,784,
    * 71,440, 105,680 and 90,844 steps and 1,145, 1,622, 5,692, 9,564, 9,161,
    * 30,944, 45,615 and 39,227 tables (every sequence of steps is counted); the
    * repeated program of the seed 20261031 at number_15 and R = 2 took 2,971
    * steps and 1,413 tables (respelled 5,223 and 2,317) and at R = 15 34,055
    * and 14,766 (respelled 57,770 and 24,099), at number_30 and R = 4 141,678
    * and 61,114 (respelled 256,382 and 107,356), and at R = 30 both twins
    * stopped at the probe's 200,000 tables, past the reference reading's
    * 50,000, which the points do not need (`NativelySolved`).
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "number_15",
      NominalRanges(
        Repetition.repetitionsWithin(15),
        Vector(NominalParameter("number", 1 to 15))
      )
    ),
    CsesRung(
      "number_30",
      NominalRanges(
        Repetition.repetitionsWithin(30),
        Vector(NominalParameter("number", 1 to 30))
      )
    ),
    CsesRung(
      "number_1000000",
      NominalRanges(
        1 to 4,
        Vector(NominalParameter("number", 500000 to 1000000))
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[RemovingDigits]] =
    CsesFamily.families(rungs, RemovingDigits(_, _))

/** CSES 1638, Grid Paths I, `grid_paths rows`: the paths from the top left
  * square to the bottom right one by steps right and down over free squares
  * (true), never entering a trap (false), modulo 10^9 + 7. A site is a square
  * grid of side n, drawn from the parameter `side`, each square a trap with
  * odds 1 in k, k drawn for the site from the parameter `trap_odds`.
  *
  * A fixed share of the grids, one in four, has a trap at the start square (one
  * grid in eight) or at the end square (one in eight), whatever the odds drew
  * there: the answer is then 0. The odds alone draw such a grid with odds of
  * about 1 in 50 to 1 in 100 at the top rung's start or end square, too rarely
  * to be offered as a trap. The share is drawn after the grid, one number a
  * site. At the top rung the grid is generated from a seed
  * (`SeededInput.Grid`), its trap squares as these draw them, the share
  * choosing the corner the program makes a trap.
  */
final class GridPaths(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[GridPaths.Site](spelling, rung):

  val problem: String = "grid_paths"

  val claim: String = "gezi.contest.corpora.reductions.GridPathsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[GridPaths.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.gridPaths(site.rows))
    )

  protected def site(draws: Draws): (GridPaths.Site, Draws) =
    val (side, afterSide) = CsesFamily.drawnParameter(draws, nominal, "side")
    val (odds, afterOdds) =
      CsesFamily.drawnParameter(afterSide, nominal, "trap_odds")
    rung.input match
      case RungInput.Written =>
        val (rows, after) = CsesFamily.drawnValues(side, afterOdds)(beforeRow =>
          CsesFamily.drawnValues(side, beforeRow)(current =>
            val (drawn, next) = CsesFamily.between(current, 1 to odds)
            (drawn != 1, next)
          )
        )
        val (share, afterShare) = CsesFamily.between(after, 0 to 7)
        val last = side - 1
        val blocked = share match
          case 0 => rows.updated(0, rows(0).updated(0, false))
          case 1 => rows.updated(last, rows(last).updated(last, false))
          case _ => rows
        (GridPaths.Site(SeededInput.Input.Written(blocked)), afterShare)
      case RungInput.Seeded =>
        val (seed, afterSeed) = CsesFamily.between(afterOdds, CsesFamily.seeds)
        val (share, afterShare) = CsesFamily.between(afterSeed, 0 to 7)
        val corner = share match
          case 0 => SeededInput.Corner.First
          case 1 => SeededInput.Corner.Last
          case _ => SeededInput.Corner.Neither
        (
          GridPaths.Site(
            SeededInput.Input.Seeded(
              SeededInput.Grid(seed, side, side, odds, corner)
            )
          ),
          afterShare
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.gridPaths

  def arguments(
      problems: CsesProblems,
      site: GridPaths.Site
  ): Vector[ProblemTerm] =
    Vector(site.input.argument(problems, CsesFamily.writtenGrid))

  /** The count of paths by a table that seeds the start square with 1 without
    * checking that it is free, and reads the end square without checking that
    * it is free: the answer where the start or the end square is a trap, which
    * is 0, is wrong, and it is right on every other grid.
    */
  def wrongAnswers(
      site: GridPaths.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(GridPaths.unguardedEndpoints(site.rows)))

/** The sites and the ladder of `GridPaths`. */
object GridPaths:

  /** The rows of a site's grid, true for a free square; written one row a line,
    * `.` for free and `*` for a trap, as CSES writes a grid.
    */
  final case class Site(input: SeededInput.Input[Vector[Vector[Boolean]]]):

    /** The rows. */
    def rows: Vector[Vector[Boolean]] = input.data

    override def toString: String = input.described(
      _.map(_.map(free => if free then '.' else '*').mkString)
        .mkString("Site(", "/", ")")
    )

  /** The wrong table of the common mistake: the paths to each square by ways(r,
    * c) = ways(r - 1, c) + ways(r, c - 1) modulo 10^9 + 7, with ways(0, 0) = 1
    * whether or not the start square is free, a trap zeroing every other square
    * but the end square, whose count is read without checking that it is free.
    */
  def unguardedEndpoints(rows: Vector[Vector[Boolean]]): BigInt =
    val width = rows.head.size
    val lastRow = rows.size - 1
    val above = Vector.tabulate(width)(column => if column == 0 then 1L else 0L)
    val last = rows.indices.foldLeft(above) { (previous, row) =>
      rows(row).indices.foldLeft(Vector.empty[Long]) { (current, column) =>
        val value =
          if row == 0 && column == 0 then 1L
          else if !rows(row)(column) && !(row == lastRow && column == width - 1)
          then 0L
          else
            (previous(column) + current.lastOption.getOrElse(
              0L
            )) % CsesFamily.modulus
        current :+ value
      }
    }
    BigInt(last(width - 1))

  /** The ladder: grids of sides up to 4 and up to 6, a square a trap with odds
    * from 1 in 2 to 1 in 4, read by the reference reading, and CSES's
    * constraint, 1 ≤ n ≤ 1000, the sides drawn from its upper half and a square
    * a trap with odds from 1 in 50 to 1 in 100, so that most grids have paths,
    * at most four sites. MEASURED 2026-11-21 by the probe of
    * `CoinCombinationsOrdered.rungs`: the single program of a grid all free
    * took, for sides 1 to 6, 1,496, 2,037, 3,105, 5,829, 13,360 and 37,704
    * steps and 751, 1,002, 1,469, 2,631, 5,794 and 15,930 tables (the paths are
    * built and counted); the repeated program of the seed 20261031 at side_4
    * and R = 4 took 2,636 steps and 1,259 tables (respelled 3,745 and 1,705)
    * and at R = 256 112,887 and 49,178 (respelled 249,730 and 107,467), at
    * side_6 and R = 4 3,753 and 1,769 (respelled 6,681 and 2,927) and at R =
    * 256 263,561 and 113,341, the respelled twin stopping at the probe's
    * 200,000 tables, past the reference reading's 50,000 at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "side_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("side", 1 to 4),
          NominalParameter("trap_odds", 2 to 4)
        )
      )
    ),
    CsesRung(
      "side_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("side", 1 to 6),
          NominalParameter("trap_odds", 2 to 4)
        )
      )
    ),
    CsesRung(
      "side_1000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("side", 500 to 1000),
          NominalParameter("trap_odds", 50 to 100)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[GridPaths]] =
    CsesFamily.families(rungs, GridPaths(_, _))

/** CSES 1158, Book Shop, `book_shop books x`: the most pages of books, each
  * bought at most once, whose prices sum to at most x. A site is n books, n
  * from the parameter `books`, each a price from the parameter `price` and a
  * number of pages from the parameter `pages`, and x from the parameter
  * `budget`.
  */
final class BookShop(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[BookShop.Site](spelling, rung):

  val problem: String = "book_shop"

  val claim: String = "gezi.contest.corpora.reductions.BookShopReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(drawn: CsesFamily.Drawn[BookShop.Site]): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.bookShop(site.books, site.budget))
    )

  protected def site(draws: Draws): (BookShop.Site, Draws) =
    val (count, afterCount) = CsesFamily.drawnParameter(draws, nominal, "books")
    val (books, afterBooks) =
      CsesFamily.drawnValues(count, afterCount)(current =>
        val (price, afterPrice) =
          CsesFamily.drawnParameter(current, nominal, "price")
        val (pages, afterPages) =
          CsesFamily.drawnParameter(afterPrice, nominal, "pages")
        ((price, pages), afterPages)
      )
    val (budget, after) =
      CsesFamily.drawnParameter(afterBooks, nominal, "budget")
    (BookShop.Site(books, budget), after)

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.bookShop

  def arguments(
      problems: CsesProblems,
      site: BookShop.Site
  ): Vector[ProblemTerm] =
    val naturals = CsesEncodings.naturals(
      site.budget +: site.books.flatMap((price, pages) => Vector(price, pages))
    )
    Vector(
      CsesEncodings.list(
        site.books.map((price, pages) =>
          CsesEncodings.pair(naturals(price), naturals(pages))
        )
      ),
      naturals(site.budget)
    )

  /** A solution that lets a book be bought any number of times. */
  def wrongAnswers(
      site: BookShop.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(BookShop.repeatedPages(site.books, site.budget)))

/** The sites, the repeated-books count and the ladder of `BookShop`. */
object BookShop:

  /** The books of a site, each its price and pages, and the budget x. */
  final case class Site(books: Vector[(Int, Int)], budget: Int)

  /** The most pages within the budget when a book may be bought any number of
    * times, by the unbounded knapsack recurrence most(b) = the largest most(b -
    * price) + pages over the books whose price is at most b, 0 where none is,
    * in O(n x) time.
    */
  def repeatedPages(books: Vector[(Int, Int)], budget: Int): BigInt =
    val most = (1 to budget).foldLeft(Vector(0L)) { (table, spent) =>
      table :+ books.foldLeft(0L) { case (best, (price, pages)) =>
        if price > spent then best else best.max(table(spent - price) + pages)
      }
    }
    BigInt(most(budget))

  /** The ladder: up to 4 and up to 7 books read by the reference reading, and
    * CSES's constraints, 1 ≤ n ≤ 1000, 1 ≤ x ≤ 10^5 and prices and pages from 1
    * to 1000, the counts and the budgets drawn from their upper halves, at most
    * four sites. MEASURED 2026-11-21 by the probe of
    * `CoinCombinationsOrdered.rungs`: the single program of the books (2, 1),
    * (3, 2), (4, 3), (1, 4), (2, 5), (3, 6), (4, 7), the first k of them at the
    * budget 8, took, for k from 1 to 7, 1,685, 2,286, 3,409, 5,630, 9,787,
    * 17,059 and 29,245 steps and 840, 1,115, 1,616, 2,588, 4,411, 7,631 and
    * 12,983 tables (the 2^k subsets are built); the repeated program of the
    * seed 20261031 at books_4 and R = 4 took 5,708 steps and 2,602 tables
    * (respelled 10,297 and 4,377) and at R = 256 192,049 and 79,240 (respelled
    * 385,392 and 156,326), at books_7 and R = 4 13,116 and 5,885 (respelled
    * 20,914 and 9,070), and at R = 256 both twins stopped at the probe's
    * 200,000 tables, past the reference reading's 50,000 at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "books_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("books", 1 to 4),
          NominalParameter("price", 1 to 4),
          NominalParameter("pages", 1 to 8),
          NominalParameter("budget", 1 to 8)
        )
      )
    ),
    CsesRung(
      "books_7",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("books", 1 to 7),
          NominalParameter("price", 1 to 4),
          NominalParameter("pages", 1 to 8),
          NominalParameter("budget", 1 to 8)
        )
      )
    ),
    CsesRung(
      "books_1000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("books", 500 to 1000),
          NominalParameter("price", 1 to 1000),
          NominalParameter("pages", 1 to 1000),
          NominalParameter("budget", 50000 to 100000)
        )
      )
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[BookShop]] =
    CsesFamily.families(rungs, BookShop(_, _))

/** CSES 1671, Shortest Routes I, `shortest_routes_single_source n flights`: the
  * sum over the cities of the least cost of a trip from city 1 to the city over
  * one-way flights. A site is n cities, n from the parameter `cities`, and m
  * flights, m from the parameter `flights` and at least n - 1, each cost from
  * the parameter `cost`, at least 1: the problem's premises, which its file's
  * program needs, are that every city is reached from city 1 (its program
  * answers the total cost plus one for a city none reaches, no answer of CSES)
  * and that every cost is positive (its recursion ends by that). So n - 1 of
  * the flights reach each city from city 1 or from a city reached before it,
  * the cities taken in an order drawn, and the others join any two cities, a
  * city to itself included; the flights are then shuffled.
  */
final class ShortestRoutesSingleSource(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[ShortestRoutesSingleSource.Site](spelling, rung):

  val problem: String = "shortest_routes_single_source"

  val claim: String =
    "gezi.contest.corpora.reductions.ShortestRoutesSingleSourceReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[ShortestRoutesSingleSource.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(
        CsesSolutions.shortestRoutesSingleSource(site.cities, site.flights)
      )
    )

  protected def site(draws: Draws): (ShortestRoutesSingleSource.Site, Draws) =
    val (cities, afterCities) =
      CsesFamily.drawnParameter(draws, nominal, "cities")
    val (wanted, afterWanted) =
      CsesFamily.drawnParameter(afterCities, nominal, "flights")
    val costs = Repetition.range(nominal, "cost")
    rung.input match
      case RungInput.Written =>
        ShortestRoutesSingleSource.written(cities, wanted, costs, afterWanted)
      case RungInput.Seeded =>
        val (treeSeed, afterTreeSeed) =
          CsesFamily.between(afterWanted, CsesFamily.seeds)
        val (flightSeed, after) =
          CsesFamily.between(afterTreeSeed, CsesFamily.seeds)
        val extra = math.max(wanted, cities - 1) - (cities - 1)
        val flights = SeededInput.Flights(
          treeSeed,
          flightSeed,
          cities,
          extra,
          costs.start,
          costs.end
        )
        (
          ShortestRoutesSingleSource.Site(
            cities,
            SeededInput.Input.Seeded(flights)
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.shortestRoutesSingleSource

  def arguments(
      problems: CsesProblems,
      site: ShortestRoutesSingleSource.Site
  ): Vector[ProblemTerm] =
    site.input match
      case SeededInput.Input.Written(flights) =>
        val naturals = CsesEncodings.naturals(
          site.cities +: flights.flatMap((from, to, cost) =>
            Vector(from, to, Math.toIntExact(cost))
          )
        )
        Vector(
          naturals(site.cities),
          CsesEncodings.list(
            flights.map((from, to, cost) =>
              CsesEncodings.triple(naturals, from, to, Math.toIntExact(cost))
            )
          )
        )
      case SeededInput.Input.Seeded(generator) =>
        Vector(CsesEncodings.natural(site.cities), generator.argument(problems))

  /** A solution off by one at every city's cost, the sum plus n, and one that
    * reads the flights as two-way.
    */
  def wrongAnswers(
      site: ShortestRoutesSingleSource.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Binary(digits) =>
      Vector(
        NativeValue.natural(CsesFamily.naturalOf(digits) + site.cities),
        NativeValue.natural(
          CsesSolutions.shortestRoutesSingleSource(
            site.cities,
            site.flights ++ site.flights.map((from, to, cost) =>
              (to, from, cost)
            )
          )
        )
      )
    case other => throw IllegalArgumentException(s"no natural: $other")

/** The sites and the ladder of `ShortestRoutesSingleSource`. */
object ShortestRoutesSingleSource:

  /** The count of cities and the flights of a site, each `(from, to, cost)`,
    * the cities from 1 to n, written or seeded.
    */
  final case class Site(
      cities: Int,
      input: SeededInput.Input[Vector[(Int, Int, Long)]]
  ):

    /** The flights. */
    def flights: Vector[(Int, Int, Long)] = input.data

    override def toString: String =
      s"Site($cities,${input.described(_.toString)})"

  /** A written site of n cities: a flight to each city but city 1 from a city
    * before it in an order drawn, so that every city is reached, then the
    * flights wanted beyond those, from and to any city, each cost from the
    * range, all in an order drawn.
    */
  def written(
      cities: Int,
      wanted: Int,
      costs: Range.Inclusive,
      afterWanted: Draws
  ): (Site, Draws) =
    val (order, afterOrder) =
      CsesFamily.shuffled((2 to cities).toVector, afterWanted)
    val (spanning, afterSpanning) = order.zipWithIndex.foldLeft(
      (Vector.empty[(Int, Int, Long)], afterOrder)
    ) { case ((found, current), (city, index)) =>
      val (earlier, afterEarlier) = CsesFamily.between(current, 0 to index)
      val (cost, afterCost) = CsesFamily.between(afterEarlier, costs)
      (
        found :+ ((
          if earlier == 0 then 1 else order(earlier - 1),
          city,
          cost.toLong
        )),
        afterCost
      )
    }
    val (others, afterOthers) = CsesFamily.drawnValues(
      math.max(wanted, cities - 1) - (cities - 1),
      afterSpanning
    )(current =>
      val (from, afterFrom) = CsesFamily.between(current, 1 to cities)
      val (to, afterTo) = CsesFamily.between(afterFrom, 1 to cities)
      val (cost, afterCost) = CsesFamily.between(afterTo, costs)
      ((from, to, cost.toLong), afterCost)
    )
    val (flights, after) = CsesFamily.shuffled(spanning ++ others, afterOthers)
    (Site(cities, SeededInput.Input.Written(flights)), after)

  /** The ladder: small graphs of small costs read by the reference reading, and
    * CSES's constraints, 1 ≤ n ≤ 10^5, 1 ≤ m ≤ 2 · 10^5 and 1 ≤ c ≤ 10^9, the
    * counts drawn from their upper halves, at most four sites. MEASURED
    * 2026-11-21 by the probe of `CoinCombinationsOrdered.rungs`: the single
    * program of a chain of n cities, each flight of cost 1, took, for n of 4,
    * 6, 8 and 11, 4,936, 12,491, 29,249 and 87,540 steps and 2,294, 5,621,
    * 13,000 and 38,660 tables, and of a cycle of 6 cities with two chords, each
    * of cost 3, 19,578 and 8,700 (the reading shares a table for each cost up
    * to the total and each city); the repeated program of the seed 20261031 at
    * cities_4 and R = 4 took 5,985 steps and 2,748 tables (respelled 9,377 and
    * 4,067) and at R = 256 348,796 and 149,530, the respelled twin stopping at
    * the probe's 200,000 tables, at cities_6 and R = 4 8,916 and 4,055
    * (respelled 12,796 and 5,539), and at R = 256 both twins stopped there,
    * past the reference reading's 50,000 tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "cities_4",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 4),
          NominalParameter("flights", 0 to 5),
          NominalParameter("cost", 1 to 3)
        )
      )
    ),
    CsesRung(
      "cities_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 6),
          NominalParameter("flights", 0 to 8),
          NominalParameter("cost", 1 to 3)
        )
      )
    ),
    CsesRung(
      "cities_100000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("cities", 50000 to 100000),
          NominalParameter("flights", 100000 to 200000),
          NominalParameter("cost", 1 to 1000000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[ShortestRoutesSingleSource]] =
    CsesFamily.families(rungs, ShortestRoutesSingleSource(_, _))

/** CSES 1672, Shortest Routes II, `shortest_routes_queries n roads queries`:
  * for each query of two cities, the least cost of a trip between them over
  * two-way roads, or none. A site is n cities, n from the parameter `cities`, m
  * roads, m from the parameter `roads`, each joining any two cities (a city to
  * itself and parallel roads included, as CSES allows) at a cost from the
  * parameter `cost`, at least 1 as the problem's premise asks, and q queries, q
  * from the parameter `queries`, each of any two cities. At the top rung the
  * roads and the queries are generated from two seeds (`SeededInput.Triples`,
  * `SeededInput.Pairs`), drawn as these draw them.
  */
final class ShortestRoutesQueries(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[ShortestRoutesQueries.Site](spelling, rung):

  val problem: String = "shortest_routes_queries"

  val claim: String =
    "gezi.contest.corpora.reductions.ShortestRoutesQueriesReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[ShortestRoutesQueries.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.Elements(
        CsesSolutions
          .shortestRoutesQueries(site.cities, site.roads, site.queries)
          .map(least => NativeValue.Optional(least.map(NativeValue.natural)))
      )
    )

  protected def site(draws: Draws): (ShortestRoutesQueries.Site, Draws) =
    val (cities, afterCities) =
      CsesFamily.drawnParameter(draws, nominal, "cities")
    val (roadCount, afterRoadCount) =
      CsesFamily.drawnParameter(afterCities, nominal, "roads")
    val costs = Repetition.range(nominal, "cost")
    rung.input match
      case RungInput.Written =>
        ShortestRoutesQueries.written(
          nominal,
          cities,
          roadCount,
          costs,
          afterRoadCount
        )
      case RungInput.Seeded =>
        val (queryCount, afterQueryCount) =
          CsesFamily.drawnParameter(afterRoadCount, nominal, "queries")
        val (roadSeed, afterRoadSeed) =
          CsesFamily.between(afterQueryCount, CsesFamily.seeds)
        val (querySeed, after) =
          CsesFamily.between(afterRoadSeed, CsesFamily.seeds)
        val roads = SeededInput.Triples(
          roadSeed,
          roadCount,
          1,
          cities,
          costs.start,
          costs.end
        )
        val queries = SeededInput.Pairs(querySeed, queryCount, 1, cities)
        (
          ShortestRoutesQueries.Site(
            cities,
            SeededInput.Input.Seeded(roads),
            SeededInput.Input.Seeded(queries)
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.shortestRoutesQueries

  def arguments(
      problems: CsesProblems,
      site: ShortestRoutesQueries.Site
  ): Vector[ProblemTerm] =
    (site.roadsInput, site.queriesInput) match
      case (
            SeededInput.Input.Written(roads),
            SeededInput.Input.Written(queries)
          ) =>
        val naturals = CsesEncodings.naturals(
          site.cities +: (roads.flatMap((first, second, cost) =>
            Vector(first, second, Math.toIntExact(cost))
          ) ++
            queries.flatMap((source, destination) =>
              Vector(source, destination)
            ))
        )
        Vector(
          naturals(site.cities),
          CsesEncodings.list(
            roads.map((first, second, cost) =>
              CsesEncodings
                .triple(naturals, first, second, Math.toIntExact(cost))
            )
          ),
          CsesEncodings.list(
            queries.map((source, destination) =>
              CsesEncodings.pair(naturals(source), naturals(destination))
            )
          )
        )
      case (
            SeededInput.Input.Seeded(roads),
            SeededInput.Input.Seeded(queries)
          ) =>
        Vector(
          CsesEncodings.natural(site.cities),
          roads.argument(problems),
          queries.argument(problems)
        )
      case _ =>
        throw IllegalStateException(
          s"a site's roads and queries are both written or both seeded: $site"
        )

  /** A solution that answers some 0 where no trip exists and none from a city
    * to itself, none and some 0 swapped at every query.
    */
  def wrongAnswers(
      site: ShortestRoutesQueries.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Elements(values) =>
      val zero = NativeValue.Optional(Some(NativeValue.natural(0)))
      val none = NativeValue.Optional(None)
      Vector(
        NativeValue.Elements(
          values.map(value =>
            if value == none then zero
            else if value == zero then none
            else value
          )
        )
      )
    case other => throw IllegalArgumentException(s"no list: $other")

/** The sites and the ladder of `ShortestRoutesQueries`. */
object ShortestRoutesQueries:

  /** The count of cities, the roads of a site, each `(first, second, cost)`,
    * and its queries, each `(source, destination)`, the cities from 1 to n,
    * written or seeded.
    */
  final case class Site(
      cities: Int,
      roadsInput: SeededInput.Input[Vector[(Int, Int, Long)]],
      queriesInput: SeededInput.Input[Vector[(Int, Int)]]
  ):

    /** The roads. */
    def roads: Vector[(Int, Int, Long)] = roadsInput.data

    /** The queries. */
    def queries: Vector[(Int, Int)] = queriesInput.data

    override def toString: String =
      s"Site($cities,${roadsInput.described(_.toString)},${queriesInput.described(_.toString)})"

  /** A written site of n cities and m roads: each road between any two cities,
    * its cost from the range, then the count of queries and each query of any
    * two cities.
    */
  def written(
      nominal: NominalRanges,
      cities: Int,
      roadCount: Int,
      costs: Range.Inclusive,
      afterRoadCount: Draws
  ): (Site, Draws) =
    val (roads, afterRoads) =
      CsesFamily.drawnValues(roadCount, afterRoadCount)(current =>
        val (first, afterFirst) = CsesFamily.between(current, 1 to cities)
        val (second, afterSecond) = CsesFamily.between(afterFirst, 1 to cities)
        val (cost, afterCost) = CsesFamily.between(afterSecond, costs)
        ((first, second, cost.toLong), afterCost)
      )
    val (queryCount, afterQueryCount) =
      CsesFamily.drawnParameter(afterRoads, nominal, "queries")
    val (queries, after) =
      CsesFamily.drawnValues(queryCount, afterQueryCount)(current =>
        val (source, afterSource) = CsesFamily.between(current, 1 to cities)
        val (destination, afterDestination) =
          CsesFamily.between(afterSource, 1 to cities)
        ((source, destination), afterDestination)
      )
    (
      Site(
        cities,
        SeededInput.Input.Written(roads),
        SeededInput.Input.Written(queries)
      ),
      after
    )

  /** The ladder: small graphs of small costs with few queries read by the
    * reference reading, and CSES's constraints, 1 ≤ n ≤ 500, 1 ≤ m ≤ n^2 and 1
    * ≤ c ≤ 10^9, the counts drawn from their upper halves, with 1,000 to 2,000
    * queries rather than CSES's 10^5, so that the answer, a list of the
    * queries' options, stays small while the native's work stays the closure of
    * the 500 cities, at most four sites. MEASURED 2026-11-21 by the probe of
    * `CoinCombinationsOrdered.rungs`: the single program of a chain of n
    * cities, each road of cost 1, and the one query from one end to the other
    * took, for n of 3, 4, 6, 8 and 11, 2,752, 4,008, 9,744, 22,360 and 66,878
    * steps and 1,338, 1,908, 4,509, 10,252 and 30,578 tables, and of a cycle of
    * 6 cities with a chord, each of cost 3, with three queries 22,878 and
    * 10,409; the repeated program of the seed 20261031 at cities_3 and R = 4
    * took 4,414 steps and 2,049 tables (respelled 7,500 and 3,320) and at R =
    * 256 130,630 and 56,055 (respelled 219,940 and 91,736), at cities_6 and R =
    * 4 6,744 and 3,102 (respelled 9,597 and 4,195), and at R = 256 both twins
    * stopped at the probe's 200,000 tables, past the reference reading's 50,000
    * at that R. The bottom rung was first cities 1 to 4, roads 0 to 4 and costs
    * 1 to 3; a scan of the seeds 0 to 2,999 at R of 1 and 2 found the direct
    * program of the seed 483 at R = 2 (two sites of 3 cities with a city's road
    * to itself and a query no trip answers) to take 220,769 steps and 96,392
    * tables, past the 50,000 the family's suite reads within; at cities_3 a
    * scan of the seeds 0 to 399, both twins, found none above 12,108 tables.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "cities_3",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 3),
          NominalParameter("roads", 0 to 3),
          NominalParameter("cost", 1 to 2),
          NominalParameter("queries", 1 to 2)
        )
      )
    ),
    CsesRung(
      "cities_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("cities", 1 to 6),
          NominalParameter("roads", 0 to 7),
          NominalParameter("cost", 1 to 3),
          NominalParameter("queries", 1 to 3)
        )
      )
    ),
    CsesRung(
      "cities_500",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("cities", 250 to 500),
          NominalParameter("roads", 125000 to 250000),
          NominalParameter("cost", 1 to 1000000000),
          NominalParameter("queries", 1000 to 2000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[ShortestRoutesQueries]] =
    CsesFamily.families(rungs, ShortestRoutesQueries(_, _))

/** CSES 1713, Counting Divisors, `counting_divisors numbers`: the sum over the
  * numbers of the number of divisors of each. A site is n numbers, n from the
  * parameter `numbers`, each from the parameter `value`, written out below the
  * top rung and generated from a seed at it (`CsesFamily.drawnNumbers`).
  */
final class CountingDivisors(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[CountingDivisors.Site](spelling, rung):

  val problem: String = "counting_divisors"

  val claim: String =
    "gezi.contest.corpora.reductions.CountingDivisorsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[CountingDivisors.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.countingDivisors(site.numbers))
    )

  protected def site(draws: Draws): (CountingDivisors.Site, Draws) =
    CsesFamily.drawnNumbers(draws, nominal, rung.input, "numbers", "value")

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.countingDivisors

  def arguments(
      problems: CsesProblems,
      site: CountingDivisors.Site
  ): Vector[ProblemTerm] = Vector(site.argument(problems))

  /** A solution off by one at every number's count, the sum plus n. */
  def wrongAnswers(
      site: CountingDivisors.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Binary(digits) =>
      Vector(
        NativeValue.natural(CsesFamily.naturalOf(digits) + site.numbers.size)
      )
    case other => throw IllegalArgumentException(s"no natural: $other")

/** The sites and the ladder of `CountingDivisors`. */
object CountingDivisors:

  /** The numbers of a site. */
  type Site = CsesFamily.NumbersSite

  /** The ladder: up to three numbers up to 16 and up to 48 read by the
    * reference reading, and CSES's constraints, 1 ≤ n ≤ 10^5 numbers, each 1 ≤
    * x ≤ 10^6, the counts drawn from the upper half, at most four sites.
    * MEASURED 2026-11-21 by the probe of `CoinCombinationsOrdered.rungs`: the
    * single program of the list (16) took 14,059 steps and 6,130 tables, of
    * (14, 15, 16) 24,050 and 10,289, of (24) 20,758 and 8,978, of (48) 49,499
    * and 21,118, of (75) 92,318 and 39,197, of (22, 23, 24) 37,932 and 16,154
    * and of (46, 47, 48) 91,841 and 38,779 (every number up to x is tried); the
    * repeated program of the seed 20261031 at value_16 and R = 4 took 21,023
    * steps and 8,980 tables (respelled 32,241 and 13,425) and at R = 256 89,327
    * and 31,149 (respelled 117,693 and 41,634), at value_48 and R = 4 115,736
    * and 48,652 (respelled 298,923 and 122,985), and at R = 256 365,528 and
    * 146,724, the respelled twin stopping at the probe's 200,000 tables, past
    * the reference reading's 50,000 at those R. The bottom rung was first
    * values up to 24, where a scan of the seeds 0 to 399 at R of 1 and 2 found
    * respelled programs of up to 43,090 tables and 0.9 s, near the 50,000
    * tables and the 3 s deadline the family's suite reads within.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "value_16",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 3),
          NominalParameter("value", 1 to 16)
        )
      )
    ),
    CsesRung(
      "value_48",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 3),
          NominalParameter("value", 1 to 48)
        )
      )
    ),
    CsesRung(
      "value_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("numbers", 50000 to 100000),
          NominalParameter("value", 1 to 1000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[CountingDivisors]] =
    CsesFamily.families(rungs, CountingDivisors(_, _))

/** CSES 1079, Binomial Coefficients, `binomial_coefficients queries`: a choose
  * b modulo 10^9 + 7 for each query, the list of the values. A site is q
  * queries, q from the parameter `queries`, each a drawn from the parameter
  * `whole` and b from 0 to a, as the problem's premise asks. At the top rung
  * the queries are generated from a seed (`SeededInput.BinomialQueries`): a and
  * b the larger and the smaller of two numbers drawn from the parameter
  * `whole`.
  */
final class BinomialCoefficients(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[BinomialCoefficients.Site](spelling, rung):

  val problem: String = "binomial_coefficients"

  val claim: String =
    "gezi.contest.corpora.reductions.BinomialCoefficientsReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[BinomialCoefficients.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.Elements(
        CsesSolutions
          .binomialCoefficients(site.queries)
          .map(NativeValue.natural)
      )
    )

  protected def site(draws: Draws): (BinomialCoefficients.Site, Draws) =
    val (count, afterCount) =
      CsesFamily.drawnParameter(draws, nominal, "queries")
    rung.input match
      case RungInput.Written =>
        val (queries, after) =
          CsesFamily.drawnValues(count, afterCount)(current =>
            val (whole, afterWhole) =
              CsesFamily.drawnParameter(current, nominal, "whole")
            val (chosen, afterChosen) =
              CsesFamily.between(afterWhole, 0 to whole)
            ((whole, chosen), afterChosen)
          )
        (BinomialCoefficients.Site(SeededInput.Input.Written(queries)), after)
      case RungInput.Seeded =>
        val (seed, after) = CsesFamily.between(afterCount, CsesFamily.seeds)
        val wholes = Repetition.range(nominal, "whole")
        require(
          wholes.start == 0,
          s"a seeded query's numbers are drawn from 0: $wholes"
        )
        (
          BinomialCoefficients.Site(
            SeededInput.Input.Seeded(
              SeededInput.BinomialQueries(seed, count, wholes.end)
            )
          ),
          after
        )

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.binomialCoefficients

  def arguments(
      problems: CsesProblems,
      site: BinomialCoefficients.Site
  ): Vector[ProblemTerm] =
    Vector(
      site.input.argument(
        problems,
        queries =>
          val naturals = CsesEncodings.naturals(
            queries.flatMap((whole, chosen) => Vector(whole, chosen))
          )
          CsesEncodings.list(
            queries.map((whole, chosen) =>
              CsesEncodings.pair(naturals(whole), naturals(chosen))
            )
          )
      )
    )

  /** A solution that forgets the modulus, a choose b exactly, at each query
    * where a^min(b, a - b), a bound of it, has at most
    * `BinomialCoefficients.unreducedBits` bits (a larger one is no trap a
    * judgment point could carry), the right value at the others.
    */
  def wrongAnswers(
      site: BinomialCoefficients.Site,
      answer: NativeValue
  ): Vector[NativeValue] = answer match
    case NativeValue.Elements(values) =>
      Vector(
        NativeValue.Elements(
          site.queries
            .zip(values)
            .map((query, value) =>
              BinomialCoefficients.unreduced(query).getOrElse(value)
            )
        )
      )
    case other => throw IllegalArgumentException(s"no list: $other")

/** The sites, the unreduced values and the ladder of `BinomialCoefficients`. */
object BinomialCoefficients:

  /** The queries of a site, each `(a, b)` with 0 ≤ b ≤ a, written or seeded. */
  final case class Site(input: SeededInput.Input[Vector[(Int, Int)]]):

    /** The queries. */
    def queries: Vector[(Int, Int)] = input.data

    override def toString: String = s"Site(${input.described(_.toString)})"

  /** The most bits of the bound a^min(b, a - b) of an unreduced value written
    * as a trap.
    */
  val unreducedBits: Long = 4096

  /** a choose b exactly, as the natural of a trap, where a^min(b, a - b) has at
    * most `unreducedBits` bits.
    */
  def unreduced(query: (Int, Int)): Option[NativeValue] =
    val (whole, chosen) = query
    val smaller = math.min(chosen, whole - chosen)
    Option.when(BigInt(whole).bitLength.toLong * smaller <= unreducedBits)(
      NativeValue.natural(
        (1 to smaller).foldLeft(BigInt(1))((product, factor) =>
          product * (whole - smaller + factor) / factor
        )
      )
    )

  /** The ladder: up to three queries of a up to 6 and up to 10 read by the
    * reference reading, and CSES's constraint 0 ≤ b ≤ a ≤ 10^6 with 1,000 to
    * 2,000 queries rather than CSES's 10^5, so that the answer, a list of the
    * values, stays small while the native's factorial table up to the largest
    * a, close to 10^6, still dominates its work, at most four sites. MEASURED
    * 2026-11-21 by the probe of `CoinCombinationsOrdered.rungs`: the single
    * program of the queries (6, 3) took 5,840 steps and 2,666 tables, (10, 5)
    * 30,929 and 13,195, (11, 5) 49,801 and 21,083, (6, 3), (6, 2), (5, 2) 9,506
    * and 4,234, and (10, 5), (10, 4), (9, 4) 57,942 and 24,278 (the subsets are
    * built and counted); the repeated program of the seed 20261031 at whole_6
    * and R = 4 took 11,790 steps and 5,205 tables (respelled 18,398 and 7,909)
    * and at R = 256 68,077 and 23,780 (respelled 175,087 and 67,146), at
    * whole_10 and R = 4 34,288 and 14,708 (respelled 53,464 and 22,560) and at
    * R = 256 281,828 and 111,867 (respelled 434,668 and 175,417), past the
    * reference reading's 50,000 tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "whole_6",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("queries", 1 to 3),
          NominalParameter("whole", 0 to 6)
        )
      )
    ),
    CsesRung(
      "whole_10",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("queries", 1 to 3),
          NominalParameter("whole", 0 to 10)
        )
      )
    ),
    CsesRung(
      "whole_1000000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("queries", 1000 to 2000),
          NominalParameter("whole", 0 to 1000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[BinomialCoefficients]] =
    CsesFamily.families(rungs, BinomialCoefficients(_, _))

/** CSES 1621, Distinct Numbers, `distinct_numbers numbers`: the number of
  * different values in the list. A site is n numbers, n from the parameter
  * `numbers`, each from the parameter `value`, written out below the top rung
  * and generated from a seed at it (`CsesFamily.drawnNumbers`).
  */
final class DistinctNumbers(spelling: Spelling, rung: CsesRung)
    extends CsesFamily[DistinctNumbers.Site](spelling, rung):

  val problem: String = "distinct_numbers"

  val claim: String =
    "gezi.contest.corpora.reductions.DistinctNumbersReferenceTest"

  /** The best known algorithm on the sites' data (`CsesSolutions`). */
  def solved(
      drawn: CsesFamily.Drawn[DistinctNumbers.Site]
  ): Vector[NativeValue] =
    drawn.sites.map(site =>
      NativeValue.natural(CsesSolutions.distinctNumbers(site.numbers))
    )

  protected def site(draws: Draws): (DistinctNumbers.Site, Draws) =
    CsesFamily.drawnNumbers(draws, nominal, rung.input, "numbers", "value")

  protected def function(problems: CsesProblems): Configured[NoFacts.type] =
    problems.distinctNumbers

  def arguments(
      problems: CsesProblems,
      site: DistinctNumbers.Site
  ): Vector[ProblemTerm] = Vector(site.argument(problems))

  /** A solution that answers the length of the list. */
  def wrongAnswers(
      site: DistinctNumbers.Site,
      answer: NativeValue
  ): Vector[NativeValue] =
    Vector(NativeValue.natural(site.numbers.size))

/** The sites and the ladder of `DistinctNumbers`. */
object DistinctNumbers:

  /** The numbers of a site. */
  type Site = CsesFamily.NumbersSite

  /** The ladder: up to 12 and up to 24 numbers, each up to 16 and up to 32,
    * read by the reference reading, and CSES's constraints, 1 ≤ n ≤ 2 · 10^5
    * and 1 ≤ x ≤ 10^9, the counts drawn from the upper half, at most four
    * sites. MEASURED 2026-11-21 by the probe of
    * `CoinCombinationsOrdered.rungs`: the single program of the numbers 1 to n
    * took, for n of 6, 12, 24, 48 and 65, 2,282, 4,498, 12,639, 43,808 and
    * 77,822 steps and 1,086, 1,979, 5,161, 17,133 and 30,115 tables (each
    * number is compared with every earlier one); the repeated program of the
    * seed 20261031 at numbers_12 and R = 4 took 5,745 steps and 2,487 tables
    * (respelled 7,028 and 3,003) and at R = 256 112,696 and 43,339 (respelled
    * 205,374 and 81,560), at numbers_24 and R = 4 20,924 and 8,401 (respelled
    * 35,366 and 14,863) and at R = 256 327,171 and 122,184 (respelled 437,193
    * and 162,411), past the reference reading's 50,000 tables at that R.
    */
  val rungs: Vector[CsesRung] = Vector(
    CsesRung(
      "numbers_12",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 12),
          NominalParameter("value", 1 to 16)
        )
      )
    ),
    CsesRung(
      "numbers_24",
      NominalRanges(
        Repetition.repetitions,
        Vector(
          NominalParameter("numbers", 1 to 24),
          NominalParameter("value", 1 to 32)
        )
      )
    ),
    CsesRung(
      "numbers_200000",
      NominalRanges(
        1 to 4,
        Vector(
          NominalParameter("numbers", 100000 to 200000),
          NominalParameter("value", 1 to 1000000000)
        )
      ),
      RungInput.Seeded
    )
  )

  /** Each rung's family in both spellings. */
  val families: Vector[Vector[DistinctNumbers]] =
    CsesFamily.families(rungs, DistinctNumbers(_, _))
