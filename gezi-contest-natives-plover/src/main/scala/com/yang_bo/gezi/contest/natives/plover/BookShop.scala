package com.yang_bo.gezi.contest.natives.plover

import java.math.BigInteger

/** The most pages of books whose prices sum to at most a budget, each bought at
  * most once, the value of the definition it replaces, the typed version
  * `plover_typed_book_shop`, by the 0-1 knapsack over the budgets up to the
  * smaller of the budget and the total price. The books come column by column,
  * the prices then the pages, canonical naturals, which is what the native's
  * place declares; a native does not check its operands (`CONTRIBUTING.md`,
  * "Types live only in the term").
  */
object BookShop:

  /** The most table cells, books times budgets, the native computes. */
  private val largestTable: BigInteger = BigInteger.valueOf(2000000000L)

  /** The most pages. Throws `ArithmeticException` when the table has more than
    * `largestTable` cells or the pages of all the books do not fit an `Int`.
    */
  def most(books: Vector[Vector[BigInteger]], budget: BigInteger): BigInteger =
    val Vector(prices, pages) = books: @unchecked
    val totalPrice = prices.foldLeft(BigInteger.ZERO)(_.add(_))
    val totalPages = pages.foldLeft(BigInteger.ZERO)(_.add(_))
    if budget.compareTo(totalPrice) >= 0 then totalPages
    else
      if totalPages.bitLength > 30 || budget
          .add(BigInteger.ONE)
          .multiply(BigInteger.valueOf(prices.size.toLong))
          .compareTo(largestTable) > 0
      then
        throw ArithmeticException(
          s"a table of ${prices.size} books, a budget of $budget and $totalPages pages is too large"
        )
      val capacity = budget.intValueExact
      val affordable = prices
        .zip(pages)
        .filter((price, _) => price.compareTo(budget) <= 0)
        .map((price, page) => (price.intValueExact, page.intValueExact))
      val best = affordable.foldLeft(IArray.fill(capacity + 1)(0)) {
        case (before, (price, page)) =>
          IArray.tabulate(capacity + 1)(spent =>
            if spent >= price then
              math.max(before(spent), before(spent - price) + page)
            else before(spent)
          )
      }
      BigInteger.valueOf(best(capacity).toLong)
