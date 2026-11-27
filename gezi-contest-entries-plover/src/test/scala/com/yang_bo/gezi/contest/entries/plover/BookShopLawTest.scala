package com.yang_bo.gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.contest.natives.plover.BookShop
import com.yang_bo.gezi.generatedinputs.GeneratedProperties

/** The law of the book shop: the native's value is the most pages over every
  * subset of the books within the budget. Its purpose is to catch a book bought
  * twice, a budget met exactly, a free book, a book dearer than the budget, a
  * budget above the total price and an empty shop.
  */
class BookShopLawTest extends GeneratedProperties:

  private val drawnBooks: Gen[List[(Int, Int)]] =
    Gen.choice1(
      Gen.constant(Nil),
      (for
        price <- Gen.int(Range.linear(0, 12))
        pages <- Gen.int(Range.linear(0, 30))
      yield (price, pages)).list(Range.linear(1, 11))
    )

  property("the value is the most pages of a subset within the budget") {
    for
      books <- drawnBooks.forAll
      budget <- Gen.int(Range.linear(0, 80)).forAll
    yield
      val most = books.indices.toSet
        .subsets()
        .map(_.toList.map(books))
        .collect {
          case chosen if chosen.map(_._1).sum <= budget => chosen.map(_._2).sum
        }
        .max
      val computed = BookShop.most(
        Vector(
          books.toVector.map(book => BigInteger.valueOf(book._1.toLong)),
          books.toVector.map(book => BigInteger.valueOf(book._2.toLong))
        ),
        BigInteger.valueOf(budget.toLong)
      )
      Result.diff(BigInt(computed), BigInt(most))(_ == _)
  }
