package com.yang_bo.gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.λ
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.saturation.StopSignal

private given narrowListBranchLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the list branch: a recursion that reads a list by
  * `(l ∥ list_type (binary_set true)) n (λh t. a)` is its program's one block
  * and computes what its definition says, a fold the sum of its list's
  * elements, a recursion over two lists, carrying the second whole while it
  * walks the first and then calling the fold on it, the sum of both; the fold
  * given a natural where it reads a list gives no value; and a fold whose list
  * is also filtered as a natural, `((l ∥ binary_set true) ∥ list_type
  * (binary_set true)) n (λh t. a)`, gives no value on a list. Their purpose is
  * to catch a branch that takes the wrong case, a head or a tail read from the
  * wrong place of the list, a list that a call does not carry whole, a natural
  * that a list branch reads, which would throw in the generated code instead of
  * giving no value, and a filter the block drops unchecked, which would give a
  * value where the term has none. The library is `NarrowListLibrary`'s; the
  * recursions are written as terms and defunctionalized by the front end, so
  * their codes are the ones it writes.
  */
class NarrowListBranchLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  private def closed(instruction: Configured[NoFacts.type]): Term =
    Term.closed(instruction)

  private val fixpoint = closed(NarrowBlocks.fixpointByValue)

  private val filter = closed(listCriterion(true))

  /** λs l. (l ∥ list_type (binary_set true)) zero (λh t. plus h (s t)), the sum
    * of a list's elements.
    */
  private val sum: Term =
    λ(self =>
      λ(summand =>
        (summand ∥ filter)(closed(zero))(
          λ(head => λ(tail => closed(plus)(head)(self(tail))))
        )
      )
    )

  /** λs a b. (a ∥ list_type (binary_set true)) (fixpoint sum b) (λh t. plus h
    * (s t b)), the sum of both lists' elements.
    */
  private val sumOfBoth: Term =
    λ(self =>
      λ(first =>
        λ(second =>
          (first ∥ filter)(fixpoint(sum)(second))(
            λ(head => λ(tail => closed(plus)(head)(self(tail)(second))))
          )
        )
      )
    )

  /** λs l. ((l ∥ binary_set true) ∥ list_type (binary_set true)) zero (λh t.
    * plus h (s t)), the fold whose list is filtered as a natural too: no list
    * meets that filter.
    */
  private val sumThroughNatural: Term =
    λ(self =>
      λ(summand =>
        ((summand ∥ closed(criterion(true))) ∥ filter)(closed(zero))(
          λ(head => λ(tail => closed(plus)(head)(self(tail))))
        )
      )
    )

  /** The list of the elements, filtered at its root by `list_type (binary_set
    * true)`, as an operand of a block is written.
    */
  private def filteredList(elements: Vector[(Int, Boolean)]): Term = closed(
    NoFacts.parallel(list(elements), listCriterion(true))
  )

  private def program(term: Term): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))(using
      com.yang_bo.gezi.ir.NoFacts
    )

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] =
    Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 7)))

  /** The elements of a non-empty list, each a value and whether it is written
    * filtered: nil alone is the term of true, no operand.
    */
  private val elements: Gen[Vector[(Int, Boolean)]] =
    Gen
      .list(
        for { number <- value; filtered <- Gen.boolean } yield (
          number,
          filtered
        ),
        Range.linear(1, 8)
      )
      .map(_.toVector)

  private def summed(written: Vector[(Int, Boolean)]): Long =
    written.map(_._1.toLong).sum

  stoppableProperty(
    "a recursion over lists is one block and computes its definition; a natural read as a list gives no value"
  ) { stopped =>
    for
      first <- elements.forAll
      second <- elements.forAll
      number <- value.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      def computed(program: Configured[NoFacts.type]) =
        compilation
          .compiled(compilation.blocks(program), DebugAttributes.Omitted, stop)
          .map(_.map(_.run(stop)))
      val programs = Vector(
        (
          program(fixpoint(sum)(filteredList(first))),
          Some(BigInteger.valueOf(summed(first)))
        ),
        (
          program(
            fixpoint(sumOfBoth)(filteredList(first))(filteredList(second))
          ),
          Some(BigInteger.valueOf(summed(first) + summed(second)))
        ),
        (program(fixpoint(sum)(closed(numeral(number)))), None),
        (program(fixpoint(sumThroughNatural)(filteredList(first))), None)
      )
      Result
        .all(
          programs.toList.zipWithIndex.map {
            case ((block, expected), position) =>
              Result
                .all(
                  List(
                    Result
                      .assert(compilation.blocks(block) == Vector(block))
                      .log(
                        s"the program is not its one block: ${compilation.blocks(block).size} blocks"
                      ),
                    Result
                      .diff(computed(block), Right(Vector(expected)))(_ == _)
                  )
                )
                .log(s"the program $position")
          }
        )
        .log(
          s"the first list ${first.mkString(", ")}, the second ${second.mkString(", ")}, the number $number"
        )
  }
