package gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction
import gezi.saturation.StopSignal

/** The laws of a narrow block's memo ([[gezi.narrowblocks.lists.NarrowMemo]]), on a recursion over two lists whose calls reach
  * every pair of suffixes along many paths, as the edit distance's do:
  * `f a b` is zero when both are nil, and otherwise adds the heads to the
  * calls on the pairs one step shorter, `f (tail a) b` and `f a (tail b)`.
  * The clearing law: the block's value from the empty memo is its value from
  * the memo that retains nothing (`NarrowMemo.forgetting`), the memo emptied
  * before every call. The count law: from the empty memo, the recursion's
  * body is evaluated once for each pair of suffixes, (n + 1)(m + 1) times for
  * lists of n and m elements, and the memo holds as many entries. Their
  * purpose is to catch a key that leaves out an argument or confuses two
  * suffixes, which would answer a call with another call's value, a memo that
  * never hits, which would evaluate a body once per path, and a record made
  * before the body returns.
  */
class NarrowMemoLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  private def closed(instruction: Instruction): Term = Term.closed(instruction)

  private val fixpoint = closed(NarrowBlocks.fixpointByValue)

  private val filter = closed(listCriterion(true))

  /** λs a b. (a ∥ L) ((b ∥ L) zero (λh t. plus h (s a t)))
    * (λh t. (b ∥ L) (plus h (s t b)) (λk u. plus (plus h k) (plus (s t b) (s a u)))),
    * L being `list_type (binary_set true)`.
    */
  private val paths: Term =
    λ(self =>
      λ(first =>
        λ(second =>
          (first ∥ filter)(
            (second ∥ filter)(closed(zero))(λ(head => λ(tail => closed(plus)(head)(self(first)(tail)))))
          )(
            λ(head =>
              λ(tail =>
                (second ∥ filter)(closed(plus)(head)(self(tail)(second)))(
                  λ(otherHead =>
                    λ(otherTail =>
                      closed(plus)(closed(plus)(head)(otherHead))(closed(plus)(self(tail)(second))(self(first)(otherTail)))
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The list of the elements, filtered at its root by `list_type (binary_set
    * true)`, as an operand of a block is written.
    */
  private def filteredList(elements: Vector[(Int, Boolean)]): Term = closed(Instruction.Parallel(list(elements), listCriterion(true)))

  private def program(term: Term): Instruction = Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] = Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 7)))

  /** The elements of a non-empty list, each a value and whether it is
    * written filtered: nil alone is the term of true, no operand. At most
    * five, so that the run without the memo, whose calls grow as the
    * number of paths, stays small.
    */
  private val elements: Gen[Vector[(Int, Boolean)]] =
    Gen.list(for { number <- value; filtered <- Gen.boolean } yield (number, filtered), Range.linear(1, 5)).map(_.toVector)

  stoppableProperty("a recursion's value is the same from the memo emptied before every call, and its body runs once a pair of suffixes") {
    stopped =>
      for
        first <- elements.forAll
        second <- elements.forAll
      yield
        val stop = StopSignal.completedWith(stopped)
        val block = program(fixpoint(paths)(filteredList(first))(filteredList(second)))
        compilation.compiled(compilation.blocks(block), DebugAttributes.Omitted, stop) match
          case Left(reason) => Result.failure.log(s"the block does not compile: $reason")
          case Right(Vector(compiled)) =>
            val memoized = compiled.ranWith(stop, NarrowMemo.empty)
            val cleared = compiled.ranWith(stop, NarrowMemo.forgetting)
            val pairs = (first.size + 1).toLong * (second.size + 1)
            Result
              .all(
                List(
                  Result.diff(memoized.map(_._1), cleared.map(_._1))(_ == _).log("the clearing law"),
                  Result.assert(memoized.isDefined).log("the block gives no value"),
                  Result
                    .diff(memoized.map(found => (found._2.recorded, found._2.entries.size.toLong)), Some((pairs, pairs)))(_ == _)
                    .log("the count law: the bodies evaluated and the entries, against the pairs of suffixes")
                )
              )
              .log(s"the first list ${first.mkString(", ")}, the second ${second.mkString(", ")}")
          case Right(programs) => Result.failure.log(s"the program is not one block: ${programs.size} blocks")
  }
