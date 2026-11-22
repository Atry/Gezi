package gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.saturation.StopSignal

/** The laws of the narrow lists' representation:
  * a list of canonical naturals filtered by `list_type (binary_set p)` at its
  * root, and at any of its tails by such filters, decodes to the narrow list
  * of its elements exactly when every filter admits the elements from its
  * place on, and with no filter at its root to none; and a block that
  * reads a list where it reads a natural, a
  * native's operand given the list directly or through a function's
  * parameter, gives no value, while the same block given a natural computes
  * it. Their purpose is to catch a list decoded that a filter does not
  * admit or that no filter governs, an element lost or reordered by the
  * decoding, a tail filter lost by the bookkeeping, and a list that
  * reaches a native, which would throw in the generated code instead of
  * giving no value. The library is `NarrowListLibrary`'s.
  */
class NarrowListLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] = Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 7)))

  /** The elements of a list, at least `least` of them, each a value and
    * whether it is written filtered.
    */
  private def elements(least: Int): Gen[Vector[(Int, Boolean)]] =
    Gen.list(for { number <- value; filtered <- Gen.boolean } yield (number, filtered), Range.linear(least, 6)).map(_.toVector)

  stoppableProperty("a list filtered by list_type (binary_set p) at its root and tails decodes to its elements exactly when each filter admits them") {
    _ =>
      for
        written <- elements(0).forAll
        admitsZero <- Gen.boolean.forAll
        tailFilters <-
          Gen.list(for { place <- Gen.int(Range.constant(1, 6)); admits <- Gen.boolean } yield (place, admits), Range.linear(0, 3)).forAll
      yield
        val numbers = written.map(_._1)
        val filters = tailFilters.filter(_._1 <= written.size).toMap
        val admitted = (filters + (0 -> admitsZero)).forall((place, admits) => admits || numbers.drop(place).forall(_ > 0))
        val expected = Option.when(admitted)(NarrowList(numbers.map(number => BigInteger.valueOf(number.toLong)), 0))
        Result
          .all(
            List(
              Result.diff(compilation.listDecoded(Instruction.Parallel(tailsFiltered(written, filters), listCriterion(admitsZero))), expected)(
                _ == _
              ),
              Result.diff(compilation.listDecoded(tailsFiltered(written, filters)), None)(_ == _).log("with no filter at its root")
            )
          )
          .log(s"the elements ${written.mkString(", ")}, admitting zero: $admitsZero, the tails' filters ${filters.toVector.sorted.mkString(", ")}")
  }

  /** λl. plus l zero, a function whose parameter is plus's operand. */
  private val plusZero =
    Instruction.Thunk(Code.Apply(Code.Apply(Code.Slot(1), Code.Slot(0)), Code.Slot(2)), Vector(Hole.Bound(0)), Vector(plus, zero))

  stoppableProperty("a list read as a natural gives no value; a natural in its place gives the sum") { stopped =>
    for
      written <- elements(1).forAll
      number <- value.forAll
    yield
      val filteredList = Instruction.Parallel(list(written), listCriterion(true))
      val stop = StopSignal.completedWith(stopped)
      def computed(program: Instruction) =
        compilation.compiled(compilation.blocks(program), DebugAttributes.Omitted, stop).map(_.map(_.run(stop)))
      val programs = Vector(
        (Instruction.Apply(Instruction.Apply(plus, filteredList), numeral(number)), None),
        (Instruction.Apply(plusZero, filteredList), None),
        (Instruction.Apply(Instruction.Apply(plus, numeral(number)), numeral(number)), Some(BigInteger.valueOf(2L * number))),
        (Instruction.Apply(plusZero, numeral(number)), Some(BigInteger.valueOf(number.toLong)))
      )
      Result
        .all(
          programs.toList.zipWithIndex.map { case ((program, expected), position) =>
            Result
              .all(
                List(
                  Result
                    .assert(compilation.blocks(program) == Vector(program))
                    .log(s"the program is not its one block: ${compilation.blocks(program).size} blocks"),
                  Result.diff(computed(program), Right(Vector(expected)))(_ == _)
                )
              )
              .log(s"the program $position")
          }
        )
        .log(s"the elements ${written.mkString(", ")}, the number $number")
  }
