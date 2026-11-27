package gezi.narrowblocks
package lists

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.frontend.Term.λ
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.saturation.StopSignal

private given narrowSelectLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the boolean branch:
  *   - a recursion that counts a natural's occurrences in a list by
  *     `(equality h n ∥ boolean_type) (increment (s t n)) (s t n)` is its
  *     program's one block and computes the count;
  *   - a let of a filtered boolean literal selects by it;
  *   - the case not selected is not evaluated, so a case that would give no
  *     value does not stop the one selected;
  *   - a natural where the branch reads a boolean gives no value;
  *   - equality's call on closed naturals, a boolean, is no block of its own.
  * Their purpose is to catch a branch that takes the wrong case, an equality or
  * an increment that computes something else, a boolean native called by the
  * wrong JVM convention (a `VerifyError` or a `NoSuchMethodError`), a case
  * evaluated before the selection, a natural read as a boolean, which would
  * throw in the generated code instead of giving no value, and a boolean
  * compiled as a natural's block. The library is `NarrowListLibrary`'s; the
  * programs are written as terms and defunctionalized by the front end, so
  * their codes are the ones it writes.
  */
class NarrowSelectLawTest extends GeneratedProperties:

  import NarrowListLibrary.*

  private def closed(instruction: Configured[NoFacts.type]): Term =
    Term.closed(instruction)

  private val fixpoint = closed(NarrowBlocks.fixpointByValue)

  private val listFilter = closed(listCriterion(true))

  private val booleanFilter = closed(booleanType)

  /** λs l n. (l ∥ list_type (binary_set true)) zero (λh t. (equality h n ∥
    * boolean_type) (increment (s t n)) (s t n)), the number of the occurrences
    * of n in l.
    */
  private val count: Term =
    λ(self =>
      λ(list =>
        λ(sought =>
          (list ∥ listFilter)(closed(zero))(
            λ(head =>
              λ(tail =>
                (closed(equality)(head)(sought) ∥ booleanFilter)(
                  closed(increment)(self(tail)(sought))
                )(self(tail)(sought))
              )
            )
          )
        )
      )
    )

  /** λb. (b ∥ boolean_type) x y, applied to the argument given. */
  private def selected(argument: Term, whenTrue: Term, whenFalse: Term): Term =
    λ(truthValue => (truthValue ∥ booleanFilter)(whenTrue)(whenFalse))(argument)

  private def program(term: Term): Configured[NoFacts.type] =
    Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))(using
      gezi.ir.NoFacts
    )

  /** A numeral's value, zero one time in three. */
  private val value: Gen[Int] =
    Gen.frequency1(1 -> Gen.constant(0), 2 -> Gen.int(Range.constant(1, 4)))

  /** The elements of a non-empty list, small enough that values repeat. */
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

  private def booleanLiteral(truthValue: Boolean): Term =
    closed(NoFacts.parallel(if truthValue then truth else falsity, booleanType))

  stoppableProperty(
    "a boolean's branch selects by its scrutinee, evaluates only the case selected, and reads only a boolean"
  ) { stopped =>
    for
      written <- elements.forAll
      sought <- value.forAll
      truthValue <- Gen.boolean.forAll
      first <- value.forAll
      second <- value.forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      def computed(program: Configured[NoFacts.type]) =
        compilation
          .compiled(compilation.blocks(program), DebugAttributes.Omitted, stop)
          .map(_.map(_.run(stop)))
      val occurrences = written.count(_._1 == sought)
      val noValue = closed(plus)(
        closed(NoFacts.parallel(list(written), listCriterion(true)))
      )(closed(zero))
      val programs = Vector(
        (
          program(
            fixpoint(count)(
              closed(NoFacts.parallel(list(written), listCriterion(true)))
            )(closed(numeral(sought)))
          ),
          Some(BigInteger.valueOf(occurrences.toLong))
        ),
        (
          program(
            selected(
              booleanLiteral(truthValue),
              closed(numeral(first)),
              closed(numeral(second))
            )
          ),
          Some(BigInteger.valueOf((if truthValue then first
                                   else second).toLong))
        ),
        (
          program(
            selected(
              booleanLiteral(truthValue),
              closed(numeral(first)),
              noValue
            )
          ),
          Option.when(truthValue)(BigInteger.valueOf(first.toLong))
        ),
        (
          program(
            selected(
              closed(numeral(sought)),
              closed(numeral(first)),
              closed(numeral(second))
            )
          ),
          None
        )
      )
      val equalityAlone = program(
        closed(equality)(closed(numeral(first)))(closed(numeral(second)))
      )
      Result
        .all(
          Result
            .assert(compilation.blocks(equalityAlone).isEmpty)
            .log(
              s"equality's call is a block: ${compilation.blocks(equalityAlone).size}"
            ) ::
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
          s"the list ${written.mkString(", ")}, sought $sought, $truthValue, $first, $second"
        )
  }
