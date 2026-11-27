package gezi.contest.entries.solo

import java.nio.file.Paths

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result

import gezi.contest.natives.solo.SoloBinaryOperations
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTables
import gezi.weakhead.Computed
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import gezi.weakhead.NormalForms
import gezi.weakhead.ReadingState

private given binaryTimesNativeLawTestNoFacts: NoFacts.type = NoFacts

/** The law of the native `solo_binary_times` against the library term it is
  * bound to: the reading of `merge_binary_times a b` under tabling(weak_head),
  * the term as written, has one normal form, the canonical binary natural of
  * the native's product of a and b. Its purpose is to catch a native whose
  * value is not the term's, at a zero or a one operand, where the term's
  * recursion ends at once, and on operands of many bits.
  */
class BinaryTimesNativeLawTest extends GeneratedProperties:

  /** The steps a reading of one product may take: the term multiplies bit by
    * bit, so a product of two naturals of 24 bits stays far below it.
    */
  private val readingLimit: Long = 5_000_000L

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        Paths.get(sys.props("gezi.buildRoot")),
        TermTables.codecTerms,
        Expansions.none
      )
      ._1

  private def term(key: String): Term = Term.closed(
    terms.getOrElse(
      key,
      throw IllegalArgumentException(s"no fixture member $key")
    )
  )

  /** The value as the library's constructors spell it. */
  private def natural(value: BigInt): Term =
    if value == 0 then term("binary_zero")
    else if value % 2 == 0 then term("binary_even")(natural(value / 2))
    else term("binary_odd")(natural(value / 2))

  /** The canonical binary natural's normal form: zero is λz e o. z, and an even
    * or odd value applies its second or third binder to its half.
    */
  private def normalForm(value: BigInt): Configured[NoFacts.type] =
    def form(remaining: BigInt): Term =
      if remaining == 0 then Term.λ(zero => Term.λ(_ => Term.λ(_ => zero)))
      else
        val half = form(remaining / 2)
        if remaining % 2 == 0 then
          Term.λ(_ => Term.λ(even => Term.λ(_ => even(half))))
        else Term.λ(_ => Term.λ(_ => Term.λ(odd => odd(half))))
    Defunctionalization.thunkInstruction(form(value).deBruijnTerm(Map.empty))(
      using gezi.ir.NoFacts
    )

  private val operand: Gen[BigInt] =
    Gen.frequency1(
      1 -> Gen.element1(BigInt(0), BigInt(1)),
      4 -> Gen.long(Range.linear(2L, (1L << 24) - 1L)).map(BigInt(_))
    )

  property("the term's one normal form is the native's product") {
    for
      left <- operand.forAll
      right <- operand.forAll
    yield
      val program = Defunctionalization.thunkInstruction(
        term("merge_binary_times")(natural(left))(natural(right))
          .deBruijnTerm(Map.empty)
      )(using gezi.ir.NoFacts)
      val product =
        BigInt(SoloBinaryOperations.times(left.bigInteger, right.bigInteger))
      NormalForms
        .normalForms(Mode.TablingWeakHead, program)
        .result(
          ReadingState.fresh(
            readingLimit,
            gezi.weakhead.ReadingConfiguration.withoutFacts
          )
        ) match
        case Computed.Done(normalForms, _) =>
          Result.diff(normalForms, Vector(normalForm(product)))(_ == _)
        case Computed.Stopped(after) =>
          Result.failure.log(
            s"the reading stopped after ${after.budget.spent} steps"
          )
  }
