package gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BinaryNaturalNatives
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.narrowblocks.lists.NarrowListLibrary
import gezi.saturation.StopSignal
import gezi.standardlibrary.NativeBound

private given groupPositivePlaceLawTestNoFacts: NoFacts.type = NoFacts

/** The static method of the law's native, whose divisor's place is one of
  * positive naturals. Public, since a block calls it by its name. It throws on
  * a divisor of 0, which is how a call the place does not license shows.
  */
object GroupPositiveQuotient:
  def quotient(dividend: BigInteger, divisor: BigInteger): BigInteger =
    dividend.divide(divisor)

/** The law's native as a block calls it; the law never runs it on an argument
  * vector.
  */
private object GroupPositiveQuotientMethod
    extends (Vector[NativeArgument] => NativeValue),
      StaticBlockMethod:
  val className: String =
    classOf[GroupPositiveQuotient.type].getName.stripSuffix("$")
  val methodName: String = "quotient"
  def apply(arguments: Vector[NativeArgument]): NativeValue =
    Native.outsidePlaces("group_positive_quotient", arguments)

/** The laws of a native's place of positive naturals in a group block, over the
  * narrow lists' test library extended with a quotient native whose divisor's
  * place names the positive naturals. N is the naturals' criterion
  * `binary_set true`, P the positive naturals' `binary_set false`. Derived from
  * the group grammar's guarantees: a block's parameter is read only under a
  * filter, and a native's place of positive naturals takes only an operand
  * filtered by P, or a constant of the positive representation, and no computed
  * value, the filter written in the term licensing the place:
  *
  *   - `λa b. quotient (a ∥ N) (b ∥ P)` compiles; P rejects a divisor 0 before
  *     the call, which stops the block (the rejected term's context can have an
  *     answer), so on groups of positive divisors it gives the quotients of
  *     every dividend by every divisor, each once, and with a divisor 0 it
  *     gives no value;
  *   - `λa b. quotient (a ∥ N) (b ∥ N)`, the divisor filtered by N, which
  *     admits 0, compiles no block;
  *   - `λa b. quotient a b`, parameters outside a filter, compiles no block;
  *   - `λa c. (λy. quotient (a ∥ N) y) (plus (a ∥ N) (c ∥ N))` binds y by a let
  *     to a computed value, which may be 0, so it does not compile, while the
  *     same let with `plus` in place of `quotient` does.
  *
  * Their purpose is to catch a positive place that takes a natural which may be
  * 0, a parameter decoded in no filter's representation, and a let's binder
  * taken for a licensed operand.
  */
class GroupPositivePlaceLawTest extends GeneratedProperties:

  /** λx y. y (x y) x, bound to the quotient native. */
  private val quotient: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(
        Code.Apply(Code.Slot(1), Code.Apply(Code.Slot(0), Code.Slot(1))),
        Code.Slot(0)
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector.empty
    )

  private val index = NarrowListLibrary.compilation.index.copy(nativeBound =
    NarrowListLibrary.compilation.index.nativeBound :+ NativeBound(
      Pure.required(quotient),
      "group_positive_quotient"
    )
  )

  private val natives: NativeBackend =
    NarrowListLibrary.compilation.natives.extended(
      NativeBackend.functions(
        Map(
          "group_positive_quotient" -> Native(
            Vector(
              NativePlace.Fixed(BinaryNaturalNatives.canonical),
              NativePlace.Fixed(BinaryNaturalNatives.positive)
            ),
            NativePlace.Fixed(BinaryNaturalNatives.canonical),
            GroupPositiveQuotientMethod
          )
        ),
        Vector.empty
      )
    )

  private val compilation = GroupCompilation(
    gezi.jit.BackendFacts(index, natives)
  )

  private val naturals: Configured[NoFacts.type] =
    NoFacts.application(NarrowListLibrary.binarySet, NarrowListLibrary.truth)

  private val positives: Configured[NoFacts.type] =
    NoFacts.application(NarrowListLibrary.binarySet, NarrowListLibrary.falsity)

  /** `λa b. quotient (a ∥ N) (b ∥ D)`: a at slot 0, b at slot 1, quotient at
    * slot 2, N at slot 3, D, the divisor's filter, at slot 4.
    */
  private def divided(
      divisorFilter: Configured[NoFacts.type]
  ): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(
        Code.Apply(Code.Slot(2), Code.Parallel(Code.Slot(0), Code.Slot(3))),
        Code.Parallel(Code.Slot(1), Code.Slot(4))
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(quotient, naturals, divisorFilter)
    )

  /** `λa b. quotient a b`: a at slot 0, b at slot 1, quotient at slot 2. */
  private val dividedBare: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(2), Code.Slot(0)), Code.Slot(1)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(quotient)
    )

  /** `λa c. (λy. f (a ∥ N) y) (plus (a ∥ N) (c ∥ N))`: a at slot 0, c at slot
    * 1, f at slot 2, plus at slot 3, N at slot 4; in the inner thunk y at slot
    * 0, f at slot 1, a at slot 2 and N at slot 3.
    */
  private def withComputed(
      function: Configured[NoFacts.type]
  ): Configured[NoFacts.type] =
    val inner = Code.Thunk(
      Code.Apply(
        Code.Apply(Code.Slot(1), Code.Parallel(Code.Slot(2), Code.Slot(3))),
        Code.Slot(0)
      ),
      Vector(Hole.Bound(0)),
      Vector(Code.Slot(2), Code.Slot(0), Code.Slot(4))
    )
    NoFacts.thunkOrInstance(
      Code.Apply(
        inner,
        Code.Apply(
          Code.Apply(Code.Slot(3), Code.Parallel(Code.Slot(0), Code.Slot(4))),
          Code.Parallel(Code.Slot(1), Code.Slot(4))
        )
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(function, NarrowListLibrary.plus, naturals)
    )

  private val group: Gen[Vector[(Representation, BigInteger)]] =
    Gen
      .int(Range.linear(0, 30))
      .list(Range.linear(1, 4))
      .map(
        _.distinct.toVector.map(value =>
          (BinaryNaturalNatives.canonical, BigInteger.valueOf(value.toLong))
        )
      )

  test("the places the term's filters do not license compile no block") {
    assertEquals(
      (
        compilation.compiled(divided(positives)).isDefined,
        compilation.compiled(divided(naturals)).isDefined,
        compilation.compiled(dividedBare).isDefined,
        compilation.compiled(withComputed(quotient)).isDefined,
        compilation.compiled(withComputed(NarrowListLibrary.plus)).isDefined
      ),
      (true, false, false, false, true)
    )
  }

  stoppableProperty(
    "the positive filter rejects a divisor 0, which stops the block; else every quotient once"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      dividends <- group.forAll
      divisors <- group.forAll
    yield
      val block = compilation
        .compiled(divided(positives))
        .getOrElse(throw IllegalStateException("the block compiles"))
      def quotients = (for
        (_, dividend) <- dividends
        (_, divisor) <- divisors
      yield dividend.divide(divisor)).distinct.sorted
      Result.diff(
        GroupRun
          .run(
            block,
            Vector(dividends, divisors)
              .map(_.map((_, value) => GroupValue.Natural(value))),
            ScalarGroupBackend,
            1000000L,
            stop
          )
          .results,
        Option.when(divisors.forall((_, divisor) => divisor.signum > 0))(
          quotients.map(GroupValue.Natural(_))
        )
      )(_ == _)
  }
