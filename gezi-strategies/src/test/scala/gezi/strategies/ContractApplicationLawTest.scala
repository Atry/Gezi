package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.standardlibrary.StandardLibraryIndex

/** The law of `specialization_attraction`'s contracts: a closure whose body
  * filters, applied to as many arguments as it has holes, counts as its body
  * with the arguments in their holes, and reads as the body does
  * (`SpecializationAttraction`, `HoleUse`). Its purpose is to catch a contract
  * application that counts a filtered hole's argument as an unfiltered
  * application, or an unfiltered one as filtered, or an argument once where the
  * body uses it twice or not at all.
  *
  * The closures are generated with one to three holes, each used in the body
  * zero, one or more times as an argument of an opaque head, filtered (`y ∥ c`)
  * or not (`y`), the body under a range `∥ c` or the argument of a two-hole
  * contract, so that the closure takes one argument more than its holes (a
  * curried function's typed member `λx. C (F (x ∥ D))`); and, in some, the
  * first hole at the head, the body's `f (…)`. The arguments are names,
  * applications, filters and a one-hole contract; the argument of a hole at the
  * head is drawn among those that read as no marker and no contract (the FIXME
  * at `SpecializationAttraction.holeUses`).
  */
class ContractApplicationLawTest extends GeneratedProperties:

  private val reading = TermReading(
    StandardLibraryIndex(
      NoFacts,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector.empty
    )
  )

  private val head = OrderTerm.Name(NoFacts.opaque("contract-application-head"))
  private val criterion =
    OrderTerm.Name(NoFacts.opaque("contract-application-criterion"))
  private val other =
    OrderTerm.Name(NoFacts.opaque("contract-application-other"))

  /** One occurrence of a hole in the body: the hole and whether it is filtered
    * there.
    */
  private final case class Occurrence(hole: Int, filtered: Boolean)

  /** A closure's shape: its holes, whether the first stands at the head, its
    * occurrences, and whether its body is under the range `∥ c` or is the
    * contract `outerContract` applied to it, a contract with one hole left,
    * which one more argument fills.
    */
  private final case class Contract(
      holeCount: Int,
      holeAtHead: Boolean,
      occurrences: Vector[Occurrence],
      underContract: Boolean
  ):
    def argumentCount: Int = if underContract then holeCount + 1 else holeCount

  private val contract: Gen[Contract] =
    for
      holeCount <- Gen.int(Range.linear(1, 3))
      holeAtHead <- Gen.boolean
      occurrences <- (for
        hole <- Gen.int(Range.linear(0, holeCount - 1)); filtered <- Gen.boolean
      yield Occurrence(hole, filtered))
        .list(Range.linear(0, 5))
      underContract <- Gen.boolean
    yield Contract(holeCount, holeAtHead, occurrences.toVector, underContract)

  /** `λf y. f (y ∥ c) ∥ c`, a contract of two holes, the second filtered. */
  private val outerContract = OrderTerm.Thunk(
    Code.Parallel(
      Code.Apply(Code.Slot(0), Code.Parallel(Code.Slot(1), Code.Slot(2))),
      Code.Slot(2)
    ),
    Vector(Hole.Bound(0), Hole.Bound(1)),
    Vector(criterion)
  )

  /** Arguments that read as no marker and no contract: a name, an application,
    * a filter, an application to a filter.
    */
  private val plainArgument: Gen[OrderTerm[NoFacts.type]] = Gen.element1(
    other,
    OrderTerm.Apply(other, other),
    OrderTerm.Parallel(other, criterion, false),
    OrderTerm.Apply(other, OrderTerm.Parallel(other, criterion, false))
  )

  /** Every argument: the plain ones and the one-hole contract `λx. x ∥ c`. */
  private val anyArgument: Gen[OrderTerm[NoFacts.type]] = Gen.frequency1(
    4 -> plainArgument,
    1 -> Gen.constant(
      OrderTerm.Thunk(
        Code.Parallel(Code.Slot(0), Code.Slot(1)),
        Vector(Hole.Bound(0)),
        Vector(criterion)
      )
    )
  )

  /** The body over the terms that stand in the holes, the head, the criterion
    * and the outer contract, built by `apply` and `parallel` alike for the code
    * and for the substituted term.
    */
  private def body[Term](
      shape: Contract,
      hole: Int => Term,
      headTerm: Term,
      criterionTerm: Term,
      outerContractTerm: Term,
      apply: (Term, Term) => Term,
      parallel: (Term, Term) => Term
  ): Term =
    val start = if shape.holeAtHead then hole(0) else headTerm
    val applied = shape.occurrences.foldLeft(start)((function, occurrence) =>
      val standing = hole(occurrence.hole)
      apply(
        function,
        if occurrence.filtered then parallel(standing, criterionTerm)
        else standing
      )
    )
    if shape.underContract then apply(outerContractTerm, applied)
    else parallel(applied, criterionTerm)

  private def stateOf(
      term: OrderTerm[NoFacts.type]
  ): SpecializationState[NoFacts.type] =
    TermOrder.ownState[SpecializationState[NoFacts.type]](
      SpecializationAttraction.folded(term, reading)
    )

  property(
    "aContractAppliedToItsArgumentsCountsAsItsBodyWithTheArgumentsInItsHoles"
  ) {
    for
      shape <- contract.forAll
      first <- (if shape.holeAtHead then plainArgument else anyArgument).forAll
      rest <- anyArgument.list(Range.singleton(shape.argumentCount - 1)).forAll
    yield
      val arguments = first +: rest.toVector
      val code = body[Code](
        shape,
        Code.Slot(_),
        Code.Slot(shape.holeCount),
        Code.Slot(shape.holeCount + 1),
        Code.Slot(shape.holeCount + 2),
        Code.Apply(_, _),
        Code.Parallel(_, _)
      )
      val closure = OrderTerm.Thunk(
        code,
        Vector.tabulate(shape.holeCount)(Hole.Bound(_)),
        Vector(head, criterion, outerContract)
      )
      val applied = arguments.foldLeft[OrderTerm[NoFacts.type]](closure)(
        OrderTerm.Apply(_, _)
      )
      val substitutedBody =
        body[OrderTerm[NoFacts.type]](
          shape,
          arguments,
          head,
          criterion,
          outerContract,
          OrderTerm.Apply(_, _),
          OrderTerm.Parallel(_, _, false)
        )
      val substituted = arguments
        .drop(shape.holeCount)
        .foldLeft(substitutedBody)(OrderTerm.Apply(_, _))
      val appliedState = stateOf(applied)
      val substitutedState = stateOf(substituted)
      Result
        .assert(appliedState.count == substitutedState.count)
        .and(
          Result.assert(
            appliedState.unfilteredLefts == substitutedState.unfilteredLefts
          )
        )
        .and(Result.assert(appliedState.root == substitutedState.root))
        .log(s"closure $closure")
        .log(s"arguments $arguments")
        .log(s"applied $appliedState, substituted $substitutedState")
  }

  /** The typed member's specialization choice `λx. f x + (f (x ∥ D) ∥ R)`, the
    * code's dispatch pattern over the untyped f, the head.
    */
  private val typedHead = OrderTerm.Thunk(
    Code.Choice(
      Code.Apply(Code.Slot(1), Code.Slot(0)),
      Code.Parallel(
        Code.Apply(Code.Slot(1), Code.Parallel(Code.Slot(0), Code.Slot(2))),
        Code.Slot(3)
      )
    ),
    Vector(Hole.Bound(0)),
    Vector(head, criterion, criterion)
  )

  /** The closure `λy. c1 (c2 (… (cn y)))` of the members. */
  private def chain(
      members: Vector[OrderTerm[NoFacts.type]]
  ): OrderTerm[NoFacts.type] =
    val code = members.indices.foldRight[Code](Code.Slot(members.size))(
      (position, inner) => Code.Apply(Code.Slot(position), inner)
    )
    OrderTerm.Thunk(code, Vector(Hole.Bound(members.size)), members)

  /** Its purpose is to catch a typed member's range priced as a filter over an
    * unchecked value: the chain of n typed members then costs as much as one
    * where some members are untyped, each untyped member dropping a range and
    * leaving the next typed member's domain unfiltered, and the extraction
    * takes the smaller spelling, which runs no native
    * (aClosuresNaturalsRunCostsASuccessorDoNotGrow, 2026-11-13). Of the
    * closures of n typed members, n from 1 to 6, and of the same n members with
    * at least one untyped, applied to a name or to a filtered name, the
    * all-typed one is strictly better.
    */
  property("aChainOfTypedMembersIsBetterThanEveryAlternationWithUntypedOnes") {
    for
      size <- Gen.int(Range.linear(1, 6)).forAll
      untypedPosition <- Gen.int(Range.linear(0, size - 1)).forAll
      typed <- Gen.boolean.list(Range.singleton(size)).forAll
      argument <- Gen
        .element1(other, OrderTerm.Parallel(other, criterion, false))
        .forAll
    yield
      val alternation = typed.toVector
        .updated(untypedPosition, false)
        .map(isTyped => if isTyped then typedHead else head)
      val allTyped =
        OrderTerm.Apply(chain(Vector.fill(size)(typedHead)), argument)
      val alternated = OrderTerm.Apply(chain(alternation), argument)
      val allTypedValue = SpecializationAttraction.value(
        SpecializationAttraction.folded(allTyped, reading)
      )
      val alternatedValue = SpecializationAttraction.value(
        SpecializationAttraction.folded(alternated, reading)
      )
      Result
        .assert(OrderValue.ordering.compare(allTypedValue, alternatedValue) < 0)
        .log(
          s"all typed ${stateOf(allTyped)}, alternated ${stateOf(alternated)}"
        )
        .log(s"alternation $alternation, argument $argument")
  }
