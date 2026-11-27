package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.weakhead.ListRepresentation

/** The laws of the conversion a configuration applies where it builds a
  * parallel (`StorageEncoding.parallel`), on generated naturals and lists of
  * the natives' library (`NativesTesting.nativesOn`) built through it. Its
  * purpose is to catch a conversion that gives a storage to a term not in the
  * unique spelling `C (f1 ∥ F1) … ∥ T` (a plain `successor zero ∥ nat_type`, a
  * cell whose tail is not filtered), that gives one term two objects, whose
  * storage's view is not the term it was converted from, or that leaves a
  * filter met twice uncollapsed.
  *
  * The expectations follow from #2163 B1 before the tests run: a natural n
  * built through the conversion layer by layer is the storage of n, whose
  * view's field is the object built one layer down; a list is the storage of
  * its first cell, its item as written (an item that converts, a natural in the
  * unique spelling, held as its storage) and its tail the storage of the rest;
  * anything else stays a parallel. Two cells whose views are equal are equal,
  * and a storage under the JIT's sharing cell converts as itself.
  */
class StorageConversionLawTest extends GeneratedProperties:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => encoding,
      _ => zero,
      _ => successor,
      _ => natType,
      _ => nil,
      _ => cons,
      _ => listType,
      _ => trueTerm,
      _ => falseTerm,
      _ => booleanType
    )

  private lazy val facts = BackendFacts.of(NativesTesting.nativesOn)
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private lazy val zero: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("zero"))
  private lazy val successor: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("successor"))
  private lazy val natType: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("nat_type"))
  private lazy val nil: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("nil"))
  private lazy val cons: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("cons"))
  private lazy val listType: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("list_type"))
  private lazy val trueTerm: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("true"))
  private lazy val falseTerm: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("false"))
  private lazy val booleanType: JitValue[encoding.type] =
    Value.of(JitTesting.libraryInstruction[encoding.type]("boolean_type"))

  private def natural(value: Int): JitValue[encoding.type] =
    (1 to value).foldLeft(JitTesting.parallelOfValues(encoding)(zero, natType))(
      (inner, _) =>
        JitTesting
          .parallelOfValues(encoding)(JitValue.Apply(successor, inner), natType)
    )

  /** The plain spelling `successor^value zero`, no filter inside. */
  private def plainNatural(value: Int): JitValue[encoding.type] =
    (1 to value).foldLeft(zero)((inner, _) => JitValue.Apply(successor, inner))

  private def naturals: JitValue[encoding.type] =
    JitValue.Apply(listType, natType)

  /** The list of the items in the unique spelling, built through the
    * conversion: `cons (i ∥ nat_type) rest ∥ list_type nat_type` over
    * `nil ∥ list_type nat_type`.
    */
  private def listOf(
      items: Vector[JitValue[encoding.type]]
  ): JitValue[encoding.type] =
    items.foldRight(JitTesting.parallelOfValues(encoding)(nil, naturals))(
      (item, rest) =>
        JitTesting.parallelOfValues(encoding)(
          JitValue.Apply(
            JitValue.Apply(
              cons,
              JitTesting.parallelOfValues(encoding)(item, natType)
            ),
            rest
          ),
          naturals
        )
    )

  /** An item: a natural in the unique spelling, a plain natural (an unevaluated
    * term to the conversion), or successor itself (a function).
    */
  private val item: Gen[JitValue[encoding.type]] = Gen.choice1(
    Gen.int(Range.linear(0, 20)).map(natural),
    Gen.int(Range.linear(1, 20)).map(plainNatural),
    Gen.constant(successor)
  )

  property(
    "a natural in the unique spelling is its storage, one object, its view the term it was built from"
  ) {
    for value <- Gen.int(Range.linear(0, 200)).forAll
    yield
      val built = natural(value)
      built match
        case JitValue.Stored(storage) =>
          val view =
            encoding.viewOf(storage)(using com.yang_bo.gezi.ir.StorageAccess.granted())
          val spelled = Value.of(view.value)
          val viewField = spelled match
            case JitValue.Apply(function, field)
                if Value.same(function, successor) =>
              Some(field)
            case _ => None
          Result.all(
            List(
              Result.diff(storage.value, NativeValue.Natural(BigInt(value)))(
                _ == _
              ),
              Result
                .assert(Value.same(natural(value), built))
                .log("built again, another object"),
              Result
                .assert(Value.same(Value.of(view.criterion), natType))
                .log("the view's criterion"),
              Result
                .assert(if value == 0 then Value.same(spelled, zero)
                else viewField.exists(Value.same(_, natural(value - 1))))
                .log("the view's field is not the object built one layer down"),
              Result
                .assert(
                  Value.same(
                    JitTesting.parallelOfValues(encoding)(
                      spelled,
                      Value.of(view.criterion)
                    ),
                    built
                  )
                )
                .log("the view converted again is another object")
            )
          )
        case other => Result.failure.log(s"no storage: $other")
  }

  property(
    "a plain spelling, or a field filtered by no criterion, keeps no storage"
  ) {
    for value <- Gen.int(Range.linear(1, 50)).forAll
    yield
      val plain =
        JitTesting.parallelOfValues(encoding)(plainNatural(value), natType)
      val unfilteredTail = JitTesting.parallelOfValues(encoding)(
        JitValue.Apply(JitValue.Apply(cons, natural(1)), nil),
        naturals
      )
      Result.all(
        List(
          Result
            .assert(JitValue.Stored.unapply(plain).isEmpty)
            .log("successor^n zero ∥ nat_type got a storage"),
          Result
            .assert(JitValue.Stored.unapply(unfilteredTail).isEmpty)
            .log("cons h nil ∥ list_type nat_type got a storage")
        )
      )
  }

  property(
    "a list in the unique spelling is its storage, one cell over the rest, one object"
  ) {
    for items <- item.list(Range.linear(0, 8)).forAll
    yield
      val built = listOf(items.toVector)
      built match
        case JitValue.Stored(storage) =>
          Result.all(
            List(
              Result
                .diff(
                  storage.value,
                  items match
                    case Nil =>
                      NativeValue.Listed(
                        ListRepresentation.Items(0, Vector.empty)
                      )
                    case first :: rest =>
                      NativeValue.Listed(
                        ListRepresentation.Cell(first, listOf(rest.toVector))
                      )
                )(_ == _)
                .log("one cell over the storage of the rest"),
              Result
                .assert(Value.same(listOf(items.toVector), built))
                .log("built again, another object")
            )
          )
        case other => Result.failure.log(s"no storage: $other")
  }

  property(
    "a filter met twice is collapsed: s ∥ F is s for a storage s whose criterion is F"
  ) {
    for value <- Gen.int(Range.linear(0, 50)).forAll
    yield
      val built = natural(value)
      Result.all(
        List(
          Result.assert(
            Value.same(
              JitTesting.parallelOfValues(encoding)(built, natType),
              built
            )
          ),
          Result.assert(
            Value.same(
              JitTesting
                .parallelOfValues(encoding)(listOf(Vector(built)), naturals),
              listOf(Vector(built))
            )
          )
        )
      )
  }

  /** Whether the two storages' views are one term: a view is a parallel of
    * interned terms made as it is, not interned (`Parallel.apply`), so it is
    * compared by its sides' identities.
    */
  private def sameView(
      first: RepresentedStorage[JitValue[encoding.type]],
      second: RepresentedStorage[JitValue[encoding.type]]
  ): Boolean =
    val access = com.yang_bo.gezi.ir.StorageAccess.granted()
    val (firstView, secondView) = (
      encoding.viewOf(first)(using access),
      encoding.viewOf(second)(using access)
    )
    Configured.same(firstView.value, secondView.value) && Configured.same(
      firstView.criterion,
      secondView.criterion
    )

  property(
    "two cells are equal exactly when their views are: an item that converts is held as its storage"
  ) {
    for value <- Gen.int(Range.linear(0, 30)).forAll
    yield
      val tail = listOf(Vector.empty)
      val representation = Representation.ListOf(natType)
      val spelledItem = JitTesting.storageOf(encoding)(
        representation,
        NativeValue.Listed(
          ListRepresentation.Cell(
            JitValue.Apply(successor, natural(value)),
            tail
          )
        )
      )
      val storedItem = JitTesting.storageOf(encoding)(
        representation,
        NativeValue.Listed(ListRepresentation.Cell(natural(value + 1), tail))
      )
      Result.all(
        List(
          Result
            .assert(sameView(spelledItem, storedItem))
            .log("the two views differ"),
          Result
            .assert(
              spelledItem == storedItem && spelledItem.## == storedItem.##
            )
            .log("equal views, unequal storages")
        )
      )
  }

  property(
    "a storage under the JIT's sharing cell converts as the storage: a typed body instantiated with a shared value"
  ) {
    for value <- Gen.int(Range.linear(0, 30)).forAll
    yield
      val shared = JitValue.Thunk[encoding.type](
        JitRules.cellCode,
        Vector.empty,
        Vector(natural(value))
      )
      Result.all(
        List(
          Result
            .assert(
              Value.same(
                JitTesting.parallelOfValues(encoding)(shared, natType),
                natural(value)
              )
            )
            .log("s ∥ F under a cell kept the parallel"),
          Result
            .assert(
              Value.same(
                JitTesting.parallelOfValues(encoding)(
                  JitValue.Apply(
                    successor,
                    JitTesting.parallelOfValues(encoding)(shared, natType)
                  ),
                  natType
                ),
                natural(value + 1)
              )
            )
            .log("successor (cell ∥ nat_type) ∥ nat_type is no storage")
        )
      )
  }

  // Whether a list's cell is in the unique spelling is read off its tail node, one layer: each cell's tail is drawn
  // as the storage below it as it is, that storage filtered by the list's criterion (which the configuration's
  // parallel makes the storage itself), or a term written with no filter (a plain natural, as cons's native in head
  // position holds a tail). Its purpose is to catch a storage that claims a filtered tail it does not have, which a
  // decode point would trust. Derived: a tail that is the list's storage holds as a tail, an unfiltered term does not.
  property(
    "a list's cell is in the unique spelling exactly when its tail is the list's storage"
  ) {
    for tails <- Gen.int(Range.linear(0, 2)).list(Range.linear(1, 6)).forAll
    yield
      val representation = Representation.ListOf(natType)
      val (_, results) = tails.foldLeft(
        (
          JitTesting.parallelOfValues(encoding)(nil, naturals),
          Vector.empty[Result]
        )
      ) { case ((below, found), kind) =>
        val (node, expected) = kind match
          case 0 => (below, true)
          case 1 =>
            (JitTesting.parallelOfValues(encoding)(below, naturals), true)
          case _ => (plainNatural(1), false)
        val value =
          NativeValue.Listed(ListRepresentation.Cell(natural(0), node))
        val cell = JitTesting.interned(encoding)(
          JitTesting.storageOf(encoding)(representation, value)
        )
        (
          cell,
          found :+ Result
            .diff(
              encoding.operations.uniquelySpelled(representation, value),
              expected
            )(_ == _)
            .log(s"$tails, tail kind $kind")
        )
      }
      Result.all(results.toList)
  }

  property("a boolean in the unique spelling is its storage") {
    for truth <- Gen.boolean.forAll
    yield
      val term = if truth then trueTerm else falseTerm
      Result.assert(
        Value.same(
          JitTesting.parallelOfValues(encoding)(term, booleanType),
          JitTesting.valueOfNative(encoding)(
            Representation.Truth,
            NativeValue.Truth(truth)
          )
        )
      )
  }
