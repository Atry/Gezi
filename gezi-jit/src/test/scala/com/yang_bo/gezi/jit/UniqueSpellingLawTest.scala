package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Value

/** The law of the specialized spelling's conversion
  * (`StorageEncoding.parallelOfValues`): whether a parallel is a storage is
  * read off its spelling, one layer. On every iteration, one term of each kind,
  * by construction:
  *
  *   - the unique spelling `C (f1 ∥ F1) … ∥ T`, every field a storage of its
  *     filter (a natural `successor^k zero`, a list of naturals), is the
  *     storage of that value;
  *   - a cell whose tail is written unfiltered, `cons (n ∥ N) t ∥ L` with t the
  *     plain `nil`, is no unique spelling and stays one layer of the IR, the
  *     parallel as written;
  *   - an open cell, its field a neutral value `cons (x ∥ N) nil ∥ L`, stays
  *     the parallel: a storage is of a closed term.
  *
  * That the conversion reads no field's view holds by its type: it takes no
  * `StorageAccess` (`NativeSpecializer.specialized`), which every view read
  * asks for (`NativeSpecializer.viewOf`).
  *
  * Its purpose is to catch a conversion that decides by more than the spelling
  * (a check of the premise, a walk below one layer), that converts a term
  * outside the unique spelling, or that makes a storage of an open term.
  */
class UniqueSpellingLawTest extends GeneratedProperties:

  given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => encoding,
      _ => zero,
      _ => successor,
      _ => natType,
      _ => nil,
      _ => cons,
      _ => listType
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

  private def naturals: JitValue[encoding.type] =
    JitValue.Apply(listType, natType)

  /** `successor^k zero`, each layer filtered by `nat_type` as it is built: the
    * unique spelling, layer by layer.
    */
  private def natural(value: Int): JitValue[encoding.type] =
    (1 to value).foldLeft(JitTesting.parallelOfValues(encoding)(zero, natType))(
      (inner, _) =>
        JitTesting
          .parallelOfValues(encoding)(JitValue.Apply(successor, inner), natType)
    )

  /** The list of the naturals, every cell in the unique spelling. */
  private def listOf(items: Vector[Int]): JitValue[encoding.type] =
    items.foldRight(JitTesting.parallelOfValues(encoding)(nil, naturals))(
      (item, rest) =>
        JitTesting.parallelOfValues(encoding)(
          JitValue.Apply(JitValue.Apply(cons, natural(item)), rest),
          naturals
        )
    )

  private def cell(
      item: JitValue[encoding.type],
      tail: JitValue[encoding.type]
  ): JitValue[encoding.type] =
    JitTesting.parallelOfValues(encoding)(
      JitValue.Apply(JitValue.Apply(cons, item), tail),
      naturals
    )

  private def stored(value: JitValue[encoding.type]): Boolean =
    com.yang_bo.gezi.ir.NativeStorage.stored(value.representation)

  /** One layer of the IR, a parallel: the term as written. */
  private def writtenParallel(value: JitValue[encoding.type]): Boolean =
    !stored(value) && (value.layer match
      case com.yang_bo.gezi.ir.Parallel(_, _) => true
      case _                      => false)

  property(
    "a parallel is a storage exactly when its one layer is the unique spelling"
  ) {
    for
      value <- Gen.int(Range.linear(0, 12)).forAll
      items <- Gen
        .int(Range.linear(0, 6))
        .list(Range.linear(0, 4))
        .map(_.toVector)
        .forAll
      variable <- Gen.int(Range.linear(0, 6)).forAll
    yield
      val natural = this.natural(value)
      val list = listOf(items)
      val unfilteredTail = cell(this.natural(value), nil)
      val open = cell(
        JitTesting.parallelOfValues(encoding)(
          JitValue.Neutral(com.yang_bo.gezi.weakhead.BoundVariable(variable), Vector.empty),
          natType
        ),
        JitTesting.parallelOfValues(encoding)(nil, naturals)
      )
      Result.all(
        List(
          Result
            .assert(
              Value.same(
                natural,
                JitTesting.valueOfNative(encoding)(
                  Representation.BigInteger,
                  NativeValue.Natural(value)
                )
              )
            )
            .log("a natural"),
          Result.assert(stored(list)).log(s"the list $items"),
          Result
            .assert(writtenParallel(unfilteredTail))
            .log(s"a cell with an unfiltered tail: $unfilteredTail"),
          Result.assert(writtenParallel(open)).log(s"an open cell: $open")
        )
      )
  }
