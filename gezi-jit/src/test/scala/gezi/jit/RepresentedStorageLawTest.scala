package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.Value
import gezi.standardlibrary.LibraryFiles
import gezi.weakhead.ListRepresentation

/** The laws of the JIT's native storages (`RepresentedStorage`) on generated
  * values of the natives' library (`NativesTesting.nativesOn`): naturals,
  * booleans, and lists of library terms held as items. Its purpose is to catch
  * an equality that is not an equivalence, that depends on which facts object
  * of one library built the storage, or that tells apart one value's storages
  * built by two entries' encodings (interning reads no configuration), a hash
  * code that does not agree with it, and a hash code that walks a natural's
  * view instead of computing it from the value.
  */
class RepresentedStorageLawTest extends GeneratedProperties:

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => encoding, _ => otherEncoding, _ => otherLibraryEncoding)

  /** The encoding of the natives' library. */
  private lazy val encoding: StorageEncoding =
    NativesTesting.encodingOf(NativesTesting.nativesOn)

  /** The encoding of the facts of the same library built again: another object.
    */
  private lazy val otherEncoding: StorageEncoding =
    NativesTesting.encodingOf(NativesTesting.nativesOn)

  /** The encoding of another library, the binary naturals' backend: another
    * encoding, which names the naturals' family as the natives' library may.
    */
  private lazy val otherLibraryEncoding: StorageEncoding =
    NativesTesting.encodingOf(
      LibraryFiles.compiled(
        "tests/library_fixtures/binary_natural_backend.lambdalattice",
        Vector(BackendChecks)
      )
    )

  /** The library terms a list holds as its items. */
  private val itemKeys: Vector[String] =
    Vector("zero", "successor", "true", "nil")

  /** A value of a representation, written independently of any configuration: a
    * natural, a boolean or a list of library terms, by the indices of
    * `itemKeys`.
    */
  private enum Spec:
    case Natural(value: Int)
    case Truth(value: Boolean)
    case Listed(indices: List[Int])

  /** The storage of the spec under the encoding. */
  private def stored[E <: StorageEncoding & Singleton](encoding: E)(
      spec: Spec
  ): RepresentedStorage[JitValue[E]] =
    given E = encoding
    spec match
      case Spec.Natural(value) =>
        JitTesting.storageOf(encoding)(
          Representation.BigInteger,
          NativeValue.Natural(BigInt(value))
        )
      case Spec.Truth(value) =>
        JitTesting.storageOf(encoding)(
          Representation.Truth,
          NativeValue.Truth(value)
        )
      case Spec.Listed(indices) =>
        val natType = Value.of(JitTesting.libraryInstruction[E]("nat_type"))
        val held = indices.toVector.map(index =>
          Value.of(
            JitTesting.libraryInstruction[E](itemKeys(index % itemKeys.size))
          )
        )
        JitTesting.storageOf(encoding)(
          Representation.ListOf(natType),
          NativeValue.Listed(ListRepresentation.Items(held.size, held))
        )

  /** A value of a representation: a natural, a boolean or a list of items. */
  private val represented: Gen[Spec] =
    Gen.choice1(
      Gen.int(Range.linear(0, 300)).map(Spec.Natural(_)),
      Gen.boolean.map(Spec.Truth(_)),
      Gen
        .int(Range.linear(0, 1000))
        .list(Range.linear(0, 6))
        .map(Spec.Listed(_))
    )

  property(
    "storages of one value are equal whichever facts of one library built them, and of two values are not"
  ) {
    for
      spec <- represented.forAll
      otherSpec <- represented.forAll
    yield
      val storage = stored(encoding)(spec)
      val again = stored(otherEncoding)(spec)
      val other = stored(encoding)(otherSpec)
      // A view is a parallel of interned terms made as it is, not interned (`Parallel.apply`): compared by its sides.
      val access = gezi.ir.StorageAccess.granted()
      val (storageView, otherView) = (
        encoding.viewOf(storage)(using access),
        encoding.viewOf(other)(using access)
      )
      val sameTerm = Configured.same(
        storageView.value,
        otherView.value
      ) && Configured.same(storageView.criterion, otherView.criterion)
      Result.all(
        List(
          // Interned when made: one object, and outside the pool hashed by its identity.
          Result
            .assert(
              (storage eq again) && storage.## == System.identityHashCode(
                storage
              )
            )
            .log("one value, two facts"),
          Result
            .assert(
              (storage == other) == sameTerm && (other == storage) == sameTerm
            )
            .log(s"$storage and $other")
        )
      )
  }

  property(
    "storages of one value built by two entries' encodings are one object"
  ) {
    for natural <- Gen.int(Range.linear(0, 300)).forAll
    yield
      val first = stored(encoding)(Spec.Natural(natural))
      val second = stored(otherLibraryEncoding)(Spec.Natural(natural))
      Result
        .assert(first eq second)
        .log(
          "a storage's content is its representation and its native data, no encoding"
        )
  }

  property(
    "a natural near 2^60 is stored, its hash code computed without its view"
  ) {
    for offset <- Gen.long(Range.linear(0L, 1000L)).forAll
    yield
      val large = BigInt(2).pow(60) + offset
      val storage = JitTesting.storageOf(encoding)(
        Representation.BigInteger,
        NativeValue.Natural(large)
      )
      val next = JitTesting.storageOf(encoding)(
        Representation.BigInteger,
        NativeValue.Natural(large + 1)
      )
      Result.assert(storage != next)
  }

  /** #2163, the verification table's row 3b: one value's storage built in eight
    * threads at once is one object, since a storage is interned when it is made
    * and the pool keeps one object of one content under concurrent interning.
    * Its purpose is to catch a construction that hands out a storage before
    * interning it, or a pool that keeps two under a race.
    */
  property("one value's storage built in parallel threads is one object") {
    for spec <- represented.forAll
    yield
      given scala.concurrent.ExecutionContext =
        scala.concurrent.ExecutionContext.global
      val built = scala.concurrent.Await.result(
        scala.concurrent.Future.sequence(
          Vector.fill(8)(scala.concurrent.Future(stored(encoding)(spec)))
        ),
        scala.concurrent.duration.Duration(10, "s")
      )
      Result
        .assert(built.sliding(2).forall {
          case Vector(first, second) => first eq second
          case _                     => true
        })
        .log(s"$spec")
  }
