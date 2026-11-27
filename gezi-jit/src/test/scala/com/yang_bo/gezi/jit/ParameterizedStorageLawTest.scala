package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.standardlibrary.LibraryFiles

/** The laws of the conversion of a family with a finite value parameter, the
  * binary naturals under `binary_set P`
  * (`StorageEncoding.parameterizedRepresentations`, the members the backend's
  * facts declare, `DataFamily.excluded`), over the library of
  * tests/library_fixtures/binary_natural_backend.lambdalattice, the criteria
  * spelled with the library's own `binary_set`, `true` and `false` as a program
  * writes them. The expectations are read by hand from the expansion
  * `binary_set p = binary_odd (binary_set true) + binary_even (binary_set
  * false) + p binary_zero top` (corpora/library/binary/natural.lambdalattice):
  * odd's field is read at true, even's at false, and zero is a member at true
  * only.
  *
  *   - A natural n spelled bottom-up in the unique spelling through the
  *     converting construction (`StorageEncoding.parallel`) at P is a storage
  *     exactly when P is true or n > 0; its value is n, its view one layer of
  *     the constructor's define over the field's storage (that very object) and
  *     the criterion (that very term); and it is the object a native's result
  *     of value n at P is.
  *   - Near misses stay parallels: even's field filtered by `binary_set true`,
  *     a field with no filter, `binary_even (binary_zero ∥ binary_set false) ∥
  *     binary_set true`, and the criterion spelled through a fallback point,
  *     `binary_set (true + (true ∥ boolean_type))`.
  *   - The premise per constructor: at false odd and even are members and zero
  *     is not; at true all three; and the non-members are exactly the
  *     constructors the backend's facts exclude.
  *
  * Their purpose is to catch a conversion that misses a layer of the positive
  * naturals (every even number), converts a spelling other than the unique one
  * (two objects for one term, or a storage whose view is another term), or
  * converts a constructor its criterion does not hold, and a premise that
  * disagrees with the backend's exclusions on the library's facts (which
  * `StorageReadingOfFacts.callable` refuses).
  */
class ParameterizedStorageLawTest extends GeneratedProperties:

  private lazy val library =
    LibraryFiles.compiled(
      "tests/library_fixtures/binary_natural_backend.lambdalattice",
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => facts,
      _ => encoding,
      _ => JitTesting.libraryTerms
    )

  private def term(key: String): Configured[encoding.type] =
    JitTesting.libraryInstruction[encoding.type](key)

  private def termValue(key: String): JitValue[encoding.type] =
    Value.of(term(key))

  private def set(canonical: Boolean): JitValue[encoding.type] =
    JitValue.Apply(
      termValue("binary_set"),
      termValue(if canonical then "true" else "false")
    )

  /** n in the unique spelling at P, each layer made by the converting
    * construction: zero `binary_zero ∥ T`, 2h `binary_even (h ∥ binary_set
    * false) ∥ T`, 2h + 1 `binary_odd (h ∥ binary_set true) ∥ T`.
    */
  private def spelled(
      value: BigInt,
      canonical: Boolean
  ): JitValue[encoding.type] =
    val layer: JitValue[encoding.type] =
      if value == 0 then termValue("binary_zero")
      else if value.testBit(0) then
        JitValue.Apply(termValue("binary_odd"), spelled(value >> 1, true))
      else JitValue.Apply(termValue("binary_even"), spelled(value >> 1, false))
    JitTesting.parallelOfValues(encoding)(layer, set(canonical))

  /** A natural of each kind, by construction: zero, 2^k − 1 (odd layers all the
    * way down), an even number, and one drawn of mixed bits.
    */
  private val naturals: Gen[Vector[BigInt]] =
    for
      ones <- Gen.int(Range.linear(1, 8))
      half <- Gen.long(Range.linear(1L, 1000L))
      mixed <- Gen.long(Range.linear(0L, 100000L))
    yield Vector(
      BigInt(0),
      (BigInt(1) << ones) - 1,
      BigInt(half) * 2,
      BigInt(mixed)
    )

  property(
    "a natural in the unique spelling under binary_set P is the storage of its value exactly when P or n > 0"
  ) {
    for values <- naturals.forAll
    yield Result.all(
      (for value <- values.toList; canonical <- List(true, false) yield
        val found = spelled(value, canonical)
        val representation = if canonical then BinaryNaturalNatives.canonical
        else BinaryNaturalNatives.positive
        found match
          case JitValue.Stored(storage: BinaryNaturalStorage) =>
            val view =
              encoding.viewOf(storage)(using com.yang_bo.gezi.ir.StorageAccess.granted())
            val oneLayer =
              if value == 0 then
                Configured.same(view.value, term("binary_zero"))
              else
                Value.of(view.value) match
                  case JitValue.Apply(define, field) =>
                    Value.same(
                      define,
                      termValue(if value.testBit(0) then "binary_odd"
                      else "binary_even")
                    ) &&
                    Value.same(field, spelled(value >> 1, value.testBit(0)))
                  case _ => false
            Result
              .assert(
                (canonical || value > 0) && storage.natural == value && storage.representation == representation &&
                  Value.same(
                    Value.of(view.criterion),
                    set(canonical)
                  ) && oneLayer &&
                  Value.same(
                    JitTesting.valueOfNative(encoding)(
                      representation,
                      BinaryNatural(value)
                    ),
                    found
                  )
              )
              .log(s"$value at $canonical: $storage, view $view")
          case other =>
            Result
              .assert(!canonical && value == 0)
              .log(s"$value at $canonical: no storage, $other")
      )
    )
  }

  property("a near miss of the unique spelling stays a parallel") {
    for value <- Gen.long(Range.linear(1L, 1000L)).map(BigInt(_)).forAll
    yield
      // The fallback point's parallel is built by the encoding, which converts `true ∥ boolean_type` into the storage of
      // true: the term `true ∥ boolean_type` as written, a plain parallel, cannot be built in a configuration.
      val fallbackCriterion = JitValue.Apply(
        termValue("binary_set"),
        JitValue.Choice[encoding.type](
          Vector(
            termValue("true"),
            JitTesting.parallelOfValues(encoding)(
              termValue("true"),
              termValue("boolean_type")
            )
          )
        )
      )
      val misses = Vector(
        "even's field filtered by binary_set true" -> JitTesting
          .parallelOfValues(encoding)(
            JitValue.Apply(termValue("binary_even"), spelled(value, true)),
            set(true)
          ),
        "a field with no filter" -> JitTesting.parallelOfValues(encoding)(
          JitValue.Apply(termValue("binary_odd"), termValue("binary_zero")),
          set(true)
        ),
        "even over zero at false" -> JitTesting.parallelOfValues(encoding)(
          JitValue.Apply(termValue("binary_even"), spelled(0, false)),
          set(true)
        ),
        "the criterion through a fallback point" -> JitTesting.parallelOfValues(
          encoding
        )(
          JitValue.Apply(termValue("binary_odd"), spelled(value, true)),
          fallbackCriterion
        )
      )
      Result.all(
        misses.toList.map((name, found) =>
          Result
            .assert(JitValue.Stored.unapply(found).isEmpty)
            .log(s"$name: $found")
        )
      )
  }
