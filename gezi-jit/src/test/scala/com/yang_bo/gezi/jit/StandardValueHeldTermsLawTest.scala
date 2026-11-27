package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.standardlibrary.LibraryFiles

/** The law that a constant storage (`ConstantStorage`) holds no term: its
  * term's children (`NativeStorage.termChildren`) are none, a storage holding
  * no criterion, whatever its value, and so are the terms the encoding finds in
  * its value (`StorageEncoding.heldTerms`). Derived before the run: no
  * constructor of these families has a field that holds an unread term. Each
  * kind is drawn every iteration by construction: a natural at 0, below 100 and
  * above 100,000 (as many successor layers), a boolean, a binary natural above
  * 2^1000 (a thousand layers), a word of a width above 2,000 (as many layers)
  * and a JVM int. Its purpose is to catch a walk of a constant's layers one by
  * one, which cost its value or its width in time and in the stack and
  * overflowed it at 4,000.
  */
class StandardValueHeldTermsLawTest extends GeneratedProperties:

  private lazy val naturalFacts = BackendFacts.of(NativesTesting.nativesOn)
  private lazy val binaryFacts =
    BackendFacts.of(
      LibraryFiles.compiled(
        "tests/library_fixtures/binary_natural_backend.lambdalattice",
        Vector(BackendChecks)
      )
    )
  private lazy val wordFacts = BackendFacts.of(
    LibraryFiles.compiled(
      "tests/library_fixtures/word_backend.lambdalattice",
      Vector(BackendChecks)
    )
  )
  private lazy val intFacts = BackendFacts.of(
    LibraryFiles.compiled(
      "tests/library_fixtures/jvm_int.lambdalattice",
      Vector(BackendChecks)
    )
  )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => naturalFacts, _ => binaryFacts, _ => wordFacts, _ => intFacts)

  /** The storage's term children and the terms the encoding finds in its value,
    * both none: a storage holds no criterion, which its configuration names
    * (`NativeSpecializer.criterionOf`), and a constant's value holds no term.
    */
  private def heldNothing(
      facts: BackendFacts,
      representation: Representation[Nothing],
      value: NativeValue[Nothing]
  ): Result =
    val encoding = facts.storageEncoding
    given encoding.type = encoding
    val held = encoding.operations.heldTerms(representation, value)
    val storage =
      RepresentedStorage[encoding.type](encoding, representation, value)
    val stored = storage.heldTerms(using com.yang_bo.gezi.ir.StorageAccess.granted())
    Result
      .assert(held.isEmpty && stored.isEmpty)
      .log(s"$representation, $value, held $held, the storage's $stored")

  property("a constant storage holds no term") {
    for
      small <- Gen.long(Range.linear(1L, 99L)).forAll
      large <- Gen.long(Range.linear(100000L, 1000000L)).forAll
      truth <- Gen.boolean.forAll
      binaryOffset <- Gen.long(Range.linear(0L, 1000000L)).forAll
      width <- Gen.int(Range.linear(2000, 5000)).forAll
      wordBits <- Gen.long(Range.linear(0L, Long.MaxValue)).forAll
      intBits <- Gen.int(Range.linear(Int.MinValue, Int.MaxValue)).forAll
    yield Result.all(
      Vector(BigInt(0), BigInt(small), BigInt(large)).toList.map(value =>
        heldNothing(
          naturalFacts,
          Representation.BigInteger,
          NativeValue.Natural(value)
        )
      ) ++ List(
        heldNothing(
          naturalFacts,
          Representation.Truth,
          NativeValue.Truth(truth)
        ),
        heldNothing(
          binaryFacts,
          BinaryNaturalNatives.canonical,
          BinaryNatural((BigInt(1) << 1000) + binaryOffset)
        ),
        heldNothing(
          wordFacts,
          Representation.Data(WordFamily.identity, Some(WordWidth(width))),
          Word(width, BigInt(wordBits))
        ),
        heldNothing(
          intFacts,
          Representation.Data(JvmIntFamily.identity, None),
          JvmBits(32, Integer.toUnsignedLong(intBits))
        )
      )
    )
  }
