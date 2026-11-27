package com.yang_bo.gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.{Closed, Configured, NoFacts, Value}
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.Mode

/** The laws of the 32-bit words held as the JVM's `int` (`JvmIntFamily`,
  * `IntStorage`), over a library compiled from
  * `tests/library_fixtures/jvm_int.lambdalattice`, which holds the module
  * `corpora/compiler/jvm_int` beside the words' backend, J the criterion
  * `jvm_int_type`. Derived from the codec's definition and from section 25 of
  * `docs/design/gezi-set-equations-proofs.md`:
  *
  *   - the library's backend checks accept the module; the codec's constructor
  *     resolves to `word_cell`; the unique spelling's premise
  *     `⊢ J = word_cell boolean_type (word_type 31)` (lemma 25.3) is shown,
  *     none a non-member;
  *   - at every int, 0, `Int.MinValue` and `Int.MaxValue` among them, `built`
  *     after `taken` is the identity, the layer's fields a boolean and a word
  *     of width 31;
  *   - a storage's view is `word_cell s w ∥ J`, s the storage of the least
  *     significant bit and w that of the 31 bits above it;
  *   - the converting construction makes `word_cell s w ∥ J`, s and w those
  *     storages, the int's one storage: one term, one object;
  *   - the JIT reads a word of 32 cells under J through the representation to
  *     the normal forms the reference reads for the word alone (lemma 25.3 and
  *     section 23);
  *   - each native of `JvmIntNatives` computes its define: the JIT reads
  *     `f (a ∥ J) (b ∥ J)` (or `f (a ∥ J)`), a and b 32-bit words written as
  *     cells, to the normal forms the reference reads for `f a b`, the filters
  *     absorbed by theorem (S) of
  *     `docs/design/gezi-type-preservation-proofs.md`, and calls the native
  *     once, at the one call site, its operands decoded at their filters
  *     (dispatch `fallback`).
  *
  * Their purpose is to catch a codec that loses or moves a bit (at the sign bit
  * in particular), a view that is not the unique spelling, a written spelling
  * that makes a second object, a decode point the wiring does not make, and a
  * native that disagrees with its define: at the sign bit, at a product that
  * wraps, at a signed against an unsigned comparison.
  */
class JvmIntStorageLawTest extends GeneratedProperties:

  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(
      "tests/library_fixtures/jvm_int.lambdalattice",
      Vector(BackendChecks)
    )

  private lazy val facts: BackendFacts = BackendFacts.of(library)

  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encoding.type = encoding

  private given com.yang_bo.gezi.ir.StorageAccess = com.yang_bo.gezi.ir.StorageAccess.granted()

  private lazy val readTerms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        LibraryFiles.buildRoot,
        TermTable(
          "tests/jit_fixtures/jvm_int_terms.lambdalattice",
          Vector(
            "true",
            "false",
            "boolean_type",
            "word_end",
            "word_cell",
            "word_type",
            "int32_type",
            "jvm_int_type",
            "int32_add",
            "int32_subtract",
            "int32_multiply",
            "int32_negate",
            "int32_equal",
            "int32_less_than"
          )
        ),
        Expansions.none
      )
      ._1

  /** The terms read under no facts, crossed into the configuration of the
    * encoding.
    */
  private lazy val terms: Map[String, Configured[encoding.type]] =
    val crossed = encoding.crossedAllFromNoFacts(readTerms.values)
    readTerms.view.mapValues(crossed).toMap

  /** The library compiled and its terms read before the first test, not charged
    * to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => facts)

  private def term(name: String): Configured[encoding.type] =
    terms.getOrElse(name, throw IllegalArgumentException(s"no member $name"))

  private val representation: Representation[Nothing] =
    Representation.Data(JvmIntFamily.identity, None)

  private val aboveRepresentation: Representation[Nothing] =
    Representation.Data(WordFamily.identity, Some(WordWidth(31)))

  private val truthRepresentation: Representation[Nothing] =
    Representation.Data(BooleanFamily.identity, None)

  /** Every int, its edges and the values whose low or high bit alone is set
    * drawn often.
    */
  private val ints: Gen[Int] =
    Gen.frequency1(
      3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)),
      1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue)
    )

  private def value(bits: Int): JvmBits =
    JvmBits(32, Integer.toUnsignedLong(bits))

  private def intStorage(bits: Int): JitValue[encoding.type] =
    JitTesting.valueOfNative(encoding)(representation, value(bits))

  private def lowBit(bits: Int): JitValue[encoding.type] =
    JitTesting.valueOfNative(encoding)(
      truthRepresentation,
      NativeValue.Truth((bits & 1) == 1)
    )

  private def above(bits: Int): JitValue[encoding.type] = JitTesting
    .valueOfNative(encoding)(aboveRepresentation, Word(31, BigInt(bits >>> 1)))

  test("the module is accepted, and its constructor is word_cell") {
    assert(
      Configured.same(
        Configured.fromPure(encoding)(
          facts.constructorDefine(
            NativeName.Constructor(JvmIntFamily.identity, 0)
          )
        ),
        term("word_cell")
      )
    )
  }

  property(
    "built after taken is the identity, the fields a boolean and a word of 31 bits"
  ) {
    for bits <- ints.forAll
    yield
      val layer = JvmIntFamily.taken(None, value(bits))
      val declared = JvmIntFamily
        .constructors(None)(layer.constructor)
        .fields
        .map(_.representation(None))
      val found = layer.fields.map {
        case NativeValue.Truth(_) => truthRepresentation
        case Word(width, _)       =>
          Representation.Data(WordFamily.identity, Some(WordWidth(width)))
        case other =>
          throw IllegalStateException(
            s"a jvm_int's field is a boolean or a word, not $other"
          )
      }
      Result.diff(
        (JvmIntFamily.built(None, layer), found),
        (value(bits), declared)
      )(_ == _)
  }

  /** The `word_cell s w` of the int's bits, a term of the configuration. */
  private def cellOf(bits: Int): Configured[encoding.type] =
    val cell = JitValue.Apply(
      JitValue.Apply(Value.of(term("word_cell")), lowBit(bits)),
      above(bits)
    )
    Closed
      .configured(cell)
      .getOrElse(
        throw IllegalStateException(
          s"a word cell of storages is no term: $cell"
        )
      )

  property("a storage's view is the unique spelling") {
    for bits <- ints.forAll
    yield
      val stored = intStorage(bits) match
        case JitValue.Stored(storage: IntStorage) => storage
        case other                                =>
          throw IllegalStateException(
            s"a jvm_int's storage is an IntStorage, not $other"
          )
      val view = encoding.viewOf(stored)
      Result.all(
        List(
          Result
            .assert(Configured.same(view.value, cellOf(bits)))
            .log("the view's value is not `word_cell s w`"),
          Result
            .assert(
              Closed
                .configured(JitTesting.criterionOf(encoding)(representation))
                .exists(Configured.same(view.criterion, _))
            )
            .log("the view's criterion is not J"),
          Result.diff(stored.bits, bits)(_ == _)
        )
      )
  }

  property(
    "the converting construction makes `word_cell s w ∥ J` the int's one storage"
  ) {
    for bits <- ints.forAll
    yield
      val written = JitTesting.parallelOfValues(encoding)(
        Value.of(cellOf(bits)),
        JitTesting.criterionOf(encoding)(representation)
      )
      Result.assert(Value.same(written, intStorage(bits)))
  }

  property(
    "a word of 32 cells under jvm_int_type reads as the word, through the representation"
  ) {
    for bits <- Gen.list(Gen.boolean, Range.singleton(32)).forAll
    yield
      val word = bits.foldRight(Term.closed(term("word_end")))((bit, rest) =>
        Term.closed(term("word_cell"))(Term.closed(term(if bit then "true"
        else "false")))(rest)
      )
      val jit = NativesTesting.normalFormsSpent(
        Jit(NativesTesting.configurationOf(encoding)),
        JitTesting.termValue(word ∥ Term.closed(term("jvm_int_type"))),
        NativesTesting.normalFormLimit
      )
      val reference = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(word),
        NativesTesting.normalFormLimit
      )
      Result.all(
        List(
          Result
            .assert(jit.outcome.finished)
            .log(s"the JIT's reading: ${jit.outcome}"),
          Result.assert(
            JitTesting.sameOutcomes(jit.outcome, reference.outcome)
          ),
          Result
            .assert(JitTesting.counts(jit.jitState).encodings > 0)
            .log(s"counts: ${JitTesting.counts(jit.jitState)}")
        )
      )
  }

  /** The 32-bit word of the int's bits written as cells, the least significant
    * bit first.
    */
  private def written(bits: Int): TermOf[Configured[encoding.type]] =
    (31 to 0 by -1).foldLeft(Term.closed(term("word_end")))((above, position) =>
      Term.closed(term("word_cell"))(
        Term.closed(term(if ((bits >>> position) & 1) == 1 then "true"
        else "false"))
      )(above)
    )

  private def filteredInt(bits: Int): TermOf[Configured[encoding.type]] =
    written(bits) ∥ Term.closed(term("jvm_int_type"))

  /** The natives by their define's name and their arity. */
  private val natives: Vector[(String, String, Int)] = Vector(
    ("int32_add", "jvm_int_add", 2),
    ("int32_subtract", "jvm_int_subtract", 2),
    ("int32_multiply", "jvm_int_multiply", 2),
    ("int32_negate", "jvm_int_negate", 1),
    ("int32_equal", "jvm_int_equal", 2),
    ("int32_less_than", "jvm_int_less_than", 2)
  )

  property(
    "each native computes its define, called once on operands decoded at their filters"
  ) {
    for
      (define, native, arity) <- Gen
        .int(Range.constant(0, natives.size - 1))
        .map(natives)
        .forAll
      left <- ints.forAll
      right <- ints.forAll
    yield
      val operands = Vector(left, right).take(arity)
      val jit = NativesTesting.normalFormsSpent(
        Jit(NativesTesting.configurationOf(encoding)),
        JitTesting.termValue(
          operands.foldLeft(Term.closed(term(define)))((function, bits) =>
            function(filteredInt(bits))
          )
        ),
        NativesTesting.normalFormLimit
      )
      val reference = NativesTesting.normalFormsSpent(
        Mode.TablingWeakHead,
        JitTesting.plainConfiguration(encoding),
        JitTesting.termValue(
          operands.foldLeft(Term.closed(term(define)))((function, bits) =>
            function(written(bits))
          )
        ),
        NativesTesting.normalFormLimit
      )
      Result.all(
        List(
          Result
            .assert(jit.outcome.finished)
            .log(s"the JIT's reading: ${jit.outcome}"),
          Result.assert(
            JitTesting.sameOutcomes(jit.outcome, reference.outcome)
          ),
          Result.diff(
            JitTesting
              .counts(jit.jitState)
              .callsOf(NativeName.Function(native)),
            1L
          )(_ == _)
        )
      )
  }
