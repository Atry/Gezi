package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.weakhead.Mode
import gezi.standardlibrary.LibraryFiles
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.generatedinputs.GeneratedProperties

/** The law of the word family's wiring (fixed_width_prolog_backend, the
  * family `word` in `NativeBackend.standard`): the library with the
  * module compiles under the backend's checks, and at a generated width w
  * and word x written as its cells, the JIT reads `x ∥ word_type w` to the
  * normal forms the reference reads, through the representation: it encodes
  * at least one layer, which it does only when the filter is a decode point.
  * Its purpose is to catch a wiring that makes no decode point of the
  * filter (a missing specialization, family or constructor binding), one
  * the backend's checks reject, and a decoding or encoding that changes the
  * word. The program's library terms are members of
  * `JitTesting.libraryTermsFile` (`JitTesting.libraryTerm`), the terms the
  * library's knowledge files import, so the specialization the backend
  * binds to word_type is the term the program applies.
  */
class WordDecodingLawTest extends GeneratedProperties:

  /** The library of native_types, fixed_width, prolog_backend and
    * fixed_width_prolog_backend, the one field of
    * tests/library_fixtures/word_backend.lambdalattice, checked by the backend.
    */
  private lazy val library =
    LibraryFiles.compiled("tests/library_fixtures/word_backend.lambdalattice", Vector(BackendChecks))

  /** The library's compilation and the library terms the words are built
    * from, forced before the first test and not charged to it
    * (FailFastSuite): charged to the property, the compilation took the
    * property just over its 3 s deadline (3.02 s on main f88684290, 2026-11-16).
    */
  private lazy val encoding: StorageEncoding = NativesTesting.encodingOf(library)

  private given encoding.type = encoding

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library, _ => JitTesting.libraryTerms)

  private def term(key: String): TermOf[Configured[encoding.type]] = JitTesting.libraryTerm[encoding.type](key)

  private def numeral(value: Int): TermOf[Configured[encoding.type]] =
    (1 to value).foldLeft(term("zero"))((below, _) => term("successor")(below))

  private def word(bits: List[Boolean]): TermOf[Configured[encoding.type]] =
    bits.foldRight(term("word_end"))((bit, above) => term("word_cell")(term(if bit then "true" else "false"))(above))

  /** The word under `word_type` of its width. */
  private def filtered(bits: List[Boolean]): TermOf[Configured[encoding.type]] = word(bits) ∥ term("word_type")(numeral(bits.size))

  private val filteredWord: Gen[List[Boolean]] =
    Gen.int(Range.linear(0, 12)).flatMap(width => Gen.list(Gen.boolean, Range.singleton(width)))

  /** Words of the two widths the natives hold as `Short` and `Int`, in the
    * one backend the other property reads.
    */
  private val nativeWidthWord: Gen[List[Boolean]] =
    Gen.element1(16, 32).flatMap(width => Gen.list(Gen.boolean, Range.singleton(width)))

  /** Whether the JIT reads `x ∥ word_type w` through the representation to
    * the normal forms the reference reads for the term `referenceTerm`, for
    * the word x written as its cells and w its width.
    */
  private def readThroughTheRepresentation(bits: List[Boolean], referenceTerm: TermOf[Configured[encoding.type]]): Result =
    val jit = NativesTesting.normalFormsSpent(
      Jit(NativesTesting.configurationOf(encoding)),
      JitTesting.termValue(filtered(bits)),
      NativesTesting.normalFormLimit
    )
    val reference =
      NativesTesting.normalFormsSpent(Mode.TablingWeakHead, JitTesting.plainConfiguration(encoding), JitTesting.termValue(referenceTerm), NativesTesting.normalFormLimit)
    Result.all(
      List(
        Result.assert(jit.outcome.finished).log(s"the JIT's reading: ${jit.outcome}"),
        Result.assert(JitTesting.sameOutcomes(jit.outcome, reference.outcome)),
        Result.assert(JitTesting.counts(jit.jitState).encodings > 0).log(s"counts: ${JitTesting.counts(jit.jitState)}")
      )
    )

  /** Catches a constructor of the family bound by anything but its position
    * in `word_type`'s `data_family`: each of the codec's constructor natives
    * resolves to the library term at that position, `word_end` at 0 and
    * `word_cell` at 1.
    */
  test("the word constructors resolve from word_type's data_family") {
    val facts = BackendFacts.of(library)
    assert(gezi.ir.Configured.same(gezi.ir.Configured.fromPure(encoding)(facts.constructorDefine(WordFamily.endNative)), JitTesting.libraryInstruction[encoding.type]("word_end")))
    assert(gezi.ir.Configured.same(gezi.ir.Configured.fromPure(encoding)(facts.constructorDefine(WordFamily.cellNative)), JitTesting.libraryInstruction[encoding.type]("word_cell")))
  }

  /** The JIT reads a word of 16 or 32 cells under `word_type` of its width
    * to the normal forms the reference reads for the word alone: a word of
    * width w under `word_type w` is the word, which the property over the
    * widths 0 to 12 checks against the reference's own reading of the
    * filter. Here the reference reads the bare word, since its reading of
    * the filter at 32 cells is what the 3 s deadline does not allow.
    */
  property("a word of 16 or 32 bits under its type reads as the word, through the representation") {
    for bits <- nativeWidthWord.forAll
    yield readThroughTheRepresentation(bits, word(bits))
  }

  property("a word under its type reads as the reference reads it, through the representation") {
    for bits <- filteredWord.forAll
    yield readThroughTheRepresentation(bits, filtered(bits))
  }
