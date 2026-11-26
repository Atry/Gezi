package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.weakhead.Mode
import gezi.standardlibrary.LibraryFiles
import gezi.frontend.Term
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
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => library, _ => JitTesting.libraryTerms)

  private def term(key: String): Term = JitTesting.libraryTerm(key)

  private def numeral(value: Int): Term =
    (1 to value).foldLeft(term("zero"))((below, _) => term("successor")(below))

  private def word(bits: List[Boolean]): Term =
    bits.foldRight(term("word_end"))((bit, above) => term("word_cell")(term(if bit then "true" else "false"))(above))

  private val filteredWord: Gen[List[Boolean]] =
    Gen.int(Range.linear(0, 12)).flatMap(width => Gen.list(Gen.boolean, Range.singleton(width)))

  property("a word under its type reads as the reference reads it, through the representation") {
    for bits <- filteredWord.forAll
    yield
      val value = JitTesting.termValue(word(bits) ∥ term("word_type")(numeral(bits.size)))
      val jit = NativesTesting.normalFormsSpent(
        Mode.Jit(Jit(NativesTesting.configurationOf(library))),
        value,
        NativesTesting.normalFormLimit
      )
      val reference = NativesTesting.normalFormsSpent(Mode.TablingWeakHead, value, NativesTesting.normalFormLimit)
      Result.all(
        List(
          Result.assert(jit.outcome.finished).log(s"the JIT's reading: ${jit.outcome}"),
          Result.diff(jit.outcome, reference.outcome)(_ == _),
          Result.assert(JitTesting.counts(jit.jitState).encodings > 0).log(s"counts: ${JitTesting.counts(jit.jitState)}")
        )
      )
  }
