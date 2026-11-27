package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.standardlibrary.LibraryFiles
import gezi.frontend.Term
import gezi.frontend.TermOf
import gezi.ir.Configured
import gezi.generatedinputs.GeneratedProperties

/** The laws of the binary naturals' family (`BinaryNaturalFamily`,
  * binary_prolog_backend):
  * (1) the codec: at both parameters, `built` after `layer` is the identity
  * on every natural the parameter admits, and the layer is never excluded;
  * (2) the decoding: the library with the module compiles under the
  * backend's checks, and at a generated numeral written with the three
  * constructors, canonical or not, under `binary_set p` for both p: where
  * the numeral is in the set, the JIT reads one normal form, the one
  * tabling(weak_head) reads of the numeral alone, through the representation (at
  * least one layer encoded), and the reference's read-out by membership
  * confirms it of the filtered term (`NativesTesting.referenceReads`, as
  * `JitNativesTest` confirms nat_type's); where it is not, the JIT reads no
  * normal form and encodes nothing, and tabling(weak_head) finds none within
  * `NativesTesting.confirmationLimit` steps. The read-out by membership
  * tests whether `binary_set p` reads the numeral by descending into the
  * set and the numeral together, so it does not enumerate the set's
  * members; it runs under tabling(weak_head).
  * The whole read-out cannot show that a filter over an infinite set has no
  * member (it reads ever larger members), so on a non-member this law
  * checks that the reference finds no normal form within its limit, not
  * that it reads the empty set; `JitNativesTest`'s
  * aFilterOnANonNumberGivesNoAnswerWithNatives states nat_type's case so.
  * Its purpose is to catch a codec that loses a bit, one that decodes a
  * non-canonical numeral or zero among the positive ones into a value
  * (an answer where the filter has none), and a wiring that makes no
  * decode point of the filter. The numerals' constructors, binary_set and
  * the booleans are members of `JitTesting.libraryTermsFile`, each read by
  * projection, so no name is resolved.
  */
class BinaryNaturalDecodingLawTest extends GeneratedProperties:

  /** The library of native_types, prolog_backend and binary_prolog_backend,
    * the one field of tests/library_fixtures/binary_natural_backend.lambdalattice,
    * checked by the backend.
    */
  private lazy val library =
    LibraryFiles.compiled("tests/library_fixtures/binary_natural_backend.lambdalattice", Vector(BackendChecks))

  /** The JIT's configuration of the library's facts, one for every input: the facts are a function of the library. */
  private lazy val encoding: StorageEncoding = NativesTesting.encodingOf(library)

  private given encoding.type = encoding

  private lazy val configuration = NativesTesting.configurationOf(encoding)

  /** The library, its configuration and the library terms the numerals are built from, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => configuration, _ => JitTesting.libraryTerms)

  /** A numeral as a tree of the three constructors, canonical or not. */
  private enum Numeral:
    case Zero
    case Even(half: Numeral)
    case Odd(half: Numeral)

  /** A numeral of at most the depth, each constructor drawn uniformly at
    * every size (a size-scaled range would draw zero at the small sizes,
    * and a run would meet a positive numeral only among its last inputs).
    */
  private def numeral(depth: Int): Gen[Numeral] =
    if depth == 0 then Gen.constant(Numeral.Zero)
    else
      Gen.int(Range.constant(0, 2)).flatMap {
        case 0 => Gen.constant(Numeral.Zero)
        case 1 => numeral(depth - 1).map(Numeral.Even(_))
        case _ => numeral(depth - 1).map(Numeral.Odd(_))
      }

  /** Whether the numeral is in binary_set at the parameter: zero at true
    * only, an even numeral when its half is a positive one, an odd numeral
    * when its half is any canonical one.
    */
  private def member(written: Numeral, canonical: Boolean): Boolean = written match
    case Numeral.Zero       => canonical
    case Numeral.Even(half) => member(half, false)
    case Numeral.Odd(half)  => member(half, true)

  private def name(key: String): TermOf[Configured[encoding.type]] = JitTesting.libraryTerm[encoding.type](key)

  private def term(written: Numeral): TermOf[Configured[encoding.type]] = written match
    case Numeral.Zero       => name("binary_zero")
    case Numeral.Even(half) => name("binary_even")(term(half))
    case Numeral.Odd(half)  => name("binary_odd")(term(half))

  property("built after layer is the identity at both parameters, never on an excluded layer") {
    for
      value <- Gen.long(Range.linear(0L, 1L << 40)).forAll
      canonical <- Gen.boolean.forAll
    yield
      val parameter = Some(BinaryCanonicity(canonical))
      if !canonical && value == 0 then Result.success
      else
        val layer = BinaryNaturalFamily.layer(parameter, BinaryNatural(BigInt(value)))
        Result.all(
          List(
            Result.diff(BinaryNaturalFamily.built(parameter, layer), BinaryNatural(BigInt(value)))(_ == _),
            Result.assert(!BinaryNaturalFamily.excluded(parameter, layer.constructor))
          )
        )
  }

  property("a numeral under binary_set reads as weak_head reads it, through the representation where it is a member") {
    for
      written <- Gen.int(Range.linear(0, 10)).flatMap(numeral).forAll
      canonical <- Gen.boolean.forAll
    yield
      val filtered = term(written) ∥ name("binary_set")(name(if canonical then "true" else "false"))
      val value = JitTesting.termValue(filtered)
      val jit = NativesTesting.normalFormsSpent(
        Jit(configuration),
        value,
        NativesTesting.normalFormLimit
      )
      val encodings = JitTesting.counts(jit.jitState).encodings
      val agreement =
        if member(written, canonical) then
          val numeralValue = JitTesting.termValue(term(written))
          val numeralForms = NativesTesting.normalFormsSpent(Mode.TablingWeakHead, JitTesting.plainConfiguration(encoding), numeralValue, NativesTesting.normalFormLimit)
          jit.outcome match
            case Bounded.Finished(Vector(found)) =>
              val confirmed = Result.diff(
                NativesTesting.referenceReads(JitTesting.plainConfiguration(encoding), value, found, NativesTesting.confirmationLimit),
                Confirmation.Confirmed
              )(_ == _)
              Result.all(List(Result.assert(JitTesting.sameOutcomes(jit.outcome, numeralForms.outcome)), confirmed))
            case other => Result.failure.log(s"a member read to $other, not to one normal form")
        else
          val reference = NativesTesting.normalFormsSpent(Mode.TablingWeakHead, JitTesting.plainConfiguration(encoding), value, NativesTesting.confirmationLimit)
          Result.all(
            List(
              Result.assert(JitTesting.sameOutcomes(jit.outcome, Bounded.Finished(Vector.empty[Configured[encoding.type]]))),
              Result.assert(reference.outcome match
                case Bounded.Finished(found) => found.isEmpty
                case _                       => true
              ).log(s"the reference's reading of a non-member: ${reference.outcome}")
            )
          )
      Result.all(
        List(
          Result.assert(jit.outcome.finished).log(s"the JIT's reading: ${jit.outcome}"),
          agreement,
          Result.diff(encodings > 0, member(written, canonical))(_ == _).log(s"encodings: $encodings")
        )
      )
  }
