package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.{Configured, NoFacts, Pure, Value}
import gezi.frontend.TermOf
import gezi.jit.JitTesting.*
import gezi.jit.NativesTesting.*
import gezi.weakhead.Bounded
import gezi.weakhead.Mode

/** A value the JIT builds that equals a native-bound library file's term by
  * content is that term, and is dispatched to its native as the term is: the
  * dispatched reading reads only answers of the reference. Its purpose is to
  * catch the claim of S4b's second change failing: a value built apart that the
  * pool did not make the term itself (so that native dispatch, which reads the
  * term's identity, missed it), or a native the dispatch calls on a built value
  * where its answers are not the reference's.
  *
  * The inputs: a native-bound term of the natives-on library
  * (`NativesTesting.nativesOn`), built again one layer from the JIT's own
  * constructors over its parts, and applied to a closed term of
  * `HoasGenerators.openTermOver` of at most six nodes over the native route
  * library's terms other than the native-bound ones. The law: the built value
  * is the term (`eq`), and every normal form the JIT reads of the application,
  * when it finishes, the reference's read-out by membership does not refute
  * (`referenceReads` is not `NotRead`).
  */
class BuiltInstructionDispatchLawTest extends GeneratedProperties:

  // The natives-on library and its facts take about 6 s to build (measured 2026-11-14), not charged to a test.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(15, "s")

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => nativeBound, _ => argumentLeaves)

  private lazy val library = nativesOn

  private lazy val encoding: StorageEncoding = encodingOf(library)

  private given encoding.type = encoding

  /** The steps the JIT's reading of an input may take: an input it does not
    * read within them proves nothing either way. A tenth of
    * `NativesTesting.normalFormLimit`: the first run of this law at that limit,
    * 10 inputs, passed none within its 15 s.
    */
  private val readingLimit: Long = 200000

  /** The terms bound by the library's `natives`, each once. */
  private lazy val nativeBound: Vector[Pure] =
    library.index.nativeBound.map(_.instruction).distinct

  /** The leaves of the generated programs: the native route's library terms,
    * closed terms of no facts, but the native-bound ones.
    */
  private lazy val argumentLeaves: Vector[TermOf[Configured[NoFacts.type]]] =
    nativeRouteLeaves[NoFacts.type](using NoFacts).filter {
      case Term.Closed(instruction) =>
        !nativeBound.exists(pure =>
          Configured.same(Configured.fromPure(NoFacts)(pure), instruction)(using
            NoFacts
          )
        )
      case _ => true
    }

  /** The term built again one layer from the JIT's own constructors over its
    * parts, as a reading builds a value.
    */
  private def builtOneLayer(
      term: Configured[encoding.type]
  ): JitValue[encoding.type] = term.layer match
    case gezi.ir.Apply(function, argument) =>
      JitValue.Apply(Value.of(function), Value.of(argument))
    case gezi.ir.Parallel(left, right) =>
      parallelOfValues(encoding)(Value.of(left), Value.of(right))
    case gezi.ir.Choice(left, right) =>
      JitValue.Choice(Vector(Value.of(left), Value.of(right)))
    case gezi.ir.Thunk(code, holes, fillings) =>
      JitValue.Thunk(code, holes, fillings.map(Value.of))
    case other =>
      throw IllegalStateException(s"a native-bound term with no layer: $other")

  /** The program of terms of no facts, its constants crossed into the
    * configuration.
    */
  private def crossed(
      program: TermOf[Configured[NoFacts.type]]
  ): TermOf[Configured[encoding.type]] =
    // The program is converted with no facts and its instruction crossed, each node in its spelling here.
    Term.closed(
      JitTesting.instructionCrossed(encoding)(
        JitTesting.termInstruction[NoFacts.type](program)(using NoFacts)
      )
    )

  property(
    "a built value equal to a native-bound term is that term and reads only answers of the reference",
    _.copy(testLimit = SuccessCount(10))
  ) {
    for
      bound <- Gen
        .int(Range.constant(0, nativeBound.size - 1))
        .map(nativeBound)
        .forAll
      nodes <- Gen.int(Range.linear(1, 6)).forAll
      open <- HoasGenerators.openTermOver(0, nodes, argumentLeaves).forAll
    yield
      val boundTerm = Configured.fromPure(encoding)(bound)
      val built = builtOneLayer(boundTerm)
      val program =
        Term.closed(Configured.fromPure(NoFacts)(bound))(open(Vector.empty))
      val value = termValue[encoding.type](crossed(program))
      val jit = Jit(configurationOf(encoding))
      val read = normalFormsSpent(jit, value, readingLimit).outcome
      val refuted = read match
        case Bounded.Finished(normalForms) =>
          normalForms.filter(normalForm =>
            referenceReads(
              referenceConfiguration(jit),
              value,
              normalForm,
              confirmationLimit
            ) == Confirmation.NotRead
          )
        case _ => Vector.empty
      Result
        .all(
          List(
            Result
              .assert(Value.same(built, Value.of(boundTerm)))
              .log(s"built $built, term $bound"),
            Result.assert(refuted.isEmpty).log(s"refuted: $refuted")
          )
        )
        .log(s"read: $read")
  }
