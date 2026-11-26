package gezi.jit

import gezi.jit.JitTesting.*
import gezi.jit.NativesTesting.*
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.weakhead.Bounded
import gezi.weakhead.Mode
import gezi.weakhead.Value
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.MalformedReason
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import gezi.standardlibrary.StandardLibraryMalformed

/** A natural pair, the value of the test's data family `natural_pair`. */
final case class NaturalPair(first: BigInt, second: BigInt) extends NativeValue

/** The pairs of naturals as a data family of one constructor, `pair l r`,
  * `\p. p l r`, whose two fields are naturals: decoded from the library's
  * pair encoding into a `NaturalPair`, and encoded back with the define the
  * fixture binds to `natural_pair_make`.
  */
object NaturalPairFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("natural_pair")

  val parameterFamily: Option[FamilyIdentity] = None

  private val unparameterisedConstructors: Vector[DataConstructor] =
    Vector(
      DataConstructor(
        NativeName.Function("natural_pair_make"),
        Vector(DataField.unparameterised(Representation.BigInteger.familyIdentity), DataField.unparameterised(Representation.BigInteger.familyIdentity))
      )
    )

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] = unparameterisedConstructors

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue = layer match
    case DataLayer(0, Vector(NativeValue.Natural(first), NativeValue.Natural(second))) => NaturalPair(first, second)
    case other => throw IllegalArgumentException(s"no layer of a natural pair: $other")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer = value match
    case NaturalPair(first, second) => DataLayer(0, Vector(NativeValue.Natural(first), NativeValue.Natural(second)))
    case other                      => throw IllegalArgumentException(s"no natural pair: $other")

/** The extension point of the natives: a set an entry gives, the standard
  * set with a data family and two natives the framework does not have,
  * declared by the test knowledge module `natural_pairs` of the fixture
  * `natural_pairs` (its `native` and `combinator_property` facts). The
  * program runs natively under that set, its decodings and native calls
  * counted as the native route's tests count them, with no file of the
  * framework changed.
  */
class NativeBackendExtensionTest extends gezi.generatedinputs.FailFastSuite:

  private val pairPlace = NativePlace.Fixed(Representation.Data(NaturalPairFamily.identity, None))
  private val naturalPlace = NativePlace.Fixed(Representation.BigInteger)

  /** The standard set with the family `natural_pair`, its constructor
    * `natural_pair_make` and the exchange `natural_pair_swap`.
    */
  private val pairNatives: NativeBackend = NativeBackend.standard.extended(
    NativeBackend.functions(
      Map(
        "natural_pair_make" -> Native(Vector(naturalPlace, naturalPlace), pairPlace, {
          case Vector(NativeArgument.Represented(NativeValue.Natural(first)), NativeArgument.Represented(NativeValue.Natural(second))) =>
            NaturalPair(first, second)
          case other => Native.outsidePlaces("natural_pair_make", other)
        }),
        "natural_pair_swap" -> Native(Vector(pairPlace), pairPlace, {
          case Vector(NativeArgument.Represented(NaturalPair(first, second))) => NaturalPair(second, first)
          case other                                                          => Native.outsidePlaces("natural_pair_swap", other)
        })
      ),
      Vector(NaturalPairFamily)
    )
  )

  /** The fixture's knowledge file, the one field of its tuple. */
  private val knowledgeFile = "tests/standard_library_fixtures/natural_pairs/compiler/natural_pairs_backend.lambdalattice"

  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(knowledgeFile, Vector(BackendChecks(pairNatives)))

  /** The steps a reading here may take: the readings measured below take
    * fewer than a thousand.
    */
  private val readingLimit: Long = 100000

  /** The library term of the key, the member of its own file of the
    * fixture's library (`natural_pairs/library/natural_pairs/<key>`) read by
    * projection (`StandardLibrary.entryMember`), as a closed HOAS term.
    */
  private def fixtureTerm(key: String): Term =
    val fixture = LibraryFiles.fixture("natural_pairs")
    Term.closed(StandardLibrary.entryMember(fixture, fixture.resolve(s"library/natural_pairs/$key.lambdalattice"), Expansions.none)._1)

  private lazy val pair = fixtureTerm("pair")
  private lazy val swap = fixtureTerm("swap")
  private lazy val zero = fixtureTerm("zero")
  private lazy val successor = fixtureTerm("successor")
  private lazy val naturalPairType = fixtureTerm("natural_pair_type")

  /** The library with the pairs' natives and the fixture's terms, forced before the first test and not charged to it (FailFastSuite). */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => library, _ => pair, _ => swap, _ => zero, _ => successor, _ => naturalPairType)

  private def valueOf(program: Term): Value =
    Defunctionalization.thunkInstruction(program.deBruijnTerm(Map.empty))

  private def jitNormalForms(program: Term): Read[Vector[gezi.ir.Instruction]] =
    normalFormsRead(Mode.Jit(Jit(configured(BackendFacts.of(library, pairNatives), JitConfiguration.defaultBudget))), valueOf(program), readingLimit)

  private def referenceNormalForms(program: Term): Bounded[Vector[gezi.ir.Instruction]] =
    normalFormsRead(Mode.TablingWeakHead, valueOf(program), readingLimit).outcome

  // Without the entry's set, the standard checks reject the fixture: its
  // natives are not the standard set's.
  test("theStandardSetRejectsTheNativesItDoesNotHave") {
    val rejected = intercept[StandardLibraryMalformed](
      LibraryFiles.compiled(knowledgeFile, Vector(BackendChecks))
    )
    rejected.reason match
      case MalformedReason.BackendRejected(BackendSetReason.UnknownNative(native)) =>
        assert(Set("natural_pair_make", "natural_pair_swap").contains(native), native)
      case other => fail(s"rejected for $other")
  }

  // The swap of a pair filtered by natural_pair_type: the operand decoded
  // once into the family, natural_pair_swap called once, and the result read
  // back as the reference reads the swapped pair written out.
  test("aNativeOfAnAddedFamilyRunsOnADecodedOperand") {
    val read = jitNormalForms(swap(pair(zero)(successor(zero)) ∥ naturalPairType))
    assertEquals(read.outcome, referenceNormalForms(pair(successor(zero))(zero)))
    val found = counts(read.jitState)
    assertEquals((found.callsOf(NativeName.Function("natural_pair_swap")), found.decodings), (1L, 1L))
  }

  // Two swaps: the inner result stays in the family, so the outer swap is
  // eliminated by the family's codec and the pair rebuilt by
  // natural_pair_make on the represented naturals; one decoding in all.
  test("aResultOfAnAddedFamilyStaysRepresented") {
    val read = jitNormalForms(swap(swap(pair(zero)(successor(zero)) ∥ naturalPairType)))
    assertEquals(read.outcome, referenceNormalForms(pair(zero)(successor(zero))))
    val found = counts(read.jitState)
    assertEquals(
      (found.callsOf(NativeName.Function("natural_pair_swap")), found.callsOf(NativeName.Function("natural_pair_make")), found.decodings),
      (1L, 1L, 1L)
    )
  }
