package com.yang_bo.gezi.jit

import com.yang_bo.gezi.jit.JitTesting.*
import com.yang_bo.gezi.jit.NativesTesting.*
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.TermOf
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.weakhead.Bounded
import com.yang_bo.gezi.weakhead.Mode
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.standardlibrary.LibraryFiles
import com.yang_bo.gezi.standardlibrary.MalformedReason
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.standardlibrary.StandardLibraryMalformed

/** A natural pair, the value of the test's data family `natural_pair`. */
final case class NaturalPair(first: BigInt, second: BigInt)
    extends NativeValue[Nothing]

/** The pairs of naturals as a data family of one constructor, `pair l r`,
  * `\p. p l r`, whose two fields are naturals: decoded from the library's pair
  * encoding into a `NaturalPair`, and encoded back with the term at position 0
  * of the fixture's `data_family` of `natural_pair_type`, its constructor
  * native.
  */
object NaturalPairFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("natural_pair")

  val parameterFamily: Option[FamilyIdentity] = None

  private val unparameterisedConstructors: Vector[DataConstructor] =
    Vector(
      DataConstructor(
        NativeName.Constructor(identity, 0),
        Vector(
          DataField.unparameterised(Representation.BigInteger.familyIdentity),
          DataField.unparameterised(Representation.BigInteger.familyIdentity)
        )
      )
    )

  def constructors[Term](
      parameter: Option[FamilyParameter[Term]]
  ): Vector[DataConstructor] = unparameterisedConstructors

  def built[Term](
      parameter: Option[FamilyParameter[Term]],
      layer: DataLayer[Term]
  ): NativeValue[Term] = layer match
    case DataLayer(
          0,
          Vector(NativeValue.Natural(first), NativeValue.Natural(second))
        ) =>
      NaturalPair(first, second)
    case other =>
      throw IllegalArgumentException(s"no layer of a natural pair: $other")

  def taken[Term](
      parameter: Option[FamilyParameter[Term]],
      value: NativeValue[Term]
  ): DataLayer[Term] = value match
    case NaturalPair(first, second) =>
      DataLayer(
        0,
        Vector(NativeValue.Natural(first), NativeValue.Natural(second))
      )
    case other => throw IllegalArgumentException(s"no natural pair: $other")

/** The extension point of the natives: a set an entry gives, the standard set
  * with a data family and two natives the framework does not have, declared by
  * the test knowledge module `natural_pairs` of the fixture `natural_pairs`
  * (its `native` and `combinator_property` facts). The program runs natively
  * under that set, its decodings and native calls counted as the native route's
  * tests count them, with no file of the framework changed.
  */
class NativeBackendExtensionTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private val pairPlace =
    NativePlace.Fixed(Representation.Data(NaturalPairFamily.identity, None))

  /** A closed HOAS term over the terms of no facts. */
  private type Hoas = TermOf[Configured[NoFacts.type]]

  /** The standard set with the family `natural_pair`, the native of its
    * constructor and the exchange `natural_pair_swap`.
    */
  private val pairNatives: NativeBackend = NativeBackend.standard.extended(
    NativeBackend(
      NativeBackend.familyConstructorNatives(NaturalPairFamily) ++ Map(
        NativeName.Function("natural_pair_swap") -> Native(
          Vector(pairPlace),
          pairPlace,
          {
            case Vector(
                  NativeArgument.Represented(NaturalPair(first, second))
                ) =>
              NaturalPair(second, first)
            case other => Native.outsidePlaces("natural_pair_swap", other)
          }
        )
      ),
      Vector(NaturalPairFamily)
    )
  )

  /** The native of the pair's constructor. */
  private val makeNative: NativeName =
    NativeName.Constructor(NaturalPairFamily.identity, 0)

  /** The fixture's knowledge file, the one field of its tuple. */
  private val knowledgeFile =
    "tests/standard_library_fixtures/natural_pairs/compiler/natural_pairs_backend.lambdalattice"

  private lazy val library: StandardLibrary =
    LibraryFiles.compiled(knowledgeFile, Vector(BackendChecks(pairNatives)))

  /** The steps a reading here may take: the readings measured below take fewer
    * than a thousand.
    */
  private val readingLimit: Long = 100000

  /** The library term of the key, the member of its own file of the fixture's
    * library (`natural_pairs/library/natural_pairs/<key>`) read by projection
    * (`StandardLibrary.entryMember`), as a closed HOAS term.
    */
  private def fixtureTerm(key: String): Hoas =
    val fixture = LibraryFiles.fixture("natural_pairs")
    Term.closed(
      StandardLibrary
        .entryMember(
          fixture,
          fixture.resolve(s"library/natural_pairs/$key.lambdalattice"),
          Expansions.none
        )
        ._1
    )

  private lazy val pair = fixtureTerm("pair")
  private lazy val swap = fixtureTerm("swap")
  private lazy val zero = fixtureTerm("zero")
  private lazy val successor = fixtureTerm("successor")
  private lazy val naturalPairType = fixtureTerm("natural_pair_type")

  /** The native specializer of the facts of the library under the pairs'
    * natives, whose singleton type is the configuration the programs are read
    * in.
    */
  private lazy val encoding: StorageEncoding =
    BackendFacts.of(library, pairNatives).storageEncoding

  private given encoding.type = encoding

  /** The library with the pairs' natives and the fixture's terms, forced before
    * the first test and not charged to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => library,
      _ => encoding,
      _ => pair,
      _ => swap,
      _ => zero,
      _ => successor,
      _ => naturalPairType
    )

  /** The value of the program written over terms of no facts, crossed into the
    * encoding's configuration.
    */
  private def valueOf(program: Hoas): Value[encoding.type] =
    instructionValue[encoding.type](
      instructionCrossed(encoding)(
        Defunctionalization.thunkInstruction[NoFacts.type](
          program.deBruijnTerm(Map.empty)
        )(using NoFacts)
      )
    )

  private def jitNormalForms(
      program: Hoas
  ): Read[encoding.type, Vector[Configured[encoding.type]]] =
    normalFormsRead(
      Jit(configured(encoding, JitConfiguration.defaultBudget)),
      valueOf(program),
      readingLimit
    )

  private def referenceNormalForms(
      program: Hoas
  ): Bounded[Vector[Configured[encoding.type]]] =
    normalFormsRead(
      Mode.TablingWeakHead,
      plainConfiguration(encoding),
      valueOf(program),
      readingLimit
    ).outcome

  // Without the entry's set, the standard checks reject the fixture: its
  // natives are not the standard set's.
  test("theStandardSetRejectsTheNativesItDoesNotHave") {
    val rejected = intercept[StandardLibraryMalformed](
      LibraryFiles.compiled(knowledgeFile, Vector(BackendChecks))
    )
    rejected.reason match
      case MalformedReason.BackendRejected(
            BackendSetReason.UnknownNative(native)
          ) =>
        assertEquals(native, "natural_pair_swap")
      case other => fail(s"rejected for $other")
  }

  // The swap of a pair filtered by natural_pair_type: the operand decoded
  // once into the family, natural_pair_swap called once, and the result read
  // back as the reference reads the swapped pair written out.
  test("aNativeOfAnAddedFamilyRunsOnADecodedOperand") {
    val read =
      jitNormalForms(swap(pair(zero)(successor(zero)) ∥ naturalPairType))
    assert(
      sameOutcomes(
        read.outcome,
        referenceNormalForms(pair(successor(zero))(zero))
      )
    )
    val found = counts(read.jitState)
    assertEquals(
      (
        found.callsOf(NativeName.Function("natural_pair_swap")),
        found.decodings
      ),
      (1L, 1L)
    )
  }

  // Two swaps: the inner result stays in the family, so the outer swap is
  // eliminated by the family's codec, with one decoding in all. The pair is
  // rebuilt by pair's own term: the native of a family's constructor is
  // called only under a filter of its family, whose criterion gives the
  // result's parameter (`Jit.nativeAppliedHeads`), and none is written here.
  test("aResultOfAnAddedFamilyStaysRepresented") {
    val read =
      jitNormalForms(swap(swap(pair(zero)(successor(zero)) ∥ naturalPairType)))
    assert(
      sameOutcomes(
        read.outcome,
        referenceNormalForms(pair(zero)(successor(zero)))
      )
    )
    val found = counts(read.jitState)
    assertEquals(
      (
        found.callsOf(NativeName.Function("natural_pair_swap")),
        found.callsOf(makeNative),
        found.decodings
      ),
      (1L, 0L, 1L)
    )
  }
