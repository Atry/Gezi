package gezi.jit

import gezi.ir.Pure
import gezi.weakhead.BooleanReading
import gezi.weakhead.NaturalReading
import gezi.weakhead.Shape
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.FieldCriterion
import gezi.standardlibrary.LibraryFiles
import gezi.standardlibrary.MalformedReason
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import gezi.standardlibrary.StandardLibraryMalformed

/** The tests of `gezi/tests/standard_library.plt` that check the backend's set
  * (`BackendChecks`, the port of prolog_backend_library.pl): the Prolog tests
  * compiled each library with the Prolog backend loaded, so its checks ran;
  * here the library is compiled with `BackendChecks`.
  */
class StandardLibraryBackendTest extends gezi.generatedinputs.FailFastSuite:

  /** The library of the fixture's knowledge file of the name, the one field of
    * its tuple, checked by the backend.
    */
  private def compiled(fixture: String, name: String): StandardLibrary =
    LibraryFiles.compiled(
      s"tests/standard_library_fixtures/$fixture/compiler/$name.lambdalattice",
      Vector(BackendChecks)
    )

  /** The library term of the key, the member of its own file
    * `<directory>/<key>` under the fixture read by projection
    * (`StandardLibrary.entryMember`): the pure key the library's knowledge
    * names, with no table from paths to terms.
    */
  private def fixtureTerm(
      fixture: String,
      directory: String,
      key: String
  ): Pure =
    val root = LibraryFiles.fixture(fixture)
    Pure.required(
      StandardLibrary
        .entryMember(
          root,
          root.resolve(s"$directory/$key.lambdalattice"),
          Expansions.none
        )
        ._1
    )

  private def rejected(fixture: String, name: String): BackendSetReason =
    intercept[StandardLibraryMalformed](compiled(fixture, name)).reason match
      case MalformedReason.BackendRejected(reason: BackendSetReason) => reason
      case other => fail(s"not a reason of the backend's check: $other")

  // The half of a_backend_property_needs_no_lemma (standard_library.plt:431)
  // that the backend's set carried: bp names big_integer for nat_type of bd
  // and gives its constructors zero and successor by a data family, so the
  // backend's set is enabled and its checks run on bd + bp (the data family
  // has the codec's constructors, at their positions, and they are of its
  // shape) and accept it, with the same index as without the checks
  // (StandardLibraryTest, aBackendPropertyNeedsNoLemma). No native is
  // declared, and the facts bind the constructors by their positions.
  test("aBackendPropertyNeedsNoLemmaAndTheBackendsChecksAcceptIt") {
    val library = compiled("backend_property", "bp")
    assertEquals(library.index.lemmaSides.size, 0)
    def instruction(name: String) =
      fixtureTerm("backend_property", "library/bd", name)
    assertEquals(library.index.nativeBound, Vector.empty)
    assertEquals(
      library.index.combinatorProperties,
      Vector(
        CombinatorProperty(instruction("zero"), Property.FirstOrderConstructor),
        CombinatorProperty(
          instruction("successor"),
          Property.FirstOrderConstructor
        ),
        CombinatorProperty(
          instruction("nat_type"),
          Property.NativeSpecialization("big_integer")
        ),
        CombinatorProperty(
          instruction("nat_type"),
          Property.DataFamily(
            0,
            Vector(instruction("zero"), instruction("successor"))
          )
        ),
        CombinatorProperty(
          instruction("nat_type"),
          Property.DataFields(1, Vector(FieldCriterion.Recursive))
        )
      )
    )
    assertEquals(
      BackendFacts.bindings(library.index, NativeBackend.standard),
      Vector(
        NativeBinding(
          instruction("zero"),
          NativeName.Constructor(BigIntegerFamily.identity, 0)
        ),
        NativeBinding(
          instruction("successor"),
          NativeName.Constructor(BigIntegerFamily.identity, 1)
        )
      )
    )
  }

  // A native binds a native of the backend to a library term that takes its
  // parameters: t = \x. x takes the one parameter of natural_double.
  test("aNativeBindsAnInstructionToAName") {
    val library = compiled("native_bound", "b")
    val instruction = fixtureTerm("native_bound", "library/b", "t")
    assert(
      library.index.nativeBound.contains(
        NativeBound(instruction, "natural_double")
      )
    )
  }

  // With the backend's set enabled, here by a native of its table, a native
  // the table does not list is malformed.
  test("aNativeThePrologBackendLacksBesideItsSetIsMalformed") {
    assertEquals(
      rejected("unknown_native", "unknown_native_set"),
      BackendSetReason.UnknownNative("no_such_native")
    )
  }

  // The value of (\x. x) ∥ (\x. \y. x) is one parallel set of two heads, no
  // single lambda, so the term does not take the one parameter of
  // natural_double. Two identities would not do: they are one term, and
  // their parallel has the one head.
  test("aNativeWhoseParametersTheDefineDoesNotTakeIsMalformed") {
    assertEquals(
      rejected("native_parameters", "parameters_untaken"),
      BackendSetReason.NativeParameters("natural_double", 1)
    )
  }

  // A constructor of a codec is bound to one term at most: two data
  // families of nat_type list two zeros at the constructor 0 of big_integer.
  test("aCodecNativeBoundToTwoTermsIsMalformed") {
    rejected("codec_native_twice", "zero_twice") match
      case BackendSetReason.CodecNative(
            NativeName.Constructor(FamilyIdentity.Codec("big_integer"), 0),
            Vector(_, _)
          ) =>
        ()
      case other => fail(s"another reason: $other")
  }

  test("aNativeSpecializationWithoutItsDataFamilyIsMalformed") {
    assertEquals(
      rejected("backend_codec", "data_family_missing"),
      BackendSetReason.Specialization(
        "big_integer",
        SpecializationProblem.DataFamilyMissing
      )
    )
  }

  // A data family of one constructor where big_integer's codec has two.
  test("aNativeSpecializationWithAnIllShapedDataFamilyIsMalformed") {
    rejected("backend_codec", "data_family_ill_shaped") match
      case BackendSetReason.Specialization(
            "big_integer",
            SpecializationProblem.DataFamilyIllShaped(
              Property.DataFamily(0, Vector(_)),
              0,
              2
            )
          ) =>
        ()
      case other => fail(s"another reason: $other")
  }

  test("aRepresentationOfAnotherBackendBesideThePrologBackendsSetIsMalformed") {
    assertEquals(
      rejected("backend_codec", "mixed_backends"),
      BackendSetReason.Specialization(
        "fixed_width",
        SpecializationProblem.NoCodec
      )
    )
  }

  // A zero that answers the second case is not of the codec's shape.
  test("aNativeSpecializationOfConstructorsOfAnotherShapeIsMalformed") {
    rejected("backend_codec_unfit", "unfit_backend") match
      case BackendSetReason.Specialization(
            "big_integer",
            SpecializationProblem.NotOfTheShape(
              Shape.Unfit(_, Vector(NaturalReading.Successor(_)))
            )
          ) =>
        ()
      case other => fail(s"another reason: $other")
  }

  test("aBooleanSpecializationWithoutItsDataFamilyIsMalformed") {
    assertEquals(
      rejected("backend_boolean_codec", "data_family_missing"),
      BackendSetReason.Specialization(
        "boolean",
        SpecializationProblem.DataFamilyMissing
      )
    )
  }

  test("aBooleanSpecializationOfConstructorsOfAnotherShapeIsMalformed") {
    assertEquals(
      rejected("backend_boolean_codec_unfit", "unfit_boolean_backend"),
      BackendSetReason.Specialization(
        "boolean",
        SpecializationProblem.NotOfTheShape(
          Shape.Unfit(
            Vector(BooleanReading.Truth(false)),
            Vector(BooleanReading.Truth(false))
          )
        )
      )
    )
  }

  test("aBooleanCodecNativeBoundToTwoTermsIsMalformed") {
    rejected("backend_boolean_codec", "true_twice") match
      case BackendSetReason.CodecNative(
            NativeName.Constructor(FamilyIdentity.Codec("boolean"), 0),
            Vector(_, _)
          ) =>
        ()
      case other => fail(s"another reason: $other")
  }
