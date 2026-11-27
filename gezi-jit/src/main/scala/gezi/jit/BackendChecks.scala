package gezi.jit

import gezi.weakhead.Computed
import gezi.weakhead.Head
import gezi.weakhead.NeutralValue
import gezi.weakhead.ListCodec
import gezi.weakhead.Mode
import gezi.weakhead.ListConstructor
import gezi.weakhead.NeutralVariable
import gezi.weakhead.ParallelView
import gezi.weakhead.ReadingState
import gezi.weakhead.Shape
import gezi.ir.Value
import gezi.weakhead.WeakHead
import gezi.weakhead.Answers
import gezi.standardlibrary.BackendNative
import gezi.standardlibrary.BackendReason
import gezi.standardlibrary.BackendSpecialization
import gezi.standardlibrary.LibraryBackend
import gezi.standardlibrary.MalformedReason
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryMalformed
import gezi.ir.{Configured, NoFacts, Pure}
import gezi.weakhead.ReadingConfiguration

/** Why a native specialization is malformed under the backend's check. */
enum SpecializationProblem:

  /** `no_codec`: the backend has no codec for the representation. */
  case NoCodec

  /** The library term the representation is declared of has no
    * `data_family`, so the codec's constructors have no terms
    * ([[FamilyIdentity]]).
    */
  case DataFamilyMissing

  /** A `data_family` of the library term the representation is declared
    * of has not the codec's criterion parameters or constructors: the
    * family as declared, and the codec's numbers of criterion parameters
    * and of constructors.
    */
  case DataFamilyIllShaped(family: Property.DataFamily, arity: Int, constructors: Int)

  /** `unfit(First, Second)`, or a reading past its budget: the codec's
    * constructors do not have its assumed shape, or the check could not
    * tell (`Shape.LimitReached`, which the Prolog check reported as `unfit`
    * with the readings `[unread]`).
    */
  case NotOfTheShape(shape: Shape[Any])

/** The reasons the backend's check of its set gives (prolog_backend_library.pl,
  * THE PROLOG BACKEND'S SET), each named after the Prolog reason.
  */
enum BackendSetReason extends BackendReason:

  /** `unknown_native(Native)`: the native is not in the backend's table. */
  case UnknownNative(native: String)

  /** `native_parameters(Native, Count)`: the library term bound to the
    * native does not take its parameters.
    */
  case NativeParameters(native: String, count: Int)

  /** `native_parameters_not_read(Native, Count)`: the check of the
    * parameters ran past its budget.
    */
  case NativeParametersNotRead(native: String, count: Int)

  /** `codec_native(Native, Terms)`: a constructor a codec encodes with is
    * bound to more than one library term: by two `native` declarations, or
    * by two `data_family` declarations of types specialized to its family
    * that list different terms at its position.
    */
  case CodecNative(native: NativeName, terms: Vector[Pure])

  /** `combinator_property(native_specialization(R), Problem)`: the native
    * specialization is malformed.
    */
  case Specialization(representation: String, problem: SpecializationProblem)

/** A fresh value a define is applied to in the check of its parameters,
  * numbered by the parameters still to be taken: a neutral value no closed
  * program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class NativeParameter(remaining: Int) extends NeutralVariable

/** The backend's checks of the standard library, the port of
  * `gezi/prolog/gezi/prolog_backend_library.pl`, whose module
  * comment these follow: the checks the library compiler runs on the
  * backend's set of facts when that set is enabled, that is when a native of
  * the enabled modules is in the backend's set or a native specialization
  * names a family the backend has a codec for. Then every native is in the
  * set, or is a constructor one of its codecs encodes with, and its define
  * takes its parameters (a constructor's: one for each of its fields), every native specialization
  * names a family with a codec, each constructor a codec encodes with is
  * bound to one term at most, and each specialization's codec finds its
  * constructors bound and of its shape. A codec whose constructors are its
  * family's positions (`NativeName.Constructor`) finds them in the
  * `data_family` of the term the specialization is declared of, which has
  * the codec's criterion parameters and constructors; one whose
  * constructors are named by strings finds them bound by `native`
  * declarations. When the set is not enabled, the
  * facts are another backend's and nothing is checked. The codecs are the
  * set's data families and the framework's lists (the judge record, section
  * 3.0).
  *
  * @param nativeBackend
  *   the natives and the data families checked against, the set the JIT
  *   then runs with on the same library (`BackendFacts.of`)
  */
final case class BackendChecks(nativeBackend: NativeBackend) extends LibraryBackend:

  def checked(
      natives: Vector[BackendNative],
      specializations: Vector[BackendSpecialization]
  ): Unit =
    if backendNamed(natives, specializations) then
      natives.foreach(nativeChecked(_))
      specializations.foreach(specializationCodecChecked)
      codecNativesChecked(specializations)
      specializations.foreach(specializationRepresentationChecked)

  /** The terms of the library are read under no facts, as a program's is: the check reads them with the weak head of
    * `NoFacts`, whose terms hold no storage.
    */
  private given NoFacts.type = NoFacts

  /** The capability of the readings of no facts, which hold no storage (`ReadingConfiguration.withoutFacts`). */
  private given gezi.ir.StorageAccess = gezi.weakhead.ReadingConfiguration.withoutFacts.storageAccess

  /** A term of the library as one of no facts: the same object. */
  private def noFactsTerm(term: Pure): Configured[NoFacts.type] = Configured.fromPure(NoFacts)(term)

  private def malformed(reason: BackendSetReason): Nothing =
    throw StandardLibraryMalformed(MalformedReason.BackendRejected(reason))

  /** Whether the set or the framework has a codec for the family. */
  private def hasCodec(family: String): Boolean =
    family == Representation.listFamily.name || family == Representation.arrayListFamily.name ||
      nativeBackend.family(FamilyIdentity.Codec(family)).isDefined

  private def backendNamed(
      natives: Vector[BackendNative],
      specializations: Vector[BackendSpecialization]
  ): Boolean =
    natives.exists(native => nativeBackend.natives.contains(NativeName.Function(native.native))) ||
      specializations.exists(specialization => hasCodec(specialization.representation))

  private def nativeChecked(native: BackendNative): Unit =
    val name = NativeName.Function(native.native)
    nativeBackend.natives.get(name) match
      case Some(found) => parametersChecked(native, found.parameterCount)
      case None =>
        codecConstructorFields.get(name) match
          case Some(fields) => parametersChecked(native, fields)
          case None         => malformed(BackendSetReason.UnknownNative(native.native))

  /** The number of fields of each constructor a data family of the set
    * encodes with, by the constructor's native: a native fact naming one is
    * known to the set even with no entry in its natives, as the family
    * `jvm_int`'s constructor has none (`JvmIntFamily`), and its
    * define must take as many parameters as the constructor has fields. A
    * constructor whose field counts differ between the family's shape
    * parameters is a defect of the family.
    */
  private val codecConstructorFields: Map[NativeName, Int] =
    nativeBackend.families
      .flatMap(family => family.shapeParameters.flatMap(family.constructors(_)))
      .groupBy(_.native)
      .map((name, constructors) =>
        val counts = constructors.map(_.fields.size).distinct
        val single = counts match
          case Vector(count) => count
          case other         => throw IllegalStateException(s"the constructor $name has the field counts $other")
        name -> single
      )

  private def specializationCodecChecked(specialization: BackendSpecialization): Unit =
    if !hasCodec(specialization.representation) then
      malformed(
        BackendSetReason.Specialization(specialization.representation, SpecializationProblem.NoCodec)
      )

  /** The lists' constructors, the framework's list codec's: nil and cons
    * at their positions.
    */
  private val listConstructors: Vector[NativeName] = listConstructorsOf(Representation.listFamily)

  /** The array lists' constructors, the framework's array list codec's: the
    * lists' nil and cons, at the same positions.
    */
  private val arrayListConstructors: Vector[NativeName] = listConstructorsOf(Representation.arrayListFamily)

  private def listConstructorsOf(family: FamilyIdentity): Vector[NativeName] =
    Vector(ListConstructor.Nil, ListConstructor.Cons).map(constructor => NativeName.Constructor(family, ListCodec.position(constructor)))

  /** The constructors each codec encodes with, in the order of the set's
    * data families and then the lists'.
    */
  private val codecNatives: Vector[NativeName] = nativeBackend.constructorNatives ++ listConstructors ++ arrayListConstructors

  /** The terms bound to the codec's constructor: at its position in the
    * `data_family` declarations of the terms specialized to its family. Each
    * once, in the order of the knowledge. Throws `IllegalStateException` for
    * a constructor named by a string, which no codec has ([[FamilyIdentity]]).
    */
  private def boundTerms(specializations: Vector[BackendSpecialization], constructor: NativeName): Vector[Pure] =
    constructor match
      case NativeName.Function(name) => throw IllegalStateException(s"a codec's constructor named by the string $name")
      case NativeName.Constructor(family, position) =>
        specializations
          .filter(specialization => FamilyIdentity.Codec(specialization.representation) == family)
          .flatMap(_.families)
          .flatMap(_.constructors.lift(position))
          .distinct

  private def codecNativesChecked(specializations: Vector[BackendSpecialization]): Unit =
    codecNatives.foreach(codecNative =>
      val terms = boundTerms(specializations, codecNative)
      if terms.size > 1 then malformed(BackendSetReason.CodecNative(codecNative, terms))
    )

  /** The codec's constructors, every one named by its family and position,
    * with the codec's number of criterion parameters; `None` for a
    * representation with no codec. Throws `IllegalStateException` for a codec
    * whose constructors are not its family's positions 0, 1, … in order, a
    * defect of the codec ([[FamilyIdentity]]).
    */
  private def declaredConstructors(representation: String): Option[(Int, Vector[NativeName])] =
    if representation == Representation.listFamily.name then Some((1, listConstructors))
    else if representation == Representation.arrayListFamily.name then Some((1, arrayListConstructors))
    else
      nativeBackend.family(FamilyIdentity.Codec(representation)).map(family =>
        val constructors = family.shapeParameters.flatMap(family.constructors(_).map(_.native)).distinct
        val positions = constructors.indices.toVector.map(NativeName.Constructor(family.identity, _))
        if constructors != positions then
          throw IllegalStateException(s"the constructors of ${family.identity.shown} are not its positions: $constructors")
        (family.criterionArity, constructors)
      )

  private def specializationRepresentationChecked(specialization: BackendSpecialization): Unit =
    def rejected(problem: SpecializationProblem): Nothing =
      malformed(BackendSetReason.Specialization(specialization.representation, problem))
    declaredConstructors(specialization.representation).foreach((arity, constructors) =>
      if specialization.families.isEmpty then rejected(SpecializationProblem.DataFamilyMissing)
      specialization.families
        .find(family => family.arity != arity || family.constructors.size != constructors.size)
        .foreach(family => rejected(SpecializationProblem.DataFamilyIllShaped(family, arity, constructors.size)))
    )
    def bound(native: NativeName): Configured[NoFacts.type] = native match
      case NativeName.Constructor(_, position) =>
        noFactsTerm(specialization.families.flatMap(_.constructors.lift(position)).headOption.getOrElse(
          throw IllegalStateException(s"a data_family of ${specialization.representation} with no constructor $position passed its check")
        ))
      case NativeName.Function(name) => throw IllegalStateException(s"a codec's constructor named by the string $name")
    val shape: Shape[Any] =
      if specialization.representation == Representation.listFamily.name then
        listConstructors.map(bound) match
          case Vector(nil, cons) => ListCodec.constructorsShape(nil, cons)
          case other             => throw IllegalStateException(s"the list's constructors bound to ${other.size} terms")
      else if specialization.representation == Representation.arrayListFamily.name then
        arrayListConstructors.map(bound) match
          case Vector(nil, cons) => ListCodec.constructorsShape(nil, cons)
          case other             => throw IllegalStateException(s"the array list's constructors bound to ${other.size} terms")
      else
        nativeBackend.family(FamilyIdentity.Codec(specialization.representation)) match
          case Some(family) =>
            family.shapeParameters.foldLeft(Shape.Fits: Shape[Any])((found, parameter) =>
              if found != Shape.Fits then found
              else family.constructorsShape(parameter, family.constructors(parameter).map(constructor => bound(constructor.native)))
            )
          case None =>
            throw IllegalStateException(
              s"a representation with no codec passed the codec check: ${specialization.representation}"
            )
    if shape != Shape.Fits then
      malformed(
        BackendSetReason.Specialization(
          specialization.representation,
          SpecializationProblem.NotOfTheShape(shape)
        )
      )

  /** What a head of the define, applied to fresh values, shows before each
    * of the parameters: a lambda for each, or not.
    */
  private enum Taken:
    case Lambda
    case NoLambda

  /** The define takes the native's parameters: every head of its value
    * under tabling(weak_head), and of each such head applied to a fresh
    * neutral value, is a lambda before each of the applications; a native of
    * no parameter needs no check. Within `parameterStepLimit` steps.
    */
  private def parametersChecked(native: BackendNative, count: Int): Unit =
    if count > 0 then
      headsTaken(Value.of(noFactsTerm(native.instruction)), count).collected
        .result(ReadingState.fresh(BackendChecks.parameterStepLimit, ReadingConfiguration.withoutFacts)) match
        case Computed.Stopped(_) =>
          malformed(BackendSetReason.NativeParametersNotRead(native.native, count))
        case Computed.Done(taken, _) =>
          if taken.contains(Taken.NoLambda) then
            malformed(BackendSetReason.NativeParameters(native.native, count))

  private def headsTaken(term: Value[NoFacts.type], count: Int): Answers[ReadingState[NoFacts.type], Taken] =
    WeakHead.heads(Mode.TablingWeakHead, term).flatMap(set =>
      set.view(NoFacts) match
        case ParallelView.Single(head @ Head.Lambda(_, _, _)) =>
          if count == 1 then Answers.single(Taken.Lambda)
          else headsTaken(Value.Apply(head.value, NeutralValue[NoFacts.type](NativeParameter(count), Vector.empty)), count - 1)
        case _ => Answers.single(Taken.NoLambda)
    )

/** The checks under the standard set (`NativeBackend.standard`), the ones a
  * library compiled for the JIT's default facts is checked with.
  */
object BackendChecks extends LibraryBackend:

  private val standard = BackendChecks(NativeBackend.standard)

  def checked(
      natives: Vector[BackendNative],
      specializations: Vector[BackendSpecialization]
  ): Unit = standard.checked(natives, specializations)

  /** The steps the check of a native's parameters may take: the Prolog check
    * read within 100,000 inferences and measured 2,866 on concrete_types'
    * successor (one parameter); a step is a coarser unit than an inference,
    * so the same number bounds it at least as loosely.
    *
    * FIXME: the check of a native's parameters reads on a https://github.com/Atry/private-overlay/issues/2036
    * reading path of its own (`WeakHead.heads(Mode.TablingWeakHead, ...)` from `ReadingState.fresh`, while other
    * readers start from `ReadingState.knowingTop`), within this fixed budget, which decides whether a native set is
    * accepted. The reading and its budget are to become options of one interface chosen by configuration (entry data
    * and `Defaults`).
    */
  val parameterStepLimit: Long = 100000
