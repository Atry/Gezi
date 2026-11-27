package gezi.jit

import gezi.weakhead.Codecs
import gezi.weakhead.Computed
import gezi.weakhead.EvaluationError
import gezi.weakhead.EvaluationErrorReason
import gezi.weakhead.Head
import gezi.weakhead.ListCodec
import gezi.weakhead.ListConstructor
import gezi.weakhead.Mode
import gezi.weakhead.ParallelView
import gezi.weakhead.ReadingState
import gezi.ir.Value
import gezi.weakhead.WeakHead
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Pure}

/** The backend's facts of a compiled library, read from its index (jit.pl, THE
  * BACKEND'S REPRESENTATIONS) under a set of natives and families: which
  * defines are bound to natives of the set, which defines carry
  * `native_specialization(Family)` of a family the set or the framework has a
  * codec for, the defines the codecs encode with and the backend's constants.
  * Every fact is a backend fact of the index, read by the instruction of a
  * define; nothing is chosen by a name, and nothing here is a type
  * (`CONTRIBUTING.md`, "Types live only in the term"). Natives of another
  * backend's set, whose implementations the set does not hold, are no natives
  * of this backend, and a representation of another backend makes no decode
  * point.
  *
  * @param index
  *   the library's index
  * @param nativeBackend
  *   the natives and the data families the JIT runs; the JIT reads them through
  *   these facts only
  */
final case class BackendFacts(
    index: StandardLibraryIndex[NoFacts.type],
    nativeBackend: NativeBackend = NativeBackend.standard
):

  /** The library terms bound to natives (`BackendFacts.bindings`). */
  private lazy val bindings: Vector[NativeBinding] =
    BackendFacts.bindings(index, nativeBackend)

  /** The natives of the set bound to each define, in the order of the bindings
    * (prolog_native/3).
    */
  val natives: Map[Pure, Vector[BoundNative]] =
    bindings
      .filter(bound => nativeBackend.natives.contains(bound.native))
      .groupBy(_.instruction)
      .map((instruction, bound) =>
        instruction -> bound.map(found =>
          BoundNative(
            found.native,
            nativeBackend.natives(found.native).parameterCount
          )
        )
      )

  /** The family each criterion names: a criterion of a family the backend
    * declares by facts (`DeclaredFamily`) names that family, its own term
    * (`FamilyIdentity.Declared`); any other define with a
    * `native_specialization` names the codec of its first one, the one the
    * Prolog JIT's if-then-else committed to (`FamilyIdentity.Codec`), whether
    * or not the backend has a codec for it.
    */
  val criterionFamily: Map[Pure, FamilyIdentity] =
    val specialized = index.combinatorProperties
      .collect {
        case found @ gezi.standardlibrary.CombinatorProperty(
              _,
              Property.NativeSpecialization(name)
            ) =>
          found.instruction -> name
      }
      .foldLeft(Map.empty[Pure, FamilyIdentity]) {
        case (found, (instruction, name)) =>
          if found.contains(instruction) then found
          else found.updated(instruction, FamilyIdentity.Codec(name))
      }
    specialized ++ nativeBackend.families.collect {
      case declared: DeclaredFamily => declared.criterion -> declared.identity
    }

  /** The first native of at least one parameter bound to the define.
    *
    * FIXME (carried from jit.pl:1674): an instruction bound
    * https://github.com/Atry/private-overlay/issues/1927 to several natives, as
    * one instruction is when equal bodies make two files one (the native
    * route's zero and true, the constructors 0 of big_integer and of boolean),
    * is resolved by its result's representation only where `JitRules`' native
    * values, type-filtered constructors and the backend's constants read it;
    * the head of the define takes the first native of at least one parameter
    * the index gives. No library binds two natives of a parameter to one
    * instruction, so neither is reached; one that did would run each
    * application by the first native. Candidate: choose by the representation
    * the reading asks for, as the native values do.
    */
  def nativeOfParameters(instruction: Pure): Option[BoundNative] =
    natives.getOrElse(instruction, Vector.empty).find(_.parameterCount > 0)

  /** Whether some native of the set is bound to the define. */
  def bound(instruction: Pure): Boolean = natives.contains(instruction)

  /** Whether the enabled library declares the family: a native specialization
    * of a codec the set or the framework has, which the library compiler's
    * check of the codec's shape then covered (shape_checked_representation/1),
    * or a family declared by facts of the set with `jvm_type(generic)` on its
    * criterion, whose shape `DeclaredFamilies.extended` checked.
    */
  def shapeChecked(family: FamilyIdentity): Boolean =
    shapeCheckedFamilies.contains(family)

  private val shapeCheckedFamilies: Set[FamilyIdentity] =
    (nativeBackend.families.map(_.identity) :+ Representation.listFamily).toSet
      .filter {
        case FamilyIdentity.Codec(name) =>
          index.combinatorProperties.exists(
            _.property == Property.NativeSpecialization(name)
          )
        case FamilyIdentity.Declared(criterion) =>
          index.combinatorProperties.contains(
            gezi.standardlibrary.CombinatorProperty(
              criterion,
              Property.JvmType(gezi.standardlibrary.JvmTypeName.Generic)
            )
          )
      }

  /** The leaves of the index (`StandardLibraryIndex.noinline`), which the
    * refinement keeps as written: noinline is what keeps a term unexpanded when
    * the library is files reached by paths.
    */
  val leaves: Set[Pure] = index.withProperty(Property.Noinline).toSet

  /** The instruction of the first define with `native_specialization(list)`,
    * the function of a list's decoding criterion (list_criterion/2).
    */
  lazy val listType: Pure =
    index
      .withProperty(
        Property.NativeSpecialization(Representation.listFamily.name)
      )
      .headOption
      .getOrElse(
        throw IllegalStateException(
          "no define of the library has native_specialization(list)"
        )
      )

  /** The library terms bound to each native, a constructor's among them. */
  lazy val definesBound: Map[NativeName, Vector[Pure]] =
    bindings
      .groupBy(_.native)
      .map((native, bound) => native -> bound.map(_.instruction).distinct)

  /** The term bound to the native, when exactly one is: the decoding of a
    * parameter by its syntax (`Jit.decodingCriterion`) reads a constructor's
    * term this way and finds no parameter where the library binds none.
    */
  def boundDefine(native: NativeName): Option[Pure] =
    definesBound.get(native) match
      case Some(Vector(instruction)) => Some(instruction)
      case _                         => None

  private lazy val nativeBoundDefines: Set[Pure] =
    definesBound.values.flatten.toSet

  /** Whether the term is bound to a native. */
  def isBoundToNative(instruction: Pure): Boolean =
    nativeBoundDefines.contains(instruction)

  /** The term bound to the native, which a codec encodes a constructor with:
    * for a codec's constructor, the term at its position in the `data_family`
    * of the types specialized to its family. Throws `EvaluationError` with
    * `CodecConstructor` unless exactly one term is bound, a defect of the
    * library compiler, which admits one term at each position of a codec's
    * constructors (`BackendChecks`) and a `data_family` on every type
    * specialized to a codec's family.
    */
  def constructorDefine(native: NativeName): Pure =
    definesBound.get(native) match
      case Some(Vector(instruction)) => instruction
      case found                     =>
        throw EvaluationError(
          EvaluationErrorReason.CodecConstructor(
            native.toString,
            found.getOrElse(Vector.empty)
          )
        )

  /** The terms the storages of these facts encode their values with. */
  lazy val storageEncoding: StorageEncoding = StorageEncoding(this)

  /** The term of nil, the list's constructor 0. */
  lazy val nil: Pure =
    constructorDefine(
      NativeName.Constructor(
        Representation.listFamily,
        ListCodec.position(ListConstructor.Nil)
      )
    )

  /** The term of cons, the list's constructor 1. */
  lazy val cons: Pure =
    constructorDefine(
      NativeName.Constructor(
        Representation.listFamily,
        ListCodec.position(ListConstructor.Cons)
      )
    )

  /** The heads of the backend's constants (native_constants/3): for each define
    * bound to a native of no parameter, the head of the define, a thunk with no
    * filling, with the native and its result's place; each configuration
    * computes the native's value in its own `C`
    * (`StorageEncodingOperations.constants`). The head of `\z. \s. z`, zero's
    * define, is also the head of true's, so one head stands for 0 in
    * big_integer and for true in boolean. The head is read by the reference
    * evaluator from the define's layer, within `constantStepLimit` steps; the
    * Prolog JIT read it by its own rules, which on a define bound to a native
    * of no parameter are the reference's (its head is its define's own). A
    * native whose result's place is at the call's parameter
    * (`NativePlace.Parameter`) has its constant at its constant's parameter
    * (`Native.constantParameter`): `word_end`'s is at width 0. Computed once
    * for the library, a table of the backend's facts and nothing about a
    * program. The constructors of the families declared by facts give no
    * constant (only the codecs of the set and the framework and the `native`
    * bindings do): a constant is a head that stands for a value wherever it is
    * met, and a declared constructor's head may be one instruction with another
    * family's, so its family is read only from a filter (`DeclaredFamilies`).
    */
  lazy val constantHeads: Vector[ConstantHead] =
    // A constant's define is a pure key, read under no facts, its own spelling there.
    given NoFacts.type = NoFacts
    bindings
      .filterNot(declaredFamilyConstructor)
      .flatMap(bound =>
        nativeBackend.natives
          .get(bound.native)
          .filter(_.parameterCount == 0)
          .flatMap(native =>
            val place = native.result match
              case NativePlace.Parameter(family) =>
                val parameter = native.constantParameter
                  .getOrElse(
                    throw IllegalStateException(
                      s"${bound.native}, of no operand, gives no constant's parameter"
                    )
                  )
                NativePlace.Fixed(Representation.Data(family, parameter))
              case other => other
            WeakHead
              .heads(
                Mode.TablingWeakHead,
                Value.of(Configured.fromPure(NoFacts)(bound.instruction))
              )
              .pull
              .result(
                ReadingState.fresh(
                  BackendFacts.constantStepLimit,
                  gezi.weakhead.ReadingConfiguration.withoutFacts
                )
              ) match
              case Computed.Done(Some((set, _)), _) =>
                set.view(NoFacts) match
                  case ParallelView.Single(Head.Lambda(code, holes, fillings))
                      if fillings.isEmpty =>
                    Some(ConstantHead(code, holes, native, place))
                  case _ => None
              case _ => None
          )
      )

  /** Whether the binding is of a constructor of a family declared by facts
    * (`DeclaredFamily`).
    */
  private def declaredFamilyConstructor(binding: NativeBinding): Boolean =
    binding.native match
      case NativeName.Constructor(family, _) =>
        nativeBackend.family(family) match
          case Some(_: DeclaredFamily) => true
          case _                       => false
      case NativeName.Function(_) => false

/** A library term bound to a native: by a `native` declaration, a function
  * named by its string; or as the constructor at a position of the
  * `data_family` of a type whose `native_specialization` names a codec's
  * family, or of a family declared by facts, the constructor named by the
  * family's identity and the position.
  */
final case class NativeBinding(instruction: Pure, native: NativeName)

/** The head of a backend constant, read from the facts: the head of a define
  * bound to a native of no parameter, `\z. \s. z` as its code and holes, the
  * native, and the place of the native's result.
  */
final case class ConstantHead(
    code: Code,
    holes: Vector[Hole],
    native: Native,
    place: NativePlace
)

/** A backend constant in a configuration: its head, the native's value there,
  * and the place of the native's result.
  */
final case class BackendConstant[+Term](
    code: Code,
    holes: Vector[Hole],
    value: NativeValue[Term],
    place: NativePlace
)

/** The facts of a compiled library. */
object BackendFacts:

  /** The facts of the compiled library under the standard set. */
  def of(library: StandardLibrary): BackendFacts =
    of(library, NativeBackend.standard)

  /** The facts of the compiled library under the set of natives and families.
    */
  def of(library: StandardLibrary, nativeBackend: NativeBackend): BackendFacts =
    BackendFacts(
      library.index,
      DeclaredFamilies.extended(library.index, nativeBackend)
    )

  /** The library terms bound to natives under the set, each once, in this
    * order: the constructors of the codecs' families the set holds, other than
    * those declared by facts, and of the framework's lists; the index's
    * `native` bindings, each a function named by its string; and the
    * constructors of the families declared by facts (`DeclaredFamily`) the set
    * holds. A codec's constructor is the term at its position in a
    * `data_family` of a type whose first `native_specialization` names the
    * family (`Codecs.declaredConstructors`), and a declared family's the term
    * at its position in the `data_family` of the family's criterion
    * (`DeclaredFamilies.constructorTerms`), named by the family's identity and
    * the position (`NativeName.Constructor`): never by a string of its own, and
    * never by its term alone ([[FamilyIdentity]]).
    */
  def bindings(
      index: StandardLibraryIndex[?],
      nativeBackend: NativeBackend
  ): Vector[NativeBinding] =
    def constructorBindings(
        family: FamilyIdentity,
        terms: Vector[Pure]
    ): Vector[NativeBinding] =
      terms.zipWithIndex.map((term, position) =>
        NativeBinding(term, NativeName.Constructor(family, position))
      )
    val codecs = Codecs
      .declaredConstructors(index)
      .map((name, terms) => (FamilyIdentity.Codec(name), terms))
      .collect {
        case (family, terms)
            if family == Representation.listFamily || nativeBackend
              .family(family)
              .isDefined =>
          constructorBindings(family, terms)
      }
    val declared = DeclaredFamilies.constructorTerms(index).collect {
      case (family, terms) if nativeBackend.family(family).isDefined =>
        constructorBindings(family, terms)
    }
    val functions = index.nativeBound.map(bound =>
      NativeBinding(bound.instruction, NativeName.Function(bound.native))
    )
    (codecs.flatten ++ functions ++ declared.flatten).distinct

  /** The steps the head of a constant's define may take: the defines bound to
    * natives of no parameter are thunks, read in one step.
    *
    * FIXME: `constants` reads on a reading path of its own
    * https://github.com/Atry/private-overlay/issues/2036
    * (`WeakHead.heads(Mode.TablingWeakHead, ...)` from `ReadingState.fresh`,
    * while other readers start from `ReadingState.knowingTop`), within this
    * fixed budget, which decides which constants the backend knows. The reading
    * and its budget are to become options of one interface chosen by
    * configuration (entry data and `Defaults`).
    */
  val constantStepLimit: Long = 1000
