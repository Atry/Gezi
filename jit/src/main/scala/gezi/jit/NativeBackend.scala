package gezi.jit

import gezi.weakhead.BigIntegerCodec
import gezi.weakhead.BooleanCodec
import gezi.weakhead.CaseReadings
import gezi.weakhead.Codecs
import gezi.weakhead.Decoding
import gezi.weakhead.Head
import gezi.weakhead.ListCodec
import gezi.weakhead.ListConstructor
import gezi.weakhead.ListRepresentation
import gezi.weakhead.ListTail
import gezi.weakhead.NaturalConstructor
import gezi.weakhead.NeutralVariable
import gezi.weakhead.Shape
import gezi.weakhead.Value
import gezi.ir.Instruction

/** The place of a native's parameter or result in its calling convention,
  * before a list's element filter is known (jit.pl, THE NATIVE'S
  * REPRESENTATIONS): a representation of a data family, any list, a list's
  * item in the representation of the list's element filter, or a list's
  * tail, ready in the list's representation and kept unread.
  *
  * A data family that takes a parameter (`DataFamily.parameterFamily`) has
  * one representation per parameter, and a native over it may have places
  * that vary with one parameter per call, the parameter of its result:
  * `Parameter` is the result's place, the family at the call's parameter,
  * and `OfParameter` an operand's, a representation that is a function of
  * it, as a constructor's field takes its representation from its layer's
  * parameter (`DataField`).
  * The call's parameter is the parameter of a representation a licensed
  * source names: the decoding criterion written in the term, read where a
  * decoding point is read (`Native.parameterAdmitted`), or the operands'
  * native values (`Native.resultParameter`).
  */
enum NativePlace:
  case Fixed(representation: Representation)
  case AnyList
  case Item
  case Tail
  case Parameter(family: FamilyIdentity)
  case OfParameter(representation: Option[NativeValue] => Representation)

  /** A parameter that is a list whose elements are all decoded binary
    * naturals of the representation `element`, a backend fact of the native's
    * binding, written here and never inferred from a term. Only a narrow block
    * with lists (`gezi.narrowblocks.lists`) passes one, the elements of the
    * `NarrowList` that the filter `∥ list_type c` written in the term licensed,
    * as a `scala.collection.immutable.Vector` of `java.math.BigInteger`, and
    * only when `c` names exactly `element`, so that a list of positive naturals
    * under `list_type (binary_set false)` is refused at `NaturalList(canonical)`;
    * otherwise the call is left to the general reading. The JIT holds a list's items unevaluated, so it is never ready at
    * this place and runs the define's body, and a block without lists does not
    * compile a call of such a native.
    */
  case NaturalList(element: Representation)

/** The name of a native implementation, the key of `NativeBackend.natives`.
  *
  * A FUNCTION is named by the string a knowledge file's `native` declaration
  * gives (`natural_double`, `wren_binary_plus`). A CONSTRUCTOR of
  * a data family is named by the family's identity (`FamilyIdentity`: a
  * codec's name, the string the `native_specialization` of its type names,
  * or a declared family's criterion) and its position in its type's
  * `data_family`; the term at that position is the constructor's, bound by
  * `BackendFacts` and never by a `native` declaration. A constructor is
  * never named by a string of its own, and never by its term alone:
  * α-equivalent library files such as zero, true and nil are one instruction
  * ([[FamilyIdentity]]). The codecs' names themselves stay an open set.
  */
enum NativeName:
  case Function(name: String)
  case Constructor(family: FamilyIdentity, position: Int)

/** A native implementation: the place of each parameter in order, the place
  * of its result, and the function from the values at the parameters' places
  * to the value at the result's. A knowledge module binds a function to a
  * library term with `native(Term, Name)`, and a codec's constructor is
  * bound by its type's `data_family` (`NativeName`), the name the key of
  * `NativeBackend.natives`. Each native is its define applied to its
  * parameters, by the meaning of the values alone (the module comment of
  * `gezi/prolog/gezi/prolog_backend_natives.pl`, WHY EACH NATIVE
  * IS RIGHT).
  *
  * A native never checks its operand (`CONTRIBUTING.md`, "Types live only in the term"): the JIT calls it
  * only with values of its places, decoded from operands whose terms carry
  * the assertion, and another value is a defect of the caller, on which the
  * implementation's match throws.
  *
  * A native whose result's place is `NativePlace.Parameter` has two more
  * parts, both part of computing its result and of nothing else:
  * `parameterAdmitted`, whether the native gives a value at the parameter a
  * decoding criterion names (a constructor that is not one of its family's
  * at that parameter, or is excluded there, does not); and
  * `resultParameter`, the parameter of its result computed from its
  * operands' native values, `None` when they are no layer of the family.
  * `resultParameter` is applied only to operands already represented, after
  * the `native` declaration and the operands' readiness have chosen to call
  * the native: it never reads a term that is not represented to conclude
  * what the term is, which would be a signature typing a node
  * (`CONTRIBUTING.md`, "Types live only in the term"), and it never chooses a route or an
  * evaluator.
  *
  * FIXME (the interface review of 2026-11-03): `resultParameter` https://github.com/Atry/private-overlay/issues/1936
  * is to be replaced by type-preservation lemmas that write the result's
  * criterion into the term; see the FIXME at `Jit.parameterisedReady`.
  */
final case class Native(
    parameters: Vector[NativePlace],
    result: NativePlace,
    implementation: Vector[NativeArgument] => NativeValue,
    parameterAdmitted: Option[NativeValue] => Boolean = _ => true,
    resultParameter: Vector[NativeValue] => Option[Option[NativeValue]] = _ => None
):

  /** The number of the native's parameters. */
  def parameterCount: Int = parameters.size

  /** Whether one of the native's parameters is a `NativePlace.NaturalList`. */
  def takesNaturalList: Boolean = parameters.exists {
    case NativePlace.NaturalList(_) => true
    case _                          => false
  }

/** What every native's implementation may rely on. */
object Native:

  /** The end of an implementation's match on its arguments, for arguments
    * the JIT never passes: it calls a native only with one argument for each
    * of its parameters, each read at the parameter's place (`Jit`'s
    * `argumentOutcome`): a value of the place's representation
    * (`NativeArgument.Represented`), a list's item (`NativeArgument.Item`) or
    * a list's tail (`NativeArgument.Tail`), and a native with no parameter
    * with none. Arguments outside that are a defect of the caller.
    */
  def outsidePlaces(native: String, arguments: Vector[NativeArgument]): Nothing =
    throw IllegalStateException(s"the native $native was called with $arguments, not one argument of each parameter's place")

/** A constructor of a data family: the name of the native implementation
  * whose bound term the codec encodes the constructor with, and the field
  * of each of its fields, in order. The name is the family's representation
  * and the constructor's position (`NativeName.Constructor`) for a family
  * whose type declares its constructors by `data_family`.
  */
final case class DataConstructor(native: NativeName, fields: Vector[DataField])

/** A field of a data family's constructor: its representation as a
  * function of the parameter of the layer it is a field of.
  * For a family whose
  * parameter is a value, the field's family at a parameter in that family
  * (`DataField.apply`); for a family declared by facts whose parameters are
  * criteria (`NativeValue.CriterionParameters`), the representation one of
  * those criteria names (`DeclaredFamilies`).
  */
final case class DataField(representation: Option[NativeValue] => Representation)

/** The fields of the families of value parameters. */
object DataField:

  /** A field of the family at its parameter, a function of the layer's:
    * `None` for a family that takes none.
    */
  def apply(family: FamilyIdentity, parameter: Option[NativeValue] => Option[NativeValue]): DataField =
    DataField(layerParameter => Representation.Data(family, parameter(layerParameter)))

  /** A field of the family, which takes no parameter. */
  def unparameterised(family: FamilyIdentity): DataField = DataField(family, _ => None)

/** One layer of a value of a data family: the index of its constructor in
  * the family's order and the values of its fields.
  */
final case class DataLayer(constructor: Int, fields: Vector[NativeValue])

/** The case of a constructor a value is applied to in a decoding of a data
  * family: the decoding, the field depth, the family and the constructor's
  * index; a neutral value no closed program can name.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class DataCase(decoding: Decoding, level: Int, family: FamilyIdentity, constructor: Int) extends NeutralVariable

/** The variable standing for one field of one constructor in the check of a
  * data family's constructors: the family, the constructor's index and the
  * field's.
  *
  * A neutral value, a free variable (`CONTRIBUTING.md`, "Types live only in the term"), kept as an exception argued here:
  * it stands for a
  * binder of the value read (a Scott value's handler, a constructor's or a
  * define's parameter), opened to read the value's head, as the normal-form
  * reader's `BoundVariable` opens a lambda, whose Scaladoc has the argument.
  * A closed term in its place would not do: a term that is no such value
  * could ignore it and build the reading itself.
  */
final case class FieldVariable(family: FamilyIdentity, constructor: Int, field: Int) extends NeutralVariable

/** What a head of a value applied to a decoding's cases reads: the case of
  * a constructor over its arguments, or no case.
  */
enum DataReading:
  case Case(constructor: Int, arguments: Vector[Value])
  case NoCase

/** A family of representations, Scott encoded: a value of the family is a
  * term of as many cases as the encoding has constructors (`constructors`
  * gives every one of them, in the order of the cases, at every parameter),
  * which, applied to the cases, answers the case of its constructor applied
  * to its fields. A constructor may be EXCLUDED at a parameter
  * (`excluded`): its case is still one of the cases, and a head that
  * answers it reads no value there. The family's identity is a codec's name,
  * the one `native_specialization(Family)` gives, or a declared family's
  * criterion (`FamilyIdentity`); how the family holds a value is the class of `NativeValue` that `built`
  * gives and `taken` reads, which the family defines.
  *
  * THE PARAMETER: a family
  * may take a parameter, a value of the family `parameterFamily`, which
  * decides its constructors at a layer and its fields' parameters; a family
  * whose values' layers are told apart by their cases takes none
  * (`parameterFamily` is `None`, and every parameter it is given is `None`).
  * The parameter is read from the decoding criterion `F P` the term carries,
  * P decoded in `parameterFamily`, never from the value.
  *
  * The JIT drives the codec by evaluation, the same way for every data
  * family: DECODING applies a value to one `DataCase` per constructor at the
  * parameter, reads each head as a case over its arguments, decodes each
  * argument one level deeper in its field's family at its field's parameter,
  * under the same decoding, and gives the values to `built`; ENCODING takes
  * the layer `taken` gives and applies the define bound to the constructor's
  * native to the fields; ELIMINATION chooses the constructor's branch among
  * the cases. The codec reads no description of a type and decides no type:
  * it reads the heads a value applied to its own cases answers.
  */
trait DataFamily:

  /** The family's identity. */
  def identity: FamilyIdentity

  /** The family of the parameter, or `None` when the family takes none. */
  def parameterFamily: Option[FamilyIdentity]

  /** The number of criteria the family's criterion is applied to in a
    * filter, `C @ P1 @ … @ Pk`, for a family declared by facts whose
    * parameters are criteria (`NativeValue.CriterionParameters`); 0 for
    * every other family.
    */
  def criterionArity: Int = 0

  /** Whether a position of this family holds its term as it is written,
    * unevaluated (`NativeValue.Unread`), because the family's criterion is a
    * least term of ⊑_O and a filter by it leaves the term as it is. Such a
    * family has no constructor and no value of it is a head. False by default.
    */
  def heldAsWritten: Boolean = false

  /** The constructors at the parameter, in the order of the cases. */
  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor]

  /** Whether the constructor of the index is excluded at the parameter: the
    * type the family specializes has no value of that constructor there, so
    * a head that answers its case reads no value, as a head that answers no
    * case does. A trusted backend fact about the representation, like the
    * rest of a native specialization, made safe by the family's law against
    * weak_head. `taken` never gives an excluded layer. None by default.
    */
  def excluded(parameter: Option[NativeValue], constructor: Int): Boolean = false

  /** The value of one layer at the parameter, whose fields are decoded. */
  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue

  /** The layer of a value of the family at the parameter. */
  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer

  /** The parameter at which the constructor whose native is named, over
    * the fields' values, is a layer, or `None` when it is no layer at any
    * parameter: the result's parameter of the constructor's native
    * (`Native.resultParameter`). A family that takes no parameter answers
    * `Some(None)`; one that takes a parameter overrides it.
    */
  def builtParameter(native: NativeName, fields: Vector[NativeValue]): Option[Option[NativeValue]] =
    if parameterFamily.isEmpty then Some(None) else None

  /** `taken`, checked: the layer is of a constructor not excluded at the
    * parameter, or the family is defective and this throws.
    */
  final def layer(parameter: Option[NativeValue], value: NativeValue): DataLayer =
    val found = taken(parameter, value)
    if excluded(parameter, found.constructor) then
      throw IllegalStateException(s"${identity.shown} took a layer of the constructor ${found.constructor}, excluded at $parameter")
    found

  /** The parameters the check of the constructors reads them at: `None`
    * alone for a family that takes no parameter. A family that takes one
    * gives parameters at which every constructor appears.
    */
  def shapeParameters: Vector[Option[NativeValue]] = Vector(None)

  /** The cases of the decoding at the field depth, one per constructor at
    * the parameter.
    */
  final def decodingCases(decoding: Decoding, level: Int, parameter: Option[NativeValue]): Vector[Value] =
    constructors(parameter).indices.toVector.map(index => Value.Neutral(DataCase(decoding, level, identity, index), Vector.empty))

  /** What a head of a value applied to the decoding's cases at the level
    * reads.
    */
  final def caseReading(head: Head, decoding: Decoding, level: Int): DataReading = head match
    case Head.Neutral(DataCase(`decoding`, `level`, family, constructor), arguments) if family == identity =>
      DataReading.Case(constructor, arguments)
    case _ => DataReading.NoCase

  /** Whether the defines bound to the constructors' natives at the
    * parameter, in the order of those constructors, have the assumed shape,
    * read under weak_head: every head of each define applied to fresh fields
    * and then to the cases reads the define's own case over those fields,
    * with at least one head. The readings are compared constructor by
    * constructor: `Shape.Fits` when every one fits; otherwise, for the first
    * constructor that does not, `Shape.Unfit` with the readings found and
    * the one reading the shape asks, or `Shape.LimitReached` when its
    * reading ran past the budget, with the reading asked. Each reading within
    * `Codecs.shapeStepLimit` steps. A family whose codec reports readings of
    * its own overrides it.
    */
  def constructorsShape(parameter: Option[NativeValue], defines: Vector[Instruction]): Shape[Any] =
    val atParameter = constructors(parameter)
    require(defines.size == atParameter.size, s"${defines.size} defines for the ${atParameter.size} constructors of ${identity.shown}")
    val cases = decodingCases(Decoding.Shape, 0, parameter)
    val compared = atParameter.indices.toVector.map(index =>
      val fields = atParameter(index).fields.indices.toVector.map(field =>
        Value.Neutral(FieldVariable(identity, index, field), Vector.empty)
      )
      val applied = (fields ++ cases).foldLeft(defines(index): Value)(Value.Apply(_, _))
      val expected = DataReading.Case(index, fields)
      (Codecs.readingsWithin(applied, DataReading.NoCase)(caseReading(_, Decoding.Shape, 0)), expected)
    )
    compared.find((found, expected) => found != CaseReadings.Read(Vector(expected))) match
      case None                                       => Shape.Fits
      case Some((CaseReadings.Read(found), expected)) => Shape.Unfit(found, Vector(expected))
      case Some((stopped, expected))                  => Shape.LimitReached(stopped, CaseReadings.Read(Vector(expected)))

/** The native implementations and the data families of a backend: the
  * value that maps the names the knowledge modules give (a function's in
  * `native(Term, Name)`, a codec family's in `native_specialization(Family)`,
  * a declared family's criterion, a constructor's the family's identity and
  * its position in `data_family`) to code.
  * It holds no type of any term: a type is an assertion in the term, and the
  * JIT decodes an operand only where the term carries it
  * (`CONTRIBUTING.md`, "Types live only in the term").
  *
  * The JIT reads it only through `BackendFacts.nativeBackend`, the library
  * compiler's checks through `BackendChecks`. The family of lists is not
  * one of it: it is the framework's (`Representation.ListOf`, `ListCodec`),
  * and a backend uses it by holding the natives of the list's two
  * constructors, `NativeName.Constructor(Codec(list), 0)` and `(Codec(list), 1)`.
  *
  * @param natives
  *   the natives, by their names
  * @param families
  *   the data families, their identities distinct
  */
final case class NativeBackend(natives: Map[NativeName, Native], families: Vector[DataFamily]):
  require(
    families.map(_.identity).distinct.size == families.size,
    s"two data families of one identity: ${families.map(_.identity.shown)}"
  )

  private val familiesByIdentity: Map[FamilyIdentity, DataFamily] = families.map(family => family.identity -> family).toMap

  /** The data family of the identity, if the backend has a codec for it. */
  def family(identity: FamilyIdentity): Option[DataFamily] = familiesByIdentity.get(identity)

  /** The natives that are the constructors of the data families, at every
    * parameter the families' check reads them at (`shapeParameters`, where
    * every constructor appears): a backend fact. A constructor's define
    * answers a lambda without reading its fields, so it is not strict in
    * them, and the JIT calls its native only on fields already written
    * represented (`Jit`'s `nativeAppliedHeads`). In the order of the
    * families; `BackendChecks` checks each against its binding.
    */
  lazy val constructorNatives: Vector[NativeName] =
    families.flatMap(family => family.shapeParameters.flatMap(family.constructors(_).map(_.native)).distinct)

  /** The backend with the natives and the families of `more` added, each of
    * `more` replacing the one of the same identity here.
    */
  def extended(more: NativeBackend): NativeBackend =
    NativeBackend(
      natives ++ more.natives,
      families.map(family => more.family(family.identity).getOrElse(family)) ++
        more.families.filterNot(family => familiesByIdentity.contains(family.identity))
    )

/** The standard set of natives and families. */
object NativeBackend:

  /** The standard set, the port of
    * `gezi/prolog/gezi/prolog_backend_natives.pl`: the families
    * `big_integer` and `boolean`, and the natives of the naturals, the
    * booleans and the lists; and the families `word` of the fixed-width
    * words (`WordFamily`) and `binary_natural` of the binary naturals
    * (`BinaryNaturalFamily`), which the Prolog set did not have. A library
    * whose facts and checks are given no set of their own is read with it.
    *
    * The constructors of the word and binary natural families, whose layers
    * depend on the family's parameter (a word's width, a binary natural's
    * set), are natives with places at the call's parameter
    * (`familyConstructorNatives`): `word_cell` takes a boolean and a word
    * of width w - 1 to a word of width w. The library binds them in
    * `fixed_width_prolog_backend` and `binary_prolog_backend`.
    *
    * THE PROLOG BACKEND'S SET IS THIS SET. The data names these natives and
    * families for the "Prolog backend": the knowledge modules
    * `prolog_backend`, `native_arithmetic_prolog_backend`,
    * `fixed_width_prolog_backend`, `binary_prolog_backend` and
    * `prolog_backend_shapes`, and the
    * backend set of the vocabulary
    * (`gezi.standardlibrary.CombinatorPropertyVocabulary`). The data is not
    * changed. The JVM reads that set as its own, since its arithmetic is the
    * same: the Prolog backend's `big_integer` is unbounded integers, and so
    * is `BigInt`; `boolean` is two atoms, here the two `Boolean`s; `list` is
    * Prolog lists of items, here `Vector`s of items. Each property's meaning
    * carries over to the JVM unchanged: `native_specialization(Family)` says
    * the define holds every value the family's codec decodes into, which
    * depends on the codec and not on the host; `first_order_constructor`
    * says the backend represents an application of the define to its fields
    * as a first-order term, which this backend reads nowhere, as the Prolog
    * JIT did not.
    *
    * TODO (carried from prolog_backend_natives.pl:109;
    * https://github.com/Atry/private-overlay/issues/1526): the test
    * of natural_double at the JIT's dispatch (tests/jit_shape_replacement.plt)
    * ran on the library of the old HM baseline and was deleted with it; it
    * comes back with the dispatch on the new HM baseline. It reads back with
    * `git show a66f8d948:lambda_jit/tests/jit_shape_replacement.plt`.
    */
  val standard: NativeBackend = NativeBackend(
    Map[NativeName, Native](
      NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Zero)) ->
        Native(Vector.empty, natural, {
          case Vector() => NativeValue.Natural(BigInt(0))
          case other    => Native.outsidePlaces("zero", other)
        }),
      NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Successor)) ->
        Native(Vector(natural), natural, {
          case Vector(NativeArgument.Represented(NativeValue.Natural(value))) => NativeValue.Natural(value + 1)
          case other                                                          => Native.outsidePlaces("successor", other)
        }),
      NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(true)) ->
        Native(Vector.empty, truth, {
          case Vector() => NativeValue.Truth(true)
          case other    => Native.outsidePlaces("true", other)
        }),
      NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(false)) ->
        Native(Vector.empty, truth, {
          case Vector() => NativeValue.Truth(false)
          case other    => Native.outsidePlaces("false", other)
        }),
      NativeName.Function("natural_double") ->
        Native(Vector(natural), natural, {
          case Vector(NativeArgument.Represented(NativeValue.Natural(value))) => NativeValue.Natural(value * 2)
          case other                                                          => Native.outsidePlaces("natural_double", other)
        }),
      NativeName.Function("natural_even") ->
        Native(Vector(natural), truth, {
          case Vector(NativeArgument.Represented(NativeValue.Natural(value))) => NativeValue.Truth(value % 2 == 0)
          case other                                                          => Native.outsidePlaces("natural_even", other)
        }),
      NativeName.Constructor(Representation.listFamily, ListCodec.position(ListConstructor.Nil)) ->
        Native(Vector.empty, NativePlace.AnyList, {
          case Vector() => NativeValue.Listed(ListRepresentation.Items(0, Vector.empty))
          case other    => Native.outsidePlaces("nil", other)
        }),
      NativeName.Constructor(Representation.listFamily, ListCodec.position(ListConstructor.Cons)) ->
        Native(Vector(NativePlace.Item, NativePlace.Tail), NativePlace.AnyList, {
          case Vector(NativeArgument.Item(item), NativeArgument.Tail(tail)) => NativeValue.Listed(listCons(item, tail))
          case other                                                         => Native.outsidePlaces("cons", other)
        })
    ) ++ familyConstructorNatives(WordFamily) ++ familyConstructorNatives(BinaryNaturalFamily) ++ BinaryNaturalNatives.operations.natives ++
      JvmBitsFamily.constructorNatives,
    Vector(BigIntegerFamily, BooleanFamily, WordFamily, BinaryNaturalFamily, UnreadFamily) ++ JvmBitsFamily.all
  )

  /** A backend of functions and families, each function named by the
    * string a knowledge file's `native` declaration gives
    * (`NativeName.Function`), as a natives project writes them.
    */
  def functions(natives: Map[String, Native], families: Vector[DataFamily]): NativeBackend =
    NativeBackend(natives.map((name, native) => NativeName.Function(name) -> native), families)

  /** The natives of a data family's constructors, by their names, read off
    * the family's own data: at a parameter, the constructor's fields'
    * places are its `DataField`s' families at their parameters, its result
    * the family at the parameter (`NativePlace.Parameter`); it is admitted
    * at a parameter where it is one of the family's constructors and not
    * excluded; its result's parameter is `DataFamily.builtParameter` of its
    * fields' values, and its value `DataFamily.built` at that parameter.
    * Each constructor's fields are those of the first parameter of
    * `shapeParameters` where it appears.
    */
  def familyConstructorNatives(family: DataFamily): Map[NativeName, Native] =
    family.shapeParameters
      .flatMap(parameter => family.constructors(parameter))
      .distinctBy(_.native)
      .map(constructor =>
        constructor.native -> Native(
          constructor.fields.map(field => NativePlace.OfParameter(field.representation)),
          NativePlace.Parameter(family.identity),
          arguments =>
            val values = arguments.map {
              case NativeArgument.Represented(value) => value
              case other => throw IllegalArgumentException(s"a field of ${constructor.native} that is not a native value: $other")
            }
            val parameter = family
              .builtParameter(constructor.native, values)
              .getOrElse(throw IllegalArgumentException(s"no layer of ${family.identity.shown} is ${constructor.native} over $values"))
            val index = constructorIndex(family, parameter, constructor.native)
              .getOrElse(throw IllegalArgumentException(s"${constructor.native} is no constructor of ${family.identity.shown} at $parameter"))
            family.built(parameter, DataLayer(index, values))
          ,
          parameter =>
            constructorIndex(family, parameter, constructor.native).exists(index => !family.excluded(parameter, index)),
          values => family.builtParameter(constructor.native, values)
        )
      )
      .toMap

  /** The index of the constructor whose native is named among the family's
    * constructors at the parameter, if it is one of them.
    */
  private def constructorIndex(family: DataFamily, parameter: Option[NativeValue], native: NativeName): Option[Int] =
    Some(family.constructors(parameter).indexWhere(_.native == native)).filter(_ >= 0)

  private def natural: NativePlace = NativePlace.Fixed(Representation.BigInteger)

  private def truth: NativePlace = NativePlace.Fixed(Representation.Truth)

  /** The library's cons of the item, as given, onto the tail (list_cons/3):
    * on a list of items, that list one item longer; on a cell or a term
    * nothing has read, a cell, so that the tail is read only where a
    * consumer of the list reads it.
    */
  private def listCons(item: JitValue, tail: ListTail[JitValue]): ListRepresentation[JitValue] =
    tail match
      case ListTail.Listed(ListRepresentation.Items(length, items)) =>
        ListRepresentation.Items(length + 1, item +: items)
      case other => ListRepresentation.Cell(item, other)

/** The family `unread`, the representation of a position a criterion leaves
  * open, whose criterion is Ω: a field of this family is held as it is written, unevaluated
  * (`NativeValue.Unread`), which is exact since x ∥ Ω ≃_O x (Lean
  * `omegaParallelContextualEquivalence`). It has no constructor, so no value
  * of it is built or taken by a layer: the JIT's decoding, encoding and
  * reading of a field handle it before they would ask for one.
  */
object UnreadFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("unread")

  val parameterFamily: Option[FamilyIdentity] = None

  override def heldAsWritten: Boolean = true

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] = Vector.empty

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue =
    throw IllegalArgumentException(s"the family unread has no layer: $layer")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer =
    throw IllegalArgumentException(s"the family unread has no layer: $value")

/** The family `big_integer` of the standard set: the library's naturals as
  * `BigInt`s, n standing for successor^n zero (`BigIntegerCodec`, THE
  * ASSUMED SHAPE). The check of its constructors is `BigIntegerCodec`'s, with
  * its readings.
  */
object BigIntegerFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("big_integer")

  val parameterFamily: Option[FamilyIdentity] = None

  private val unparameterisedConstructors: Vector[DataConstructor] = Vector(
    DataConstructor(NativeName.Constructor(identity, BigIntegerCodec.position(NaturalConstructor.Zero)), Vector.empty),
    DataConstructor(
      NativeName.Constructor(identity, BigIntegerCodec.position(NaturalConstructor.Successor)),
      Vector(DataField.unparameterised(identity))
    )
  )

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] = unparameterisedConstructors

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue = layer match
    case DataLayer(0, Vector())                                 => NativeValue.Natural(BigInt(0))
    case DataLayer(1, Vector(NativeValue.Natural(predecessor))) => NativeValue.Natural(predecessor + 1)
    case other => throw IllegalArgumentException(s"no layer of a natural: $other")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer = value match
    case NativeValue.Natural(natural) =>
      val (_, branch, fields) = BigIntegerCodec.eliminatedBranch(natural)
      DataLayer(branch - 1, fields.map(NativeValue.Natural(_)))
    case other => throw IllegalArgumentException(s"no natural: $other")

  override def constructorsShape(parameter: Option[NativeValue], defines: Vector[Instruction]): Shape[Any] =
    defines match
      case Vector(zero, successor) => BigIntegerCodec.constructorsShape(zero, successor)
      case other => throw IllegalArgumentException(s"${other.size} defines for the two constructors of ${identity.name}")

/** The family `boolean` of the standard set: the library's booleans as
  * `Boolean`s, true the first constructor (`BooleanCodec`, THE ASSUMED
  * SHAPE). The check of its constructors is `BooleanCodec`'s, with its
  * readings.
  */
object BooleanFamily extends DataFamily:

  val identity: FamilyIdentity.Codec = FamilyIdentity.Codec("boolean")

  val parameterFamily: Option[FamilyIdentity] = None

  private val unparameterisedConstructors: Vector[DataConstructor] = Vector(
    DataConstructor(NativeName.Constructor(identity, BooleanCodec.position(true)), Vector.empty),
    DataConstructor(NativeName.Constructor(identity, BooleanCodec.position(false)), Vector.empty)
  )

  def constructors(parameter: Option[NativeValue]): Vector[DataConstructor] = unparameterisedConstructors

  def built(parameter: Option[NativeValue], layer: DataLayer): NativeValue = layer match
    case DataLayer(0, Vector()) => NativeValue.Truth(true)
    case DataLayer(1, Vector()) => NativeValue.Truth(false)
    case other                  => throw IllegalArgumentException(s"no layer of a boolean: $other")

  def taken(parameter: Option[NativeValue], value: NativeValue): DataLayer = value match
    case NativeValue.Truth(truth) =>
      val (_, branch, _) = BooleanCodec.eliminatedBranch(truth)
      DataLayer(branch - 1, Vector.empty)
    case other => throw IllegalArgumentException(s"no boolean: $other")

  override def constructorsShape(parameter: Option[NativeValue], defines: Vector[Instruction]): Shape[Any] =
    defines match
      case Vector(trueDefine, falseDefine) => BooleanCodec.constructorsShape(trueDefine, falseDefine)
      case other => throw IllegalArgumentException(s"${other.size} defines for the two constructors of ${identity.name}")

/** The terms of the standard set's codec constructors of the naturals and
  * the booleans, which the tests of the natives build values from: the
  * terms at the constructors' positions in the `data_family` of the types
  * specialized to big_integer and boolean.
  */
extension (facts: BackendFacts)

  /** The term of zero, big_integer's constructor 0. */
  def zero: Instruction =
    facts.constructorDefine(NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Zero)))

  /** The term of successor, big_integer's constructor 1. */
  def successor: Instruction =
    facts.constructorDefine(NativeName.Constructor(BigIntegerFamily.identity, BigIntegerCodec.position(NaturalConstructor.Successor)))

  /** The term of true, boolean's constructor 0. */
  def trueDefine: Instruction = facts.constructorDefine(NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(true)))

  /** The term of false, boolean's constructor 1. */
  def falseDefine: Instruction = facts.constructorDefine(NativeName.Constructor(BooleanFamily.identity, BooleanCodec.position(false)))
