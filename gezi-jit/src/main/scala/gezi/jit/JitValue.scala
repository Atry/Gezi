package gezi.jit

import gezi.weakhead.ListRepresentation
import gezi.weakhead.Mode
import gezi.weakhead.Neutral
import gezi.weakhead.NeutralVariable
import gezi.strategies.DispatchDecision
import gezi.strategies.DispatchStrategy
import gezi.ir.Code
import gezi.ir.ConstructorIdentity
import gezi.ir.InternedConstructor
import gezi.ir.Interned
import gezi.ir.Interned.Interned
import gezi.ir.Hole
import gezi.ir.{
  Closed,
  Configured,
  NativeSpecializer,
  Pure,
  Value,
  ValueExtension
}
import gezi.weakhead.{NeutralValue, SuspensionValue}

/** A representation of the backend (jit.pl, THE BACKEND'S REPRESENTATIONS): the
  * values of a data family of the backend's `NativeBackend`, named by the
  * family's identity (`FamilyIdentity`), at a parameter when the family takes
  * one, or the lists of one element filter as host vectors (list(Key) in the
  * Prolog JIT, Key the element filter's instruction; here the element filter
  * itself, an interned value), the framework's own family `list`, or the array
  * lists of a scalar representation, the framework's family `array_list`. Equal
  * by its cases' fields.
  */
enum Representation[+Term]:
  // A storage holds no codec's name: a codec of no parameter is its storage's class, whose representation is a
  // constant; a storage holds only what varies within its codec (a word's width, a list's element criterion) and a
  // declared family's criterion (`RepresentedStorage.representation`).
  case Data(family: FamilyIdentity, parameter: Option[FamilyParameter[Term]])
  case ListOf(element: Term)

  /** The array lists of a scalar representation (`array_list E`, E the
    * criterion `element` names): lists whose every element is a scalar of
    * `element`, held as one vector that every suffix shares
    * (`ArrayListStorage`), the family the facts name `array_list`.
    */
  case ArrayListOf(element: Representation[Term])

  /** The representation as one holding no term, for the storage of a constant,
    * which is native data alone: a family's with no parameter or a parameter of
    * plain data (a word's width). Throws `IllegalStateException` for a
    * representation that holds a term (a list's element criterion, a declared
    * family's criterion parameters), whose values are no constants.
    */
  def asConstant: Representation[Nothing] = this match
    case Data(_, Some(_: CriterionParameters[?])) | ListOf(_) =>
      throw IllegalStateException(
        s"a representation holding a term is no constant's: $this"
      )
    case Data(FilteredFamily.identity, _) =>
      throw IllegalStateException(
        s"a filter of no family is no constant's: $this"
      )
    // The other cases hold no term, whatever their type argument says: the same object serves as a constant's.
    case _ => this.asInstanceOf[Representation[Nothing]]

  /** The identity of the family the representation belongs to. */
  def familyIdentity: FamilyIdentity = this match
    case Data(family, _) => family
    case ListOf(_)       => Representation.listFamily
    case ArrayListOf(_)  => Representation.arrayListFamily

/** The framework's family of lists and the standard set's two data families'
  * representations.
  */
object Representation:

  /** The framework's family of lists, a codec named `list`. */
  val listFamily: FamilyIdentity.Codec = FamilyIdentity.Codec("list")

  /** The framework's family of array lists, a codec named `array_list`. */
  val arrayListFamily: FamilyIdentity.Codec = FamilyIdentity.Codec("array_list")

  /** The representation of the standard set's naturals. */
  val BigInteger: Representation[Nothing] =
    Data(BigIntegerFamily.identity, None)

  /** The representation of the standard set's booleans. */
  val Truth: Representation[Nothing] = Data(BooleanFamily.identity, None)

/** A value of a representation, held as its family chooses: the standard set's
  * natural as a `BigInt` and boolean as a `Boolean`, the framework's list as
  * `ListRepresentation` over the JIT's run-time values (its items kept
  * unevaluated, a cell's tail unread), and a value of a data family a backend
  * adds as a class of its own that extends this trait. Equality is the class's.
  * Covariant in the type of the terms it holds (a list's items, a field held as
  * written): a value that holds none is a `NativeValue[Nothing]`, one of every
  * configuration, and one that holds terms of the configuration `C` holds
  * `JitValue[C]`.
  */
trait NativeValue[+Term]:

  /** The terms the value holds, read off its own data with no configuration and
    * no walk of a storage it reaches: a list's items or a cell's item and tail,
    * a declared value's fields' terms, an unread or a stored term. None for a
    * value of native data alone, the default; a provider's value class that
    * holds terms gives them, so that its storage's closedness costs no walk of
    * the value (`ValueStorage`).
    */
  def heldTerms: Vector[Term] = Vector.empty

/** The parameter of a data family that takes one, read from the decoding
  * criterion written in the term (`word_type W`, `binary_set P`, a declared
  * family's `C P1 … Pk`): each family that takes a parameter has its own class,
  * a provider's family included. It is no family's value: a value is a
  * `NativeValue`.
  */
trait FamilyParameter[+Term]

/** The parameters of a data family declared by facts whose parameters are
  * criteria: the representation each criterion of its filter `C @ P1 @ … @ Pk`
  * names, in order, read from the filter as written.
  */
final case class CriterionParameters[+Term](
    criteria: Vector[Representation[Term]]
) extends FamilyParameter[Term]

/** The values of the standard set's families and of the framework's lists. */
object NativeValue:

  /** A natural of the family `big_integer`. */
  final case class Natural(value: BigInt) extends NativeValue[Nothing]

  /** A boolean of the family `boolean`. */
  final case class Truth(value: Boolean) extends NativeValue[Nothing]

  /** A list of the framework's family `list`: a storage holds the empty list or
    * one cell (`ListRepresentation.Cell`), a whole list of items being made
    * into its cells when it is stored (`RepresentedStorage.apply`).
    */
  final case class Listed[+Term](list: ListRepresentation[Term])
      extends NativeValue[Term]:
    override def heldTerms: Vector[Term] = list match
      case ListRepresentation.Items(_, items)  => items
      case ListRepresentation.Cell(item, tail) => Vector(item, tail)

  /** An array list's value: the suffix from `start` of the elements, which
    * every suffix of one list shares (`ArrayElements`). Equal by the elements
    * from `start` on, the same elements and start first, so that a value
    * compares in one step with its own suffixes' kin; its hash code is its
    * elements' content's, computed once for every suffix.
    */
  final case class ArrayListed(elements: ArrayElements, start: Int)
      extends NativeValue[Nothing]:
    require(
      start >= 0 && start <= elements.values.size,
      s"a suffix starts within its list: $start of ${elements.values.size}"
    )

    /** Whether the suffix is empty. */
    def nil: Boolean = start == elements.values.size

    /** The suffix's elements. */
    def suffix: Vector[ArrayItem] = elements.values.drop(start)

    override def equals(other: Any): Boolean = other match
      case that: ArrayListed =>
        ((that.elements eq elements) && that.start == start) ||
        (that.elements.values.size - that.start == elements.values.size - start && that.hashCode == hashCode && that.suffix == suffix)
      case _ => false

    override def hashCode: Int = elements.contentHash(start)

  /** A value of a data family declared by facts with `jvm_type(generic)`
    * (`DeclaredFamily`): the family's identity, its constructor's index in the
    * order of the cases, and the values of its fields.
    */
  final case class Constructed[+Term](
      family: FamilyIdentity,
      constructor: Int,
      fields: Vector[NativeValue[Term]]
  ) extends NativeValue[Term]:
    override def heldTerms: Vector[Term] = fields.flatMap(_.heldTerms)

  /** A field of the family `unread` (`UnreadFamily`), the term as it is
    * written, unevaluated. It stands only in the fields of another family's
    * value: a head is never a value of `unread`.
    */
  final case class Unread[+Term](term: Term) extends NativeValue[Term]:
    override def heldTerms: Vector[Term] = Vector(term)

  /** A value of a declared family held as its storage, the term itself (a
    * `ConstructedStorage` of the configuration): a native takes or gives it as
    * a typed term, and its fields' values are the configuration's reading of
    * the storage (`StorageEncodingOperations.fieldValues`), not data the value
    * holds.
    */
  final case class Stored[+Term](term: Term) extends NativeValue[Term]:
    override def heldTerms: Vector[Term] = Vector(term)

/** The value a native takes or gives at one place of its calling convention
  * (jit.pl, THE NATIVE'S REPRESENTATIONS): a value of a representation; a
  * list's item, a run-time value kept as given; or a list's tail's node, a
  * storage of the list or, under the default construction, the tail as given
  * (`ListRepresentation.Cell`).
  */
enum NativeArgument[+Term]:
  case Represented(value: NativeValue[Term])
  case Item(item: Term)
  case Tail(tail: Term)

/** The cell the JIT puts around an open value it shares (`JitRules.shared`): an
  * extension of the readers' values, not closed, whose table shares the reads
  * of its filling, which the JIT's syntactic reads see through, so that a
  * decode point or a fallback point shared this way is still found. It holds an
  * open value only (`Open[C]`): a closed term is shared by the table key
  * `TabledInstance(cellCode, [t])`, never by a cell.
  */
final case class SharingCellLayer[+Child] private (inner: Child)
    extends InternedConstructor
    with ValueExtension[Child]:
  override def toString: String = ConstructorIdentity.shown(this)

  /** False: it holds an open value. */
  def closed: Boolean = false

object SharingCellLayer:
  /** The canonical layer. */
  def apply[Child](inner: Child): SharingCellLayer[Child] =
    Interned.canonicalLayer(new SharingCellLayer(inner))

/** The sharing cell as a value, and its filling. */
object SharingCell:
  def apply[C <: NativeSpecializer & Singleton](inner: gezi.ir.Open[C])(using
      C
  ): JitValue[C] = Value.extension(SharingCellLayer(gezi.ir.Open.value(inner)))

  def unapply[C <: NativeSpecializer & Singleton](
      value: JitValue[C]
  ): Option[JitValue[C]] = value.layer match
    case SharingCellLayer(inner) => Some(inner)
    case _                       => None

/** The empty parallel set: the head of a listed least term of ⊑_O, such as Ω,
  * under the reading's known extremes (`gezi.weakhead.KnownExtremes`), whatever
  * it is applied to, as the weak head's machines give it
  * (`WeakHead.knownExtreme`). The JIT's own head: a least term is not
  * evaluated, and no layer of a value gives this head.
  */
case object EmptyParallel

/** One layer of a run-time value of the JIT: the IR's own layers (`IrLayer`:
  * application, parallel, binary choice, thunk, URI node, opaque term), the
  * reference's neutral value, and the JIT's own three, the evaluation a
  * fallback point's check passes on, a cell and the choice of no member. A
  * value of a representation is a native storage (`RepresentedStorage`), whose
  * layer is its view, a parallel. Every layer of the IR is one, so an
  * instruction is a value of the JIT as it is: one pool holds both, and a value
  * the JIT builds that equals an instruction by content is that instruction.
  */
type JitLayer[+Child] = gezi.ir.ValueLayer[Child]

/** A run-time value of the JIT (jit.pl, AN EVALUATOR OVER THE REFERENCE'S
  * VALUES): an interned term ([[gezi.ir.Interned]]) of `JitLayer`, every value
  * interned, as every IR term is.
  */
type JitValue[C <: NativeSpecializer & Singleton] = gezi.ir.Value[C]

/** The constructions and the parts of the JIT's values, each made through the
  * pool.
  */
object JitValue:

  // TODO: deleted: `JitValue.of`, the untyped construction of a value from a layer. Wrong because it builds a value
  // from children of any configuration, so two configurations' terms can be mixed in one value; issue
  // https://github.com/Atry/private-overlay/issues/2261, design v38, section 6.
  // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/JitValue.scala`.

  /** Whether the value is a storage, which no extractor but `Represented`
    * reads: one class test.
    */
  private def stored[C <: NativeSpecializer & Singleton](
      value: JitValue[C]
  ): Boolean =
    gezi.ir.NativeStorage.stored(value.representation)

  /** A value that is an instruction, a term of the IR's layers alone
    * (`ConstructorIdentity.isInstruction`, one field read), whoever built it:
    * the program's syntax, read one layer when reached (`Jit.layer`), and the
    * identity a native-bound library file's term is found by.
    */
  object IrTerm:
    def unapply[C <: NativeSpecializer & Singleton](value: JitValue[C])(using
        C
    ): Option[Configured[C]] =
      // A storage is read as its own head, never as syntax.
      if stored(value) then None else Closed.configured(value)

  /** An application. */
  object Apply:
    def apply[C <: NativeSpecializer & Singleton](
        function: JitValue[C],
        argument: JitValue[C]
    )(using C): JitValue[C] =
      Value.Apply(function, argument)

    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[(JitValue[C], JitValue[C])] = if stored(value) then None
    else
      value.layer match
        case gezi.ir.Apply(function, argument) => Some((function, argument))
        case _                                 => None

  /** The parallel of two sides. */
  object Parallel:

    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[(JitValue[C], JitValue[C])] = if stored(value) then None
    else
      value.layer match
        case gezi.ir.Parallel(left, right) => Some((left, right))
        case _                             => None

  /** The choice of the members, in order: the IR's binary choice, a chain of
    * several nested to the right (`gezi.ir.ChoiceSpine`), so that its heads are
    * its members' heads in order. A choice's parts are its two sides, not the
    * chain flattened: a fallback point `v + (v ∥ c)` that is the right side of
    * another choice is a node of its own, read when that side is read
    * (`fallbackMembers` reads two parts). A choice of one member is that
    * member, whose heads are the choice's; of none, `noAnswer`.
    */
  object Choice:
    def apply[C <: NativeSpecializer & Singleton](members: Vector[JitValue[C]])(
        using C
    ): JitValue[C] = members match
      case Vector()       => noAnswer[C]
      case Vector(member) => member
      case _              =>
        members.init.foldRight(members.last)((member, rest) =>
          Value.Choice(member, rest)
        )

    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[Vector[JitValue[C]]] = if stored(value) then None
    else
      value.layer match
        case gezi.ir.Choice(left, right) => Some(Vector(left, right))
        case _                           => None

  /** The value of no answer, the choice of no member: the library's `top`
    * (`gezi.frontend.Literals.top`), a term of the IR that readers hold as it
    * is, and whose known extreme they read as no head. It is the same object
    * under every configuration: `top` is thunks and applications with no
    * parallel in a unique spelling, so no native specializer converts any node
    * of it.
    */
  def noAnswer[C <: NativeSpecializer & Singleton](using
      specializer: C
  ): JitValue[C] =
    Value.of(Configured.fromPure(specializer)(topPure))

  /** `top` as a pure term, built once. */
  private lazy val topPure: Pure =
    gezi.frontend.Defunctionalization.pure(gezi.frontend.Literals.top)

  /** A lambda chain: its code, the holes still to be applied, the fillings. */
  object Thunk:
    /** The thunk value of a code with holes still to fill, or its suspension
      * when every hole is filled.
      */
    def apply[C <: NativeSpecializer & Singleton](
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[JitValue[C]]
    )(using
        C
    ): JitValue[C] =
      if holes.isEmpty then SuspensionValue(code, fillings)
      else Value.Thunk(code, holes, fillings)

    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[(Code, Vector[Hole], Vector[JitValue[C]])] = if stored(value) then
      None
    else
      value.layer match
        case gezi.ir.Thunk(code, holes, fillings) =>
          Some((code, holes, fillings))
        case _ => None

  /** The free variable applied to the arguments. */
  object Neutral:
    def apply[C <: NativeSpecializer & Singleton](
        variable: NeutralVariable,
        arguments: Vector[JitValue[C]]
    )(using C): JitValue[C] =
      NeutralValue(variable, arguments)

    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[(NeutralVariable, Vector[JitValue[C]])] = if stored(value) then
      None
    else
      value.layer match
        case gezi.weakhead.Neutral(variable, arguments) =>
          Some((variable, arguments))
        case _ => None

  /** A value of a representation, its own head: a storage
    * (`RepresentedStorage`) under the facts' encoding.
    */
  object Represented:
    // A storage of native data is built by the configuration's encoding (`StorageEncodingOperations.storageOf`).
    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[(Representation[JitValue[C]], NativeValue[JitValue[C]])] =
      value match
        case JitValue.Stored(storage) =>
          Some((storage.representation, StorageOf.nativeValue(storage)))
        case _ => None

  /** The members of a group of storages (`GroupStorage`), each its own head:
    * the group is the choice of them.
    */
  object Grouped:
    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[Vector[JitValue[C]]] = value match
      // TODO: deleted: the cast of each group member to `JitValue`. Wrong because the cast stands where the types
      // should say which configuration a value belongs to, sound only by coding discipline; issue
      // https://github.com/Atry/private-overlay/issues/2261, design v38, sections 6 and 8.
      // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/JitValue.scala`.
      case _ => None

  /** A value of a representation as its storage, which is its own head. */
  object Stored:
    def unapply[C <: NativeSpecializer & Singleton](
        value: JitValue[C]
    ): Option[RepresentedStorage[JitValue[C]]] =
      StorageOf.typed[C](value.representation)

/** A native of the backend's `NativeBackend`, bound to a define: its name and
  * the number of its parameters.
  */
final case class BoundNative(name: NativeName, parameterCount: Int)

/** `native_application(Handle, Predicate, Missing, Arguments)`: the head of the
  * define at the instruction, bound to the native of at least one parameter,
  * with the arguments so far and the number still missing; never a value.
  */
final case class NativeApplication[C <: NativeSpecializer & Singleton] private (
    instruction: Configured[C],
    native: BoundNative,
    missing: Int,
    arguments: Vector[JitValue[C]]
) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

/** `elimination(Representation, Value, Cases)`: the represented value applied
  * to fewer arguments than its codec takes before it chooses a branch; never a
  * value.
  */
final case class Elimination[C <: NativeSpecializer & Singleton] private (
    representation: Representation[JitValue[C]],
    value: NativeValue[JitValue[C]],
    cases: Vector[JitValue[C]]
) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

object Elimination:
  /** The canonical Elimination: a layer that no construction site converts is
    * interned when it is made.
    */
  def apply[C <: NativeSpecializer & Singleton](
      representation: Representation[JitValue[C]],
      value: NativeValue[JitValue[C]],
      cases: Vector[JitValue[C]]
  ): Elimination[C] =
    Interned.canonicalLayer(new Elimination(representation, value, cases))

/** A head of the JIT (jit.pl's heads): the reference's kinds (a lambda and a
  * neutral value, each the layer of an interned value, and two values met as a
  * parallel), and the JIT's own: a represented value, a native's define taken
  * before its parameters are all there, and a represented value applied to
  * fewer arguments than its codec takes. Equal by content.
  */
type JitHead[C <: NativeSpecializer & Singleton] =
  gezi.ir.Thunk[JitValue[C]] | Neutral[JitValue[C]] | ParallelHead[C] |
    RepresentedStorage[JitValue[C]] | NativeApplication[C] | Elimination[C] |
    EmptyParallel.type

/** Two values met as a head, `left ∥ right`, when the criterion names no
  * representation: a head, not a node of the IR, so it is never interned; as a
  * value it is built through the facts' native specializer (`asValue`).
  */
final case class ParallelHead[C <: NativeSpecializer & Singleton](
    left: JitValue[C],
    right: JitValue[C]
)

/** The constructions and the parts of the JIT's heads. */
object JitHead:

  /** A thunk with at least one hole. */
  object Lambda:
    def apply[C <: NativeSpecializer & Singleton](
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[JitValue[C]]
    )(using
        specializer: C
    ): JitHead[C] =
      Value.thunkLayer(specializer)(
        code,
        gezi.ir.NonEmptyHoles
          .of(holes)
          .getOrElse(
            throw IllegalArgumentException(
              s"a head of no hole, a suspension: $code"
            )
          ),
        fillings
      )

    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[(Code, Vector[Hole], Vector[JitValue[C]])] = head match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                    => None

  /** A neutral value. */
  object Neutral:
    def apply[C <: NativeSpecializer & Singleton](
        variable: NeutralVariable,
        arguments: Vector[JitValue[C]]
    ): JitHead[C] =
      gezi.weakhead.Neutral(variable, arguments)

    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[(NeutralVariable, Vector[JitValue[C]])] = head match
      case gezi.weakhead.Neutral(variable, arguments) =>
        Some((variable, arguments))
      case _ => None

  /** Two values met as a head, its sides not evaluated (`ParallelHead`): equal
    * by its sides, which are interned, so that sets of answers and the
    * comparison of a table's answers with another computation's find two such
    * heads over the same sides equal.
    */
  object Parallel:
    def apply[C <: NativeSpecializer & Singleton](
        left: JitValue[C],
        right: JitValue[C]
    ): JitHead[C] = ParallelHead(left, right)

    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[(JitValue[C], JitValue[C])] = head match
      case ParallelHead(left, right) => Some((left, right))
      case _                         => None

  /** A head that is a storage, typed by the head's configuration
    * (`StorageOf.ofHead`).
    */
  object StorageHead:
    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[RepresentedStorage[JitValue[C]]] = head match
      case storage: RepresentedStorage[?] => Some(StorageOf.ofHead[C](storage))
      case _                              => None

  /** A value of a representation, its own head. */
  object Represented:
    // A head of native data is the storage the configuration's encoding builds (`StorageEncodingOperations.storageOf`).
    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[(Representation[JitValue[C]], NativeValue[JitValue[C]])] =
      head match
        case StorageHead(storage) =>
          Some((storage.representation, StorageOf.nativeValue(storage)))
        case _ => None

  /** The head of a bound define, its parameters not all there. */
  object NativeApplication:
    def apply[C <: NativeSpecializer & Singleton](
        instruction: Configured[C],
        native: BoundNative,
        missing: Int,
        arguments: Vector[JitValue[C]]
    ): JitHead[C] =
      gezi.jit.NativeApplication(instruction, native, missing, arguments)

    def unapply[C <: NativeSpecializer & Singleton](
        head: JitHead[C]
    ): Option[(Configured[C], BoundNative, Int, Vector[JitValue[C]])] =
      head match
        case gezi.jit.NativeApplication(
              instruction,
              native,
              missing,
              arguments
            ) =>
          Some((instruction, native, missing, arguments))
        case _ => None

  /** A represented value applied to fewer arguments than its codec takes. */
  object Elimination:
    def apply[C <: NativeSpecializer & Singleton](
        representation: Representation[JitValue[C]],
        value: NativeValue[JitValue[C]],
        cases: Vector[JitValue[C]]
    ): JitHead[C] =
      gezi.jit.Elimination(representation, value, cases)

    def unapply[C <: NativeSpecializer & Singleton](head: JitHead[C]): Option[
      (
          Representation[JitValue[C]],
          NativeValue[JitValue[C]],
          Vector[JitValue[C]]
      )
    ] = head match
      case gezi.jit.Elimination(representation, value, cases) =>
        Some((representation, value, cases))
      case _ => None

/** The operations of a JIT head (`JitHead`), as extensions in the companion of
  * [[NativeApplication]], a constructor of that union alone, which puts them in
  * its implicit scope.
  */
object NativeApplication:

  /** The canonical NativeApplication: a layer that no construction site
    * converts is interned when it is made.
    */
  def apply[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      native: BoundNative,
      missing: Int,
      arguments: Vector[JitValue[C]]
  ): NativeApplication[C] = Interned.canonicalLayer(
    new NativeApplication(instruction, native, missing, arguments)
  )

  extension [C <: NativeSpecializer & Singleton](head: JitHead[C])
    /** The name of the head's kind, for messages. */
    def name: String = head match
      case _: RepresentedStorage[?] => "RepresentedStorage"
      case product: Product         => product.productPrefix

    /** The head as a run-time value, a parallel head built through the
      * encoding's native specializer. Throws `IllegalStateException` for the
      * two heads that are never values.
      */
    def asValue(using C): JitValue[C] = head match
      case thunk @ gezi.ir.Thunk(_, _, _) => Value.ofHeadLayer(thunk)
      case gezi.weakhead.Neutral(variable, arguments) =>
        NeutralValue(variable, arguments)
      case ParallelHead(left, right)    => Value.Parallel(left, right)
      case JitHead.StorageHead(storage) => StorageOf.value(storage)
      case other                        =>
        throw IllegalStateException(s"the head ${other.name} is never a value")

/** The mode the JIT evaluates under (jit.pl's `jit_dispatch_set/1`): none,
  * which reads as a strategy deciding `untyped`, or a dispatch strategy chosen
  * when the program was compiled (jit.pl, DISPATCH STRATEGIES): a value of
  * `gezi.strategies.DispatchStrategy` that baseline or entry code gives, with
  * its decision at a fallback point whose check does not hold, `Untyped`
  * running the untyped path and `Rejected` throwing `TypedVersionDomain`. This
  * module names no strategy.
  */
enum DispatchMode:
  case NoDispatch
  case Dispatch(strategy: DispatchStrategy)

  /** The decision at a fallback point whose check does not hold. */
  def outsideDecided: DispatchDecision = this match
    case NoDispatch         => DispatchDecision.Untyped
    case Dispatch(strategy) => strategy.outsideDecided

/** A fallback point's check under a strategy deciding `rejected` found its
  * operand outside the typed version's domain (the Prolog JIT's
  * `error(domain_error(typed_version_domains([R]), Written), _)`): the
  * representation and the operand as written. The message names the
  * representation only, the operand may be deep.
  */
final case class TypedVersionDomain(
    representation: Representation[Any],
    written: Interned[gezi.ir.ValueLayer]
) extends RuntimeException:
  override def getMessage: String =
    s"typed_version_domains([${representation.familyIdentity.shown}])"
