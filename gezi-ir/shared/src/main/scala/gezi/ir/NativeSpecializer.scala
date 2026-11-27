package gezi.ir

import gezi.ir.Interned.Interned

/** A term in the specialized spelling of the native specializer `C`: every node whose unique spelling `C`'s facts give
  * a native storage is that storage, every other node one layer of the IR over terms of `C`. Invariant in `C` and with
  * no upper bound, so that a term of one configuration is neither a term of another nor an [[Instruction]] that any
  * code may take: the terms of two configurations are two types, and the compiler rejects mixing them.
  *
  * `C` is the singleton type of one native specializer (`c.type`), one per entry.
  */
opaque type Configured[C <: NativeSpecializer & Singleton] = Instruction

object Configured:

  /** The term the specializer built, taken as its configuration's: only this file and the specializer's own
    * construction call it, every caller having built the object through `C`.
    */
  private[ir] def built[C <: NativeSpecializer & Singleton](term: Instruction)(using C): Configured[C] = term

  extension [C <: NativeSpecializer & Singleton](term: Configured[C])

    /** The object the term is, for the registered readers that interpret it (the value layer of the readers, the
      * pool's content comparison): the same object, storages still in it, so it is no conversion to a form without
      * storages.
      */
    def representation: Instruction = term

    /** The term's one layer, its children terms of the same configuration; a storage is a leaf of it. */
    def layer: IrLayer[Configured[C]] = term.layer

    /** The URI of a URI node; none for any other term, a storage answered by a class test. */
    def uri: Option[java.net.URI] = UriNode.uri(term)

    /** Whether the term is opaque: named, its layer no part of the IR (a URI node included). */
    def opaque: Boolean = UriNode.opaque(term)

    /** Whether the e-graph holds the term as a leaf whose layer it never reads: an opaque term, or a storage it keeps
      * as a leaf.
      */
    def heldAsLeaf: Boolean = UriNode.heldAsLeaf(term)

  /** The spine of a term of the configuration ([[gezi.ir.Spine]]): its head and its arguments, read from the flat copy an
    * application stores; a storage, a leaf of its term's layer, is its own head.
    */
  object Spine:
    def of[C <: NativeSpecializer & Singleton](term: Configured[C]): (Configured[C], Vector[Configured[C]]) =
      gezi.ir.Spine.of[IrLayer](term)

    def unapplySeq[C <: NativeSpecializer & Singleton](term: Configured[C]): Option[(Configured[C], Seq[Configured[C]])] =
      gezi.ir.Spine.unapplySeq[IrLayer](term)

  /** Whether the two terms of one configuration are one term: one object, since every term is interned. */
  def same[C <: NativeSpecializer & Singleton](left: Configured[C], right: Configured[C])(using C): Boolean = left eq right

  /** The pure term in the configuration of `specializer`: the same object, since a pure term holds no parallel at the
    * level of instructions and is its own specialized spelling under every configuration. O(1).
    */
  def fromPure[C <: NativeSpecializer & Singleton](specializer: C)(term: Pure): Configured[C] = term.representation

/** A term with no parallel layer, no storage and no thunk without holes at the level of instructions (a parallel inside
  * a code's body, such as `z ∥ x` in `top`'s code, does not count): a fact's key, a framework constant. Since native
  * specialization acts only on parallel layers, a pure term is its own specialized spelling under every configuration,
  * and enters one by `Configured.fromPure`.
  */
opaque type Pure = Instruction

object Pure:

  /** The term of no facts as a pure term, when it is one: a deep read, done once per fact's key when the facts are
    * built, each node of the term's DAG read once.
    */
  def of(term: Configured[NoFacts.type]): Option[Pure] =
    @scala.annotation.tailrec
    def read(pending: List[Instruction], seen: Set[Instruction]): Boolean = pending match
      case Nil                                 => true
      case node :: rest if seen.contains(node) => read(rest, seen)
      case node :: rest =>
        node.layer match
          case _: NativeStorage                    => false
          case Parallel(_, _)                      => false
          case Apply(function, argument)           => read(function :: argument :: rest, seen + node)
          case Choice(left, right)                 => read(left :: right :: rest, seen + node)
          case Thunk(_, holes, _) if holes.isEmpty => false
          case Thunk(_, _, fillings)               => read(fillings.toList ::: rest, seen + node)
          case _                                   => read(rest, seen + node)
    val instruction = term.representation
    Option.when(read(List(instruction), Set.empty))(instruction)

  /** The term of no facts as a pure term (`of`). Throws `IllegalArgumentException` for a term that is none: a
    * parallel, a storage or a thunk without holes at the level of instructions.
    */
  def required(term: Configured[NoFacts.type]): Pure =
    of(term).getOrElse(throw IllegalArgumentException(s"the term is no pure term: $term"))

  /** The term the front end built pure (`Defunctionalization.pure`), which checked it holds no parallel layer: only
    * the front end and this file call it.
    */
  private[gezi] def checkedByTheFrontEnd(term: Instruction): Pure = term

  /** The application of two pure terms, itself pure: an application is no parallel, so no specializer converts it, and
    * it is the same object under every configuration.
    */
  def application(function: Pure, argument: Pure): Pure =
    Interned[IrLayer](Apply.ofTerms(function.representation, argument.representation))

  extension (term: Pure)

    /** The object the term is, for the registered readers that interpret it. */
    def representation: Instruction = term

/** The holes of a thunk that is a term: at least one, so that no thunk without holes, a suspended computation, is built
  * as an IR term. A code's own thunk layer (an inner code) keeps `Vector[Hole]`, which may be empty: it is a code, not
  * a term.
  */
opaque type NonEmptyHoles = Vector[Hole]

object NonEmptyHoles:

  /** The holes, when there is one at least: the typed dispatch of every site that makes a term of a code's thunk. */
  def of(holes: Vector[Hole]): Option[NonEmptyHoles] = Option.when(holes.nonEmpty)(holes)

  /** The first hole and the rest. */
  def apply(first: Hole, rest: Vector[Hole]): NonEmptyHoles = first +: rest

  extension (holes: NonEmptyHoles) def toVector: Vector[Hole] = holes

/** The native specialization of one configuration: the specializer builds every term of its configuration, and it is
  * the only way to build one, so construction is specialization. It converts each parallel layer into its storage when
  * it is the unique spelling of one, before it is interned, so that no API gives the unspecialized object of a node
  * that has a storage, not even a temporary one, as C++'s `vector<bool>` is always its specialization. Where no facts
  * exist yet (the library and an entry's data are read before their facts), the specializer is [[NoFacts]], which
  * declares no representation.
  *
  * A storage holds no configuration (interning replaces structural equality and reads none): what depends on the
  * configuration, a storage's criterion and its one-layer view, the specializer of the entry in scope reads
  * (`criterionOf`, `viewOf`), and its type says which configuration the result is of.
  *
  * The operations are extensions of the companion over the singleton type `C` of the specializer they are called on
  * (`specializer.application(f, a)` with `specializer: C` gives a `Configured[C]`), not members: a member's
  * `Configured[this.type]`, called on a `specializer: C`, is a `Configured[specializer.type]`, which Scala does not
  * take for a `Configured[C]`, although `C`'s only value is `specializer`.
  *
  * A backend subclasses it with its facts' one conversion (`specialized`) and its reading of its own storages
  * (`storageCriterion`, `storageView`), all protected, written in its own `this.type`, and makes the storages of
  * natives' results through `storedTerm`, the only entry of a storage to the pool. A backend's own typed operations
  * carry its `this.type` to the `C` of their caller by [[NativeSpecializer.sameType]]. Which subclasses exist is
  * checked by the conventions project.
  */
abstract class NativeSpecializer:

  /** The specialized object of the parallel `left ∥ right` of two closed values under these facts, read from one layer
    * of each side, when it has one: the storage of a unique spelling `C (f1 ∥ F1) … ∥ T`; a group storage of a run of
    * storages; or `left` itself when it already is a storage, or written `l ∥ right`, under the criterion `right` (∥ is
    * idempotent). None for any other parallel, which is then built as written. Closed values, not only terms of the
    * IR: a storage keeps a field held as written whatever closed value it is, a suspension included, and its result is
    * a term of the IR exactly when both sides are.
    */
  protected def specialized(left: Closed[this.type], right: Closed[this.type]): Option[Closed[this.type]]

  /** The criterion T of the storage's view `v ∥ T` under this configuration (`criterionOf`). */
  protected def storageCriterion(storage: NativeStorage): Configured[this.type]

  /** The storage's one-layer view under this configuration's families (`viewOf`). */
  protected def storageView(storage: NativeStorage)(using StorageAccess): StorageView[Configured[this.type]]

  /** The storage read as untyped Scott ADT values, one layer (`scottReadingOf`). */
  protected def storageScottReading(storage: NativeStorage)(using StorageAccess): ScottReading[Configured[this.type]]

  /** The term of a storage this specializer's backend made from native data (a native's result, a block's output, a
    * decode point's value): the pool's object for it. Every term the storage holds must already be a term of this
    * configuration.
    */
  protected final def storedTerm(storage: NativeStorage): Configured[this.type] =
    Configured.built(Interned.stored[IrLayer](storage))(using this)

object NativeSpecializer:

  /** The evidence that the specializer's own singleton type and `C` are one configuration: `C`'s only value is the
    * specializer, so a value of `specializer.type`'s configuration is one of `C`'s. A backend carries what it built in
    * its `this.type` to its caller's `C` with it.
    */
  def sameType[C <: NativeSpecializer & Singleton](specializer: C): SameSpecializer[specializer.type, C] =
    SameSpecializer.of[specializer.type, C]

  /** The evidence that two configurations are one, when their specializers are one object, checked at run time: a
    * configuration's only value is its specializer, so `From` and `To` are one configuration exactly when `from` and
    * `to` are the same object; none otherwise. What reads a value whose configuration is known only as a wildcard (an
    * executor a module built, the entry a cell returned) in a known configuration again, after the check and never by
    * assumption.
    */
  def sameAs[From <: NativeSpecializer & Singleton, To <: NativeSpecializer & Singleton](from: From, to: To): Option[SameSpecializer[From, To]] =
    Option.when(from eq to)(SameSpecializer.of[From, To])

  extension [C <: NativeSpecializer & Singleton](specializer: C)

    /** The criterion T of the storage's view `v ∥ T` under this configuration. */
    def criterionOf(storage: NativeStorage): Configured[C] =
      sameType(specializer)[Configured](specializer.storageCriterion(storage))

    /** The storage's one-layer view `v ∥ T` under this configuration's families: one layer of native-free IR, its
      * children storages or terms the storage holds, all of this configuration. No API reads deeper; only a formatter
      * recurses over views, privately, writing text and building no IR.
      */
    def viewOf(storage: NativeStorage)(using access: StorageAccess): StorageView[Configured[C]] =
      if !access.readsViews then
        throw IllegalStateException(s"a storage's view read under a capability that reads native data only: $storage")
      sameType(specializer)[[Specializer <: NativeSpecializer & Singleton] =>> StorageView[Configured[Specializer]]](
        specializer.storageView(storage)
      )

    /** The storage read as untyped Scott ADT values, one layer, its outer filter dropped: a storage of one value as
      * the layer `λc1 … ck. ci f1 … fn` (the number k of its family's cases at its parameter, the position i of its
      * constructor among them, its view's value's field nodes), a group as its members; read from its native data by
      * this configuration's families, never through its view. The Scott ADT reading of a storage
      * (`gezi.weakhead.ScottADTChoices`) reads one layer this way, as an operation the storage supports natively.
      */
    def scottReadingOf(storage: NativeStorage)(using StorageAccess): ScottReading[Configured[C]] =
      sameType(specializer)[[Specializer <: NativeSpecializer & Singleton] =>> ScottReading[Configured[Specializer]]](
        specializer.storageScottReading(storage)
      )

    /** The parallel of the two sides, converted into its storage when it is the unique spelling of one. */
    def parallel(left: Configured[C], right: Configured[C]): Configured[C] =
      given C = specializer
      specializedOf(specializer)(Closed.of(left), Closed.of(right)) match
        case Some(specializedValue) =>
          Closed.configured(Closed.value(specializedValue)).getOrElse(
            throw IllegalStateException(s"the specialized parallel of two terms holds a suspension: $specializedValue")
          )
        case None => Configured.built(Interned.parallelOfTerms[IrLayer](left.representation, right.representation))

    /** The parallel of two closed values, converted into its storage when it is the unique spelling of one
      * (`Value.parallel` calls it).
      */
    def parallelOfClosed(left: Closed[C], right: Closed[C]): Value[C] =
      given C = specializer
      specializedOf(specializer)(left, right) match
        case Some(specializedValue) => Closed.value(specializedValue)
        case None                   => Value.parallelAsWritten(Closed.value(left), Closed.value(right))

    /** The application. */
    def application(function: Configured[C], argument: Configured[C]): Configured[C] =
      Configured.built(Interned[IrLayer](Apply.ofTerms(function.representation, argument.representation)))(using specializer)

    /** The binary choice. */
    def choice(left: Configured[C], right: Configured[C]): Configured[C] =
      Configured.built(Interned[IrLayer](Choice.ofTerms(left.representation, right.representation)))(using specializer)

    /** The thunk of the code with its holes, at least one, and its fillings. */
    def thunk(code: Code, holes: NonEmptyHoles, fillings: Vector[Configured[C]]): Configured[C] =
      Configured.built(Interned[IrLayer](Thunk.ofTerms(code, holes.toVector, fillings.map(_.representation))))(using specializer)

    /** The URI node of an absolute URI. */
    def uri(uri: java.net.URI): Configured[C] = Configured.built(Interned[IrLayer](UriNode(uri)))(using specializer)

    /** The opaque term of the name. */
    def opaque(name: String): Configured[C] = Configured.built(Interned[IrLayer](Opaque(name)))(using specializer)

    /** The term of a thunk layer of the code, the holes and the fillings, as the front end builds it: the thunk when it
      * has holes, else the closed instance of its code (`instance`), since a thunk without holes is no term.
      */
    def thunkOrInstance(code: Code, holes: Vector[Hole], fillings: Vector[Configured[C]]): Configured[C] =
      NonEmptyHoles.of(holes) match
        case Some(present) => thunk(code, present, fillings)
        case None          => instance(code, fillings)

    /** The closed instance of a code whose holes are all filled: its body with each slot replaced by its filling, built
      * layer by layer through this specializer, an inner thunk with holes a thunk, one with none its instance in turn.
      */
    def instance(code: Code, fillings: Vector[Configured[C]]): Configured[C] =
      // A code is written by the front end and is small next to the terms it is instantiated with; the recursion follows
      // the code's own nesting, not a term's.
      code.layer match
        case Slot(index)               => fillings(index)
        case Apply(function, argument) => application(instance(function, fillings), instance(argument, fillings))
        case Parallel(left, right)     => parallel(instance(left, fillings), instance(right, fillings))
        case Choice(left, right)       => choice(instance(left, fillings), instance(right, fillings))
        case Thunk(inner, holes, innerFillings) =>
          val filled = innerFillings.map(instance(_, fillings))
          NonEmptyHoles.of(holes) match
            case Some(present) => thunk(inner, present, filled)
            case None          => instance(inner, filled)

    /** The term of one layer over terms this configuration built, as the e-graph's write-back and the extraction's
      * spelling make it: a leaf the term itself, a storage's view `value ∥ criterion` built as a parallel (which gives
      * the storage back when it is its unique spelling), a thunk with no holes its instance, any other layer built here.
      */
    def layerBuilt(layer: LayerWith[Configured[C], Configured[C]]): Configured[C] =
      built(layer)(identity)

    /** The term of one layer over children of any kind (the e-graph's classes) whose terms `term` gives, built as
      * `layerBuilt` builds, with no layer over terms made on the way: the write-back's and the extraction's
      * construction.
      */
    def built[Child](layer: LayerWith[Child, Configured[C]])(term: Child => Configured[C]): Configured[C] =
      layer match
        case NoinlineLeaf(leaf)            => leaf
        case StorageView(value, criterion) => parallel(term(value), term(criterion))
        case Apply(function, argument)     => application(term(function), term(argument))
        case Parallel(left, right)         => parallel(term(left), term(right))
        case Choice(left, right)           => choice(term(left), term(right))
        case Thunk(code, holes, fillings) =>
          NonEmptyHoles.of(holes) match
            case Some(present) => thunk(code, present, fillings.map(term))
            case None          => instance(code, fillings.map(term))

    /** The term's one layer: a storage is a leaf, its view read only through `viewOf`; any other term its layer of the
      * IR over terms of this configuration.
      */
    def layer(term: Configured[C]): IrLayer[Configured[C]] = term.layer

    /** The library's terms read with no facts in this configuration's spelling, bottom up, each node converted where
      * its unique spelling has a storage here, each node shared among them built once: the one crossing of the library
      * into the facts, registered in the conversion table of https://github.com/Atry/private-overlay/issues/2261,
      * section 8. A term of no facts holds no storage.
      */
    def crossedAllFromNoFacts(terms: Iterable[Configured[NoFacts.type]]): Map[Configured[NoFacts.type], Configured[C]] =
      // A work list in post order, each node built once its children are, so that a term of any depth costs no frame
      // of the JVM stack.
      @scala.annotation.tailrec
      def crossedAll(pending: List[Instruction], crossed: Map[Instruction, Configured[C]]): Map[Instruction, Configured[C]] =
        pending match
          case Nil                                    => crossed
          case node :: rest if crossed.contains(node) => crossedAll(rest, crossed)
          case node :: rest =>
            val children = childrenOfNoFacts(node)
            children.filterNot(crossed.contains) match
              case Vector() => crossedAll(rest, crossed.updated(node, rebuilt(node, crossed)))
              case missing  => crossedAll(missing.toList ::: pending, crossed)
      val crossed = crossedAll(terms.toList.map(_.representation), Map.empty)
      terms.map(term => term -> crossed(term.representation)).toMap

    /** The node of no facts built again in this configuration's spelling, its children's images given. */
    private def rebuilt(node: Instruction, crossed: Map[Instruction, Configured[C]]): Configured[C] =
      node.layer match
        case Apply(function, argument) => application(crossed(function), crossed(argument))
        case Parallel(left, right)     => parallel(crossed(left), crossed(right))
        case Choice(left, right)       => choice(crossed(left), crossed(right))
        case Thunk(code, holes, fillings) =>
          val filled = fillings.map(crossed)
          NonEmptyHoles.of(holes) match
            case Some(present) => thunk(code, present, filled)
            case None          => instance(code, filled)
        case UriNode(address)       => uri(address)
        case Opaque(name)           => opaque(name)
        case storage: NativeStorage => throw IllegalStateException(s"a term of no facts holds a storage: $storage")

  /** The specializer's `specialized` in its caller's `C`. */
  private def specializedOf[C <: NativeSpecializer & Singleton](specializer: C)(left: Closed[C], right: Closed[C]): Option[Closed[C]] =
    val same = sameType[C](specializer)
    same[[Specializer <: NativeSpecializer & Singleton] =>> Option[Closed[Specializer]]](
      specializer.specialized(same.flip.apply[Closed](left), same.flip.apply[Closed](right))
    )

  /** The children of a node of [[NoFacts]], which holds no storage. */
  private def childrenOfNoFacts(node: Instruction): Vector[Instruction] = node.layer match
    case Apply(function, argument) => Vector(function, argument)
    case Parallel(left, right)     => Vector(left, right)
    case Choice(left, right)       => Vector(left, right)
    case Thunk(_, _, fillings)     => fillings
    case storage: NativeStorage    => throw IllegalStateException(s"a term of no facts holds a storage: $storage")
    case _                         => Vector.empty

/** The evidence that two singleton types of native specializers are one configuration, made only by
  * [[NativeSpecializer.sameType]] for a specializer's own type and the `C` it is the value of: what is of one is of the
  * other. One of the registered conversions of https://github.com/Atry/private-overlay/issues/2261, section 8: it is
  * sound because a singleton type has one value.
  */
final class SameSpecializer[From <: NativeSpecializer & Singleton, To <: NativeSpecializer & Singleton] private ():

  /** The value of `From`'s configuration as one of `To`'s: the same object. */
  def apply[Of[Specializer <: NativeSpecializer & Singleton]](value: Of[From]): Of[To] =
    // Registered conversion (issue 2261, section 8): `From` and `To` are one singleton type.
    value.asInstanceOf[Of[To]]

  /** The evidence the other way. */
  def flip: SameSpecializer[To, From] = SameSpecializer.of[To, From]

object SameSpecializer:
  private[ir] def of[From <: NativeSpecializer & Singleton, To <: NativeSpecializer & Singleton]: SameSpecializer[From, To] =
    new SameSpecializer[From, To]()

/** The native specializer of no facts: no representation is declared, so the specialized spelling is the IR everywhere
  * and no storage is ever built. The library and an entry's data are read under it, before the facts that come from
  * them exist; so are the judge's reference reading and the problem corpora.
  */
object NoFacts extends NativeSpecializer:
  protected def specialized(left: Closed[this.type], right: Closed[this.type]): Option[Closed[this.type]] = None

  protected def storageCriterion(storage: NativeStorage): Configured[this.type] =
    throw IllegalStateException(s"a term of no facts holds no storage: $storage")

  protected def storageView(storage: NativeStorage)(using StorageAccess): StorageView[Configured[this.type]] =
    throw IllegalStateException(s"a term of no facts holds no storage: $storage")

  protected def storageScottReading(storage: NativeStorage)(using StorageAccess): ScottReading[Configured[this.type]] =
    throw IllegalStateException(s"a term of no facts holds no storage: $storage")

/** The capability to read a native storage's view and data. A method reads a storage only when its signature asks
  * for this value, so that whether a piece of code can take a storage apart is visible in its type. It is made once,
  * where an entry is set up, and passed down as a parameter; the conventions project checks which files make it.
  */
final class StorageAccess private (
    /** Whether the capability reads views (`NativeSpecializer.viewOf`), not only native data. */
    val readsViews: Boolean
)

object StorageAccess:
  /** The capability. Called only where an entry or a test sets up its readers. */
  def granted(): StorageAccess = new StorageAccess(true)

  /** The capability to read a storage's native data (`NativeSpecializer.scottReadingOf`, the data a native or a block
    * reads) but not its view: a test runs a computation under it to show that the computation reads no view, a view
    * read throwing `IllegalStateException`. Called only by tests.
    */
  def dataOnly(): StorageAccess = new StorageAccess(false)

/** A storage read as untyped Scott ADT values, one layer, from its native data: a description, not a node of the IR. */
enum ScottReading[+Child]:

  /** The one layer `λc1 … ck. ci f1 … fn` of a storage of one value: `cases` is k, `chosen` is i (from 0), `fields`
    * the field nodes.
    */
  case Layer(cases: Int, chosen: Int, fields: Vector[Child])

  /** A group of storages, the choice of its members, each a storage of one value. */
  case Members(members: Vector[Child])

/** One layer of the term a native storage stands for, `value ∥ criterion`: a view, not a node. It is no layer of the
  * IR, so it is never interned, never a node of the e-graph and never a key; where a node is required, the storage
  * itself is that node.
  */
final case class StorageView[+Child](value: Child, criterion: Child)
