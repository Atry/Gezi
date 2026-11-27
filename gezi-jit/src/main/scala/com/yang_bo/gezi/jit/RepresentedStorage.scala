package com.yang_bo.gezi.jit

import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.ir.Value

import com.yang_bo.gezi.ir.ConstructorIdentity
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.Parallel
import com.yang_bo.gezi.weakhead.ListCodec
import com.yang_bo.gezi.weakhead.ListConstructor
import com.yang_bo.gezi.weakhead.ListRepresentation
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, Pure}
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex

/** A value of a representation, held as the JIT holds it (a `NativeValue`): a
  * native storage (`com.yang_bo.gezi.ir.NativeStorage`) of one IR term, its unique spelling
  * `C (f1 ∥ F1) … (fm ∥ Fm) ∥ T`, the one spelling that has a storage, the
  * storage and the term one to one: T the criterion the backend's facts name
  * for the representation (`StorageEncoding.criterionOf`), C the define bound
  * to the constructor of the value's outermost layer, and each field node
  * `fi ∥ Fi` the storage of the field's value, Fi the criterion of the field's
  * representation; a field whose representation holds its term as written
  * (`DataFamily.heldAsWritten`, the criterion Ω) is that term, `x ∥ Ω` being x;
  * and a field a declared family filters by a criterion F of no family
  * (`FilteredFamily`) is the node `f ∥ F` itself, unread. A list of items i1 …
  * in of the element E is `cons (i1 ∥ E) s ∥ list_type E`, s the storage of the
  * rest, and the empty list `nil ∥ list_type E`; an item node `i ∥ E` is the
  * storage of i when the encoding converts it (`StorageEncoding.parallel`). A
  * cell cons's native makes under the default construction holds its tail as
  * given, not the unique spelling (the FIXME at `ListRepresentation.Cell`,
  * https://github.com/Atry/private-overlay/issues/2202). The JIT eliminates a
  * storage as C ȳ, dropping the outer `∥ T`, by the pattern theorem of the
  * unique spelling (`C ȳ ∥ T ≃_O C ȳ` when each field carries the filter T
  * implies; `docs/design/gezi-set-equations-proofs.md`, section 23).
  *
  * The JIT reads a storage as its own head, never through its view: every
  * extractor of `JitValue` but `JitValue.Represented` gives none for it. Its
  * hash code comes from its representation and its value, at the cost of the
  * value, never of the view (a declared family's one layer from its field
  * nodes' hash codes, `ConstructedStorage`); the view is read by the
  * configuration's specializer when a reader outside the JIT asks for it, one
  * layer, its field storages interned, and never kept on the storage, which
  * several configurations may read differently.
  *
  * A storage the JIT makes is interned through the pool (`Interned.stored`),
  * one object per storage, and is never equal to a constructor object.
  */
abstract class RepresentedStorage[+Term] protected () extends NativeStorage:

  /** The storage's representation: for a codec of no parameter its class's
    * constant (the class is the codec), for one with a parameter that varies
    * within the codec (a word's width, a list's element criterion, an array
    * list's element, a declared family's criterion and parameters) the
    * parameter it holds. No codec's name is held.
    */
  def representation: Representation[Term]

  /** The value as a `NativeValue`, the data of one layer the family's codec
    * takes apart and builds (`DataFamily.layer`, `built`): made from the
    * storage's own data when first asked and kept; a declared family's storage
    * is its own value (`ConstructedStorage`). A subclass that holds its value's
    * data unboxed (a natural's `BigInt`, a bit tuple's `Long`) is read by a
    * consumer that knows its class, with no `NativeValue` made.
    */
  def value: NativeValue[Term]

  /** Whether the other storage, of the same class and representation, holds the
    * same data.
    */
  protected def sameData(that: RepresentedStorage[?]): Boolean

  /** The hash code of the storage's representation and of the value it holds, a
    * function of its native data with no view built: a storage equals storages
    * only, never an ordinary node (conversion happens before interning), so its
    * hash code agrees with storages' equality and need not be its view's.
    * Computed when first asked.
    */
  lazy val contentHash: Int = 31 * representation.## + value.##

  // TODO: deleted: `viewValue`, the view's value spelled from the storage's own `encoding` and kept on the storage.
  // Wrong because the view depends on the entry's families, which the storage does not hold, and a view kept on a
  // storage shared between entries is one entry's; issue https://github.com/Atry/private-overlay/issues/2261, design
  // v38, sections 2 and 11.
  // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/RepresentedStorage.scala`.

  /** The objects the storage holds, read off its own data with no
    * configuration: the terms of fields held as written, a list cell's item and
    * tail, a declared value's fields, the members' chain of a group. Empty for
    * a storage of native data alone.
    */
  protected def held: Vector[Any]

  protected final lazy val termChildren: IArray[AnyRef] =
    IArray.from(held.map(_.asInstanceOf[AnyRef]))

  /** Whether no held object holds a neutral value, computed once from the held
    * objects, made before the storage.
    */
  final lazy val closed: Boolean =
    held.forall(com.yang_bo.gezi.ir.ConstructorIdentity.closed)

  /** Whether no held object holds a value extension, computed once as `closed`
    * is.
    */
  final lazy val suspensionFree: Boolean =
    held.forall(com.yang_bo.gezi.ir.ConstructorIdentity.suspensionFree)

  /** Whether the storage may be handed over whole as a Scott ADT value
    * (`NativeStorage.handedOverWhole`): every held object is a storage that may
    * itself, and none is a group, which under a constructor stands for a choice
    * of members.
    */
  final lazy val handedOverWhole: Boolean = held.forall {
    case _: GroupStorage[?]             => false
    case storage: com.yang_bo.gezi.ir.NativeStorage => storage.handedOverWhole
    case _                              => false
  }

  /** False: the e-graph reads the storage through its one-layer view; a storage
    * of a constant whose view no typed round rewrites says true.
    */
  def leafInEGraph: Boolean = false

  /** False: a storage whose size grows with its value's. */
  def constantSize: Boolean = false

  /** Whether this storage comes strictly before the other in the canonical
    * order (`RepresentedStorage.canonicalOrder`): of one class and one
    * representation, and ordered by their data, with no configuration read.
    */
  def precedes(other: com.yang_bo.gezi.ir.NativeStorage): Boolean = other match
    case that: RepresentedStorage[?] =>
      (that.getClass eq getClass) && that.representation == representation &&
      RepresentedStorage.canonicalOrder(this, that).exists(_ < 0)
    case _ => false

  /** Whether the other storage holds the same content: one class (which is the
    * codec), one representation (the parameters within the codec, a declared
    * family's criterion) and the same data. No configuration is compared.
    */
  def sameContent(other: NativeStorage): Boolean = other match
    case that: RepresentedStorage[?] =>
      (that.getClass eq getClass) && that.contentHash == contentHash && that.representation == representation &&
      sameData(that)
    case _ => false

  /** The position of the value's outermost constructor among its family's cases
    * at its parameter (`constructorIndex`), for the configuration's Scott ADT
    * reading of the storage.
    */
  private[jit] final def constructorPositionWithin: Int = constructorIndex

  /** The parameter of the storage's family its representation names (a word's
    * width, a binary natural's set), read off the representation it holds: no
    * configuration.
    */
  protected final def dataParameter: Option[FamilyParameter[Term]] =
    representation match
      case Representation.Data(_, parameter) => parameter
      case _                                 => None

  override def toString: String =
    s"RepresentedStorage(${representation.familyIdentity.shown}, $value)"

/** The terms the storages of one backend's facts encode their values with: the
  * constructors the facts bind and the criteria they name, read once per facts
  * (`BackendFacts.storageEncoding`). A pure function of the facts, equal to
  * another when they read the same criteria and bound terms (see the FIXME at
  * `key`).
  */
// The backend's native specializer: the one conversion of its
// facts, and the only entry of its storages to the pool.
final class StorageEncoding(val facts: BackendFacts)
    extends com.yang_bo.gezi.ir.NativeSpecializer:

  /** The encoding's operations in its own singleton type, made once, so that
    * their tables are built once per facts.
    */
  private[jit] lazy val ownOperations: StorageEncodingOperations[this.type] =
    StorageEncodingOperations[this.type](this)

  /** The specialized object of `left ∥ right`
    * (`StorageEncodingOperations.specializedValue`): a storage, a group or the
    * already filtered side.
    */
  protected def specialized(
      left: Closed[this.type],
      right: Closed[this.type]
  ): Option[Closed[this.type]] =
    ownOperations.specializedClosed(left, right)

  /** The storage's criterion under this configuration
    * (`NativeSpecializer.criterionOf`).
    */
  protected def storageCriterion(
      storage: com.yang_bo.gezi.ir.NativeStorage
  ): Configured[this.type] =
    ownOperations.criterionOfStorage(storage)

  /** The storage's one-layer view under this configuration's families
    * (`NativeSpecializer.viewOf`).
    */
  protected def storageView(storage: com.yang_bo.gezi.ir.NativeStorage)(using
      com.yang_bo.gezi.ir.StorageAccess
  ): com.yang_bo.gezi.ir.StorageView[Configured[this.type]] =
    ownOperations.viewOfStorage(storage)

  /** The storage read as untyped Scott ADT values
    * (`StorageEncodingOperations.scottReadingOfStorage`).
    */
  protected def storageScottReading(storage: com.yang_bo.gezi.ir.NativeStorage)(using
      com.yang_bo.gezi.ir.StorageAccess
  ): com.yang_bo.gezi.ir.ScottReading[Configured[this.type]] =
    ownOperations.scottReadingOfStorage(storage)

  /** The pool's object of a storage this backend made
    * (`StorageEncodingOperations.stored`), in the encoding's own type.
    */
  private[jit] def storedOwn(
      storage: com.yang_bo.gezi.ir.NativeStorage
  ): Configured[this.type] = storedTerm(storage)

object StorageEncoding:

  extension [C <: NativeSpecializer & Singleton](encoding: StorageEncoding & C)

    /** The encoding's operations in the caller's configuration `C`, whose only
      * value is the encoding.
      */
    def operations: StorageEncodingOperations[C] =
      NativeSpecializer.sameType[C](encoding)[StorageEncodingOperations](
        encoding.ownOperations
      )

/** The terms the storages of one backend's facts encode their values with: the
  * constructors the facts bind and the criteria they name, read once per facts
  * (`BackendFacts.storageEncoding`, `StorageEncoding.operations`), every term
  * of the configuration `C` of the encoding.
  */
final class StorageEncodingOperations[C <: NativeSpecializer & Singleton](
    encoding: StorageEncoding & C
):

  /** A value of this configuration. */
  type Term = JitValue[C]

  /** The specializer in scope of its own constructions (`Value.Apply` and the
    * others).
    */
  private given self: C = encoding

  private def facts: BackendFacts = encoding.facts

  /** A pure key of the facts as a value of this configuration: the same object
    * (`Configured.fromPure`).
    */
  private def pureTerm(key: Pure): Term =
    Value.of(Configured.fromPure(encoding)(key))

  /** The library's index in this configuration, its lemmas' sides crossed into
    * it once (`StandardLibraryIndex.crossed`): the part of the facts that holds
    * terms of the program's kind (the design's `LibraryIn[C]`).
    */
  lazy val index: StandardLibraryIndex[C] =
    StandardLibraryIndex.crossed(facts.index, encoding)

  /** The leaves of the index, terms of this configuration. */
  lazy val leaves: Set[Configured[C]] =
    facts.leaves.map(Configured.fromPure(encoding))

  /** The family each criterion names, by the criterion's term in this
    * configuration.
    */
  lazy val criterionFamily: Map[Term, FamilyIdentity] =
    facts.criterionFamily.map((key, family) => pureTerm(key) -> family)

  /** The natives bound to each define, by the define's term in this
    * configuration.
    */
  lazy val natives: Map[Term, Vector[BoundNative]] =
    facts.natives.map((key, bound) => pureTerm(key) -> bound)

  /** The terms bound to each native, in this configuration. */
  lazy val definesBound: Map[NativeName, Vector[Term]] =
    facts.definesBound.map((native, defines) => native -> defines.map(pureTerm))

  /** The first native of at least one parameter bound to the define
    * (`BackendFacts.nativeOfParameters`).
    */
  def nativeOfParameters(define: Term): Option[BoundNative] =
    natives.getOrElse(define, Vector.empty).find(_.parameterCount > 0)

  /** Whether some native of the set is bound to the define
    * (`BackendFacts.bound`).
    */
  def bound(define: Term): Boolean = natives.contains(define)

  private lazy val nativeBoundTerms: Set[Term] =
    definesBound.values.flatten.toSet

  /** Whether the term is bound to a native (`BackendFacts.isBoundToNative`). */
  def isBoundToNative(term: Term): Boolean = nativeBoundTerms.contains(term)

  /** The term bound to the native when exactly one is
    * (`BackendFacts.boundDefine`), in this configuration.
    */
  def boundDefine(native: NativeName): Option[Term] =
    facts.boundDefine(native).map(pureTerm)

  /** The term a codec encodes the constructor with
    * (`BackendFacts.constructorDefine`), in this configuration.
    */
  def constructorTerm(native: NativeName): Term = pureTerm(
    facts.constructorDefine(native)
  )

  /** The backend's constants in this configuration: each constant's head with
    * its native's value computed here.
    */
  lazy val constants: Vector[BackendConstant[Term]] =
    facts.constantHeads.map(head =>
      BackendConstant(
        head.code,
        head.holes,
        head.native.implementation(Vector.empty),
        head.place
      )
    )

  /** The specialized object of `left ∥ right` (`specializedValue`): a storage,
    * a group or the already filtered side.
    */
  def specializedClosed(left: Closed[C], right: Closed[C]): Option[Closed[C]] =
    // A storage, a group or a side of two closed values holds no neutral value: the result is closed by construction.
    specializedValue(Closed.value(left), Closed.value(right)).map(found =>
      Value
        .closed(found)
        .getOrElse(
          throw IllegalStateException(
            s"the specialized parallel of two closed values is open: $found"
          )
        )
    )

  /** The pool's object of a storage of this encoding, made from native data by
    * this backend (a native's result, a block's output, a decode point's
    * value): the only entry of a storage to the pool, besides the conversion.
    */
  def stored(
      storage: RepresentedStorage[Term] | GroupStorage[Term]
  ): Configured[C] =
    NativeSpecializer.sameType[C](encoding)[Configured](
      encoding.storedOwn(storage)
    )

  // TODO: deleted: `key`, `equals` and `hashCode`, which made two encodings equal when their two maps were, leaving out
  // the native backend's families and the bound defines, so that the pool shared storages between encodings that
  // convert one term differently (https://github.com/Atry/private-overlay/issues/2263). Wrong because a storage is to
  // hold no encoding at all, so no equality of encodings enters interning; issue
  // https://github.com/Atry/private-overlay/issues/2261, design v38, section 2.
  // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/RepresentedStorage.scala`.

  private lazy val criteriaByFamily: Map[FamilyIdentity, Vector[Term]] =
    facts.criterionFamily.toVector.groupMap(_._2)(entry => pureTerm(entry._1))

  /** The one criterion that names the family. Throws `IllegalStateException`
    * when the facts name it by none or by several, a configuration whose values
    * of the family have no one criterion to be stored under.
    */
  private def head(family: FamilyIdentity): Term = family match
    case FamilyIdentity.Declared(criterion) => pureTerm(criterion)
    case _                                  =>
      criteriaByFamily.getOrElse(family, Vector.empty) match
        case Vector(only) => only
        case found        =>
          throw IllegalStateException(
            s"the facts name the family ${family.shown} by ${found.size} criteria, not one: $found"
          )

  /** The storage's criterion under this configuration
    * (`NativeSpecializer.criterionOf`): what its representation names by this
    * entry's facts.
    */
  def criterionOfStorage(storage: com.yang_bo.gezi.ir.NativeStorage): Configured[C] =
    StorageOf.representationOf[C](storage) match
      case Some(representation) => termOf(criterionOf(representation))
      case None                 =>
        throw IllegalStateException(
          s"a storage of no backend of this module: $storage"
        )

  /** The storage's one-layer view `v ∥ T` under this configuration's families
    * (`NativeSpecializer.viewOf`).
    */
  def viewOfStorage(
      storage: com.yang_bo.gezi.ir.NativeStorage
  )(using com.yang_bo.gezi.ir.StorageAccess): com.yang_bo.gezi.ir.StorageView[Configured[C]] =
    com.yang_bo.gezi.ir.StorageView(
      termOf(layerValueOf(typedStorage(storage))),
      criterionOfStorage(storage)
    )

  /** The storage read as untyped Scott ADT values
    * (`NativeSpecializer.scottReadingOf`): a group as its members; any other
    * storage as its layer `λc1 … ck. ci f1 … fn`, the cases its family has at
    * its parameter, its constructor's position among them, and the field nodes
    * of its view's value, read from the storage's native data by this
    * configuration's families, its view not read.
    */
  def scottReadingOfStorage(
      storage: com.yang_bo.gezi.ir.NativeStorage
  ): com.yang_bo.gezi.ir.ScottReading[Configured[C]] =
    (storage: AnyRef) match
      case group: GroupStorage[?] =>
        val members = StorageOf
          .groupOfStorage[C](group)
          .members
          .map(member => termOf(StorageOf.value(member)))
        com.yang_bo.gezi.ir.ScottReading.Members(members)
      case _ => scottLayer(typedStorage(storage))

  private def scottLayer(
      represented: RepresentedStorage[Term]
  ): com.yang_bo.gezi.ir.ScottReading[Configured[C]] =
    val representation = represented.representation
    val chosen = represented.constructorPositionWithin
    val (cases, fieldCount) = representation match
      case Representation.ListOf(_) | Representation.ArrayListOf(_) =>
        (
          ListConstructor.values.size,
          if chosen == ListCodec.position(ListConstructor.Cons) then 2 else 0
        )
      case Representation.Data(identity, parameter) =>
        val constructors = family(identity).constructors(parameter)
        (constructors.size, constructors(chosen).fields.size)
    // The last arguments of the view's value are the fields: the constructor's define may itself be an application.
    val fields = Value.Spine
      .of(layerValueOf(represented))
      ._2
      .takeRight(fieldCount)
      .map(termOf)
    com.yang_bo.gezi.ir.ScottReading.Layer(cases, chosen, fields)

  private def typedStorage(
      storage: com.yang_bo.gezi.ir.NativeStorage
  ): RepresentedStorage[Term] =
    StorageOf
      .typed[C](storage)
      .getOrElse(
        throw IllegalStateException(
          s"a storage of no backend of this module: $storage"
        )
      )

  /** The value `C ȳ` of the storage's view, one layer: a declared family's
    * constructor define applied to the field nodes the storage holds, any other
    * storage's spelling of its native data (`spelled`).
    */
  private def layerValueOf(represented: RepresentedStorage[Term]): Term =
    StorageOf.constructed[C](represented) match
      case Some(constructed) =>
        constructed.fields.foldLeft(
          Value.of(
            constructorDefine(
              represented.representation,
              constructed.constructor
            )
          )
        )(Value.Apply(_, _))
      case None => spelled(represented.representation, represented.value)

  /** The term a value of this configuration's view or criterion is: a view and
    * a criterion hold no neutral value and no suspension, being built from the
    * facts and from what the storage holds, which a storage of a term holds
    * closed.
    */
  private def termOf(value: Term): Configured[C] =
    Closed
      .configured(value)
      .getOrElse(
        throw IllegalStateException(
          s"a storage's view or criterion is no term: $value"
        )
      )

  /** The criterion the facts name for the representation: the family's
    * criterion, applied to its criterion parameters or to the encoding of its
    * value parameter; a list's criterion applied to its element filter.
    */
  def criterionOf(representation: Representation[Term]): Term =
    representation match
      case Representation.ListOf(element) =>
        JitValue.Apply(head(Representation.listFamily), element)
      case Representation.ArrayListOf(element) =>
        JitValue.Apply(
          head(Representation.arrayListFamily),
          criterionOf(element)
        )
      case Representation.Data(identity, None) => head(identity)
      case Representation.Data(
            FilteredFamily.identity,
            Some(FieldFilter(criterion))
          ) =>
        criterion
      case Representation.Data(identity, Some(CriterionParameters(criteria))) =>
        criteria.foldLeft(head(identity))((function, parameter) =>
          JitValue.Apply(function, criterionOf(parameter))
        )
      case Representation.Data(identity, Some(parameter)) =>
        val parameterFamily = family(identity).parameterFamily.getOrElse(
          throw IllegalStateException(
            s"the family ${identity.shown} takes no value parameter, given $parameter"
          )
        )
        JitValue.Apply(
          head(identity),
          plainTerm(
            Representation.Data(parameterFamily, None),
            family(identity).parameterValue(parameter)
          )
        )

  private def family(identity: FamilyIdentity): DataFamily =
    facts.nativeBackend
      .family(identity)
      .getOrElse(
        throw IllegalStateException(
          s"no data family ${identity.shown} in the backend"
        )
      )

  /** Whether a field of the representation holds its term as written: a family
    * held as written (`DataFamily.heldAsWritten`, the criterion Ω) or a filter
    * of no family (`FilteredFamily`), whose field node is a term and never a
    * storage of the field's value.
    */
  def holdsAsWritten(representation: Representation[Term]): Boolean =
    representation match
      case Representation.Data(FilteredFamily.identity, _) => true
      case Representation.Data(identity, _)                =>
        facts.nativeBackend.family(identity).exists(_.heldAsWritten)
      case Representation.ListOf(_) | Representation.ArrayListOf(_) => false

  /** The representations of the fields of the family's constructor at the
    * parameter.
    */
  def fieldRepresentations(
      identity: FamilyIdentity,
      parameter: Option[FamilyParameter[Term]],
      constructor: Int
  ): Vector[Representation[Term]] =
    family(identity)
      .constructors(parameter)(constructor)
      .fields
      .map(_.representation(parameter))

  /** The term of nil, the list's constructor 0, in this configuration. */
  lazy val nilTerm: Term = pureTerm(facts.nil)

  /** The term of cons, the list's constructor 1, in this configuration. */
  lazy val consTerm: Term = pureTerm(facts.cons)

  /** The value spelled with plain constructors, every layer, as a criterion
    * applied to a value parameter is written (`criterionOf`): the constructors
    * of its data layers applied to their fields, a field kept unread as the JIT
    * holds it; a list's cells over its items, each filtered by the element
    * through this native specializer, ending in nil. It builds a criterion's
    * term from the facts' parameter value, never a program's storage taken
    * apart.
    */
  private def plainTerm(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Term =
    plainOf(representation, value).result

  private def plainOf(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): TailRec[Term] =
    (representation, value) match
      case (Representation.Data(identity, parameter), _) =>
        val dataFamily = family(identity)
        val DataLayer(constructor, fields) = dataFamily.layer(parameter, value)
        val atParameter = dataFamily.constructors(parameter)(constructor)
        plainFields(
          atParameter.fields
            .zip(fields)
            .map((field, fieldValue) =>
              (field.representation(parameter), fieldValue)
            )
            .toList,
          Vector.empty
        )
          .map(
            _.foldLeft(constructorTerm(atParameter.native))(
              JitValue.Apply(_, _)
            )
          )
      case (Representation.ListOf(element), NativeValue.Listed(list)) =>
        val items = listItems(list)
        done(
          items.foldRight(nilTerm)((item, rest) =>
            JitValue.Apply(
              JitValue.Apply(consTerm, Value.Parallel(item, element)),
              rest
            )
          )
        )
      case (
            Representation.ArrayListOf(element),
            listed: NativeValue.ArrayListed
          ) =>
        done(
          listed.suffix.foldRight(nilTerm)((item, rest) =>
            JitValue.Apply(
              JitValue.Apply(
                consTerm,
                plainTerm(element, arrayElement(element, item))
              ),
              rest
            )
          )
        )
      case _ =>
        throw IllegalStateException(
          s"a value of another representation than ${representation.familyIdentity.shown}: $value"
        )

  /** The value of an array list's element, a scalar of the element
    * representation: a binary natural, or a 32-bit word held as a JVM `int`.
    */
  def arrayElement(
      element: Representation[Term],
      item: ArrayItem
  ): NativeValue[Term] = (element.familyIdentity, item) match
    case (BinaryNaturalFamily.identity, natural: java.math.BigInteger) =>
      BinaryNatural(BigInt(natural))
    case (JvmIntFamily.identity, bits: Int) => JvmIntNatives.value(bits)
    case (other, _)                         =>
      throw IllegalStateException(
        s"an array list of ${other.shown} does not hold $item"
      )

  /** The element representations whose array lists this encoding makes: the
    * binary naturals, canonical and positive, when the facts name their
    * criterion; and the 32-bit words held as a JVM `int`, when the encoding
    * converts them.
    */
  private lazy val arrayElementRepresentations: Vector[Representation[Term]] =
    (if criteriaByFamily
         .getOrElse(BinaryNaturalFamily.identity, Vector.empty)
         .size == 1
     then Vector(BinaryNaturalNatives.canonical, BinaryNaturalNatives.positive)
     else Vector.empty) ++ Vector(JvmIntNatives.jvmInt).filter(converts)

  /** The array lists' representations the encoding makes storages of. */
  lazy val arrayListRepresentations: Vector[Representation[Term]] =
    arrayElementRepresentations
      .map(Representation.ArrayListOf(_))
      .filter(converts)

  /** An array list's value of the elements, from the first, its suffixes'
    * content hash codes computed in one pass when first asked.
    */
  def arrayList(
      representation: Representation[Term],
      values: Vector[ArrayItem]
  ): NativeValue.ArrayListed =
    require(
      values.forall(ArrayElements.holds(representation, _)),
      s"an array list of $representation holds its elements' kind only"
    )
    NativeValue.ArrayListed(
      ArrayElements(values, representation.asConstant, None),
      0
    )

  /** An array list's value of the item before the suffix: new elements whose
    * content's hash codes are the suffix's with the item's one step before
    * them, so that a list built by cons costs one step a cell.
    */
  def arrayConsed(
      representation: Representation[Term],
      item: ArrayItem,
      rest: NativeValue.ArrayListed
  ): NativeValue.ArrayListed =
    // TODO: deleted: the run-time `require` that the rest's elements are of this representation and of this encoding
    // (the elements' own `encoding` field). Wrong because the elements hold no configuration; issue
    // https://github.com/Atry/private-overlay/issues/2261, design v38, section 2.
    // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/RepresentedStorage.scala`.
    require(
      ArrayElements.holds(representation, item),
      s"an array list of $representation does not hold $item"
    )
    val restContent = rest.elements.contentHashes.drop(rest.start)
    NativeValue.ArrayListed(
      ArrayElements(
        item +: rest.suffix,
        representation.asConstant,
        Some((31 * restContent.head + item.hashCode) +: restContent)
      ),
      0
    )

  /** The array list under the target representation of the same elements, when
    * it holds them: the empty list under any target, whatever its elements'
    * family; a nonempty list under a target of its elements' family each of
    * whose elements the target admits (`elementAdmitted`), none otherwise. The
    * list itself when it already is of the target; otherwise new elements of
    * the suffix, sharing its vector and its content's hash codes, with no
    * element read again for a target that admits every element of the family.
    * Its storage is the unique spelling
    * `storageOf(target, arrayList(target, values))` gives (proofs, section 26,
    * lemma 26.2; section 23 for the empty list).
    */
  def relabelled(
      listed: NativeValue.ArrayListed,
      target: Representation[Term]
  ): Option[NativeValue.ArrayListed] =
    // TODO: deleted: the run-time `require` that the list's elements are of this encoding (their own `encoding` field).
    // Wrong because the elements hold no configuration; issue https://github.com/Atry/private-overlay/issues/2261,
    // design v38, section 2.
    // Read it back with `git show 7669694cc:gezi/jit/src/main/scala/gezi/jit/RepresentedStorage.scala`.
    require(
      arrayListRepresentations.contains(target),
      s"the encoding makes no array lists of $target"
    )
    val (source, wanted) =
      (arrayElementOf(listed.elements.representation), arrayElementOf(target))
    if listed.elements.representation == target then Some(listed)
    else if listed.nil then Some(arrayList(target, Vector.empty))
    else if source.familyIdentity != wanted.familyIdentity then None
    else
      val suffix = listed.suffix
      Option.when(holdsEvery(target, suffix))(
        NativeValue.ArrayListed(
          ArrayElements(
            suffix,
            target.asConstant,
            Some(listed.elements.contentHashes.drop(listed.start))
          ),
          0
        )
      )

  /** Whether every element is of the array list representation's element
    * representation (`elementAdmitted`), with no element read for one that
    * admits every value of its family.
    */
  def holdsEvery(
      representation: Representation[Term],
      values: Vector[ArrayItem]
  ): Boolean =
    val element = arrayElementOf(representation)
    admitsEveryElement(element) || values.forall(elementAdmitted(element, _))

  /** The element representation of an array list's. */
  private def arrayElementOf(
      representation: Representation[Term]
  ): Representation[Term] = representation match
    case Representation.ArrayListOf(element) => element
    case other                               =>
      throw IllegalStateException(s"an array list's elements under $other")

  /** Whether the element representation admits every value of its family: no
    * constructor of the family is excluded at its parameter.
    */
  private def admitsEveryElement(element: Representation[Term]): Boolean =
    element match
      case Representation.Data(identity, parameter) =>
        val dataFamily = family(identity)
        dataFamily
          .constructors(parameter)
          .indices
          .forall(!dataFamily.excluded(parameter, _))
      case other =>
        throw IllegalStateException(s"an array list's element of $other")

  /** Whether the element, a value of the element representation's family, is of
    * the representation: the constructor of its outermost layer, read where the
    * family's every constructor appears (`shapeParameters`), is not excluded at
    * the representation's parameter. One layer suffices for the elements an
    * array list holds (`arrayElementRepresentations`), whose fields' parameters
    * do not depend on the outer one: a positive natural is one whose outermost
    * constructor is not zero.
    */
  private def elementAdmitted(
      element: Representation[Term],
      item: ArrayItem
  ): Boolean = element match
    case Representation.Data(identity, parameter) =>
      val dataFamily = family(identity)
      val shape = dataFamily.shapeParameters.headOption.getOrElse(
        throw IllegalStateException(s"${identity.shown} has no shape parameter")
      )
      !dataFamily.excluded(
        parameter,
        dataFamily.taken(shape, arrayElement(element, item)).constructor
      )
    case other =>
      throw IllegalStateException(s"an array list's element of $other")

  private def plainFields(
      fields: List[(Representation[Term], NativeValue[Term])],
      found: Vector[Term]
  ): TailRec[Vector[Term]] =
    fields match
      case Nil                                   => done(found)
      case (_, NativeValue.Unread(term)) :: rest =>
        tailcall(plainFields(rest, found :+ term))
      case (fieldRepresentation, fieldValue) :: rest =>
        tailcall(plainOf(fieldRepresentation, fieldValue)).flatMap(encoded =>
          plainFields(rest, found :+ encoded)
        )

  /** The items of a whole list. Throws `IllegalStateException` for a cell,
    * whose tail is not read.
    */
  def listItems(list: ListRepresentation[Term]): Vector[Term] = list match
    case ListRepresentation.Items(_, items)   => items
    case cell @ ListRepresentation.Cell(_, _) =>
      throw IllegalStateException(s"a cell's items are not read: $cell")

  /** The value as a storage holds it: a list of items made into its first cell,
    * over the storages of the rest, built from the end; any other value as it
    * is.
    */
  def oneLayer(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): NativeValue[Term] = (representation, value) match
    case (
          Representation.ListOf(element),
          NativeValue.Listed(ListRepresentation.Items(length, items))
        ) if items.nonEmpty =>
      val rest = items.tail.foldRight(
        storageOf(
          representation,
          NativeValue.Listed(ListRepresentation.Items(0, Vector.empty))
        )
      )((item, tail) =>
        storageOf(
          representation,
          NativeValue.Listed(ListRepresentation.Cell(item, tail))
        )
      )
      NativeValue.Listed(
        ListRepresentation.Cell(specializedItem(items.head, element), rest)
      )
    case (
          Representation.ListOf(element),
          NativeValue.Listed(ListRepresentation.Cell(item, tail))
        ) =>
      NativeValue.Listed(
        ListRepresentation.Cell(specializedItem(item, element), tail)
      )
    case _ => value

  /** The item a cell holds, so that two cells are equal exactly when their
    * views are: the storage its node `item ∥ E` converts to (`parallel`), which
    * is the item itself when the item already is that storage, and the item as
    * given otherwise, its node then the parallel `item ∥ E`.
    */
  private def specializedItem(item: Term, element: Term): Term =
    Value.Parallel(item, element) match
      case JitValue.Parallel(asGiven, _) => asGiven
      case converted                     => converted

  /** The storage of the value, interned (`Interned.stored`): one object for one
    * value of one representation under this encoding.
    */
  def storageOf(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Term =
    // The encoding's own type and the caller's `C` are one configuration (`NativeSpecializer.sameType`).
    val same = NativeSpecializer.sameType[C](encoding)
    val storage = RepresentedStorage(
      encoding,
      same.flip[[S <: NativeSpecializer & Singleton] =>> Representation[
        JitValue[S]
      ]](representation),
      same.flip[[S <: NativeSpecializer & Singleton] =>> NativeValue[
        JitValue[S]
      ]](value)
    )
    Value.of(
      stored(
        same[[S <: NativeSpecializer & Singleton] =>> RepresentedStorage[
          JitValue[S]
        ]](storage)
      )
    )

  /** The term v of a storage's view `v ∥ T`, one layer of the unique spelling:
    * the define bound to the outermost layer's constructor applied to its field
    * nodes (`fieldNode`); for a list, nil, or cons applied to its first item's
    * node `i ∥ E` (`parallel`) and to the storage of the rest. The field
    * storages are interned, so a field term has one object.
    */
  def spelled(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Term =
    (representation, value) match
      case (Representation.Data(identity, parameter), _) =>
        val dataFamily = family(identity)
        val DataLayer(constructor, fields) = dataFamily.layer(parameter, value)
        val atParameter = dataFamily.constructors(parameter)(constructor)
        atParameter.fields
          .zip(fields)
          .map((field, fieldValue) =>
            fieldNode(field.representation(parameter), fieldValue)
          )
          .foldLeft(constructorTerm(atParameter.native))(JitValue.Apply(_, _))
      case (
            Representation.ListOf(_),
            NativeValue.Listed(ListRepresentation.Items(0, _))
          ) =>
        nilTerm
      case (
            Representation.ListOf(element),
            NativeValue.Listed(ListRepresentation.Cell(item, tail))
          ) =>
        JitValue.Apply(
          JitValue.Apply(consTerm, Value.Parallel(item, element)),
          tail
        )
      case (
            Representation.ArrayListOf(element),
            listed: NativeValue.ArrayListed
          ) =>
        if listed.nil then nilTerm
        else
          JitValue.Apply(
            JitValue.Apply(
              consTerm,
              storageOf(
                element,
                arrayElement(element, listed.elements.values(listed.start))
              )
            ),
            storageOf(
              representation,
              NativeValue.ArrayListed(listed.elements, listed.start + 1)
            )
          )
      case _ =>
        throw IllegalStateException(
          s"a value of another representation than ${representation.familyIdentity.shown}: $value"
        )

  /** The node of a field in the unique spelling: the term the field holds for a
    * field held as written (its criterion Ω, `x ∥ Ω` being x) or filtered by a
    * criterion of no family (the node `f ∥ F` itself), otherwise the storage of
    * the field's value, whose view is `f ∥ F`.
    */
  private def fieldNode(
      fieldRepresentation: Representation[Term],
      fieldValue: NativeValue[Term]
  ): Term = fieldValue match
    case NativeValue.Unread(term) => term
    case _                        => storageOf(fieldRepresentation, fieldValue)

  /** The define bound to the constructor of the family of the representation,
    * at its parameter.
    */
  def constructorDefine(
      representation: Representation[Term],
      constructor: Int
  ): Configured[C] = representation match
    case Representation.Data(identity, parameter) =>
      Configured.fromPure(encoding)(
        facts.constructorDefine(
          family(identity).constructors(parameter)(constructor).native
        )
      )
    case other =>
      throw IllegalStateException(s"no data family's constructor in $other")

  /** The node `left ∥ right` as a configuration that converts builds it, before
    * it is interned: left itself when left is a storage of this encoding whose
    * criterion is right, or is already written `l ∥ right` (`filteredAlready`),
    * by (4) and the idempotence of ∥ (`unions_parallel_idempotence`); the
    * storage of the unique spelling when `left ∥ right` is one (`converted`);
    * the parallel otherwise. O(width): it reads one layer and the field nodes'
    * classes.
    *
    * The one admission of every construction site, the reader's and the JIT's
    * alike: a term is converted, or a run grouped, only when its criterion and
    * every field node (or the run) is an instruction
    * (`ConstructorIdentity.isInstruction`, one field read; a storage answers
    * its own), so that a storage is a closed term of instructions, one object
    * for one term (#2163 B1), and its readback is an instruction. A term over
    * the JIT's own layers (a sharing cell, an evaluation passed on, a carried
    * value) or an open term stays the parallel. Under the converting
    * construction that means fewer run-time storages: a list cell or a declared
    * family's value whose field is a shared value held in a sharing cell, and
    * not itself a storage, gets none, the case the e-graph's folds would
    * otherwise read; and under a strict strategy a value read untyped for want
    * of its storage throws at a fallback point (the mechanism of the FIXME at
    * `JitRules`' tail outcome), an answer lost, never a wrong one.
    */
  def specializedValue(left: Term, right: Term): Option[Term] = storedThrough(
    left
  ) match
    case Some(stored @ JitValue.Stored(storage))
        if Value.same(criterionOf(storage.representation), right) =>
      Some(stored)
    case _ =>
      val written = writtenThrough(left)
      Value.closed(written).flatMap(StorageOf.group[C]) match
        case Some(group)
            if Value.same(criterionOf(group.representation), right) =>
          Some(written)
        case _ =>
          written.layer match
            case run @ com.yang_bo.gezi.ir.Choice(_, _)
                if run.storageRun >= 2 && admitted(written) && admitted(
                  right
                ) =>
              grouped(written, run, right)
            case _ =>
              filteredAlready(left, right).orElse(convertedValue(left, right))

  /** Whether a node may stand in a storage: an instruction, a storage that is
    * one included (`ConstructorIdentity.isInstruction`).
    */
  def admitted(node: Term): Boolean = com.yang_bo.gezi.ir.ConstructorIdentity.closed(node)

  /** The node read through the JIT's sharing cells (`SharingCell`), as
    * `storedThrough` reads a storage, so that a run or a group shared through a
    * cell makes a group as the same run written in place does.
    */
  @scala.annotation.tailrec
  private def writtenThrough(node: Term): Term = node match
    case SharingCell(inner) => writtenThrough(inner)
    case _                  => node

  /** The group storage of `run ∥ criterion` when the run's first member
    * (`com.yang_bo.gezi.ir.Choice.storageRun`, a choice of storages in their canonical
    * order, told by the choice in constant time) is a storage of this encoding
    * whose criterion is this one: then every member is, a member preceding the
    * next only within one encoding and one representation. `(m1 + … + mk) ∥ T`
    * is the choice of the members by the distributivity of ∥ over + and
    * `mi ∥ T = mi`. Constant time: the group holds the chain.
    */
  private def grouped(
      chain: Term,
      run: com.yang_bo.gezi.ir.Choice[Term],
      criterion: Term
  ): Option[Term] =
    StorageOf.typed[C](run.left.representation) match
      case Some(first)
          if Value.same(criterionOf(first.representation), criterion) =>
        Some(
          Value.of(
            stored(GroupStorage(first.representation, chain.representation))
          )
        )
      case _ => None

  /** The parallel the node already is when it is written `n ∥ filter`, read
    * through the JIT's sharing cell (as `storedThrough` reads it); none
    * otherwise. Filtering it by the filter again is that node, by the
    * idempotence of ∥, so that a value filtered twice keeps one filter.
    */
  @scala.annotation.tailrec
  def filteredAlready(node: Term, filter: Term): Option[Term] = node match
    case JitValue.Parallel(_, found) if Value.same(found, filter) => Some(node)
    case SharingCell(inner) => filteredAlready(inner, filter)
    case _                  => None

  /** The storage the node holds: the node itself, or the value of the JIT's
    * sharing cell over it (`SharingCell`); none otherwise. The same value, so
    * that a typed body instantiated with a shared storage builds a storage.
    */
  @scala.annotation.tailrec
  def storedThrough(node: Term): Option[Term] = node match
    case JitValue.Stored(_) => Some(node)
    case SharingCell(inner) => storedThrough(inner)
    case _                  => None

  /** The storage of `value ∥ criterion` when that term is in the unique
    * spelling: the criterion is the one criterion of a family of this encoding
    * that takes no parameter, or the list criterion applied to an element; the
    * value is the define bound to one of the family's constructors applied to
    * exactly its fields; and each field node is the storage of the field's
    * representation (this encoding's), for a field held as written any term,
    * and for a field filtered by a criterion F of no family a node written
    * `f ∥ F`; a list's item node is `i ∥ E` or the storage whose criterion is
    * E, its tail node the storage of the list. None for any other term, which
    * keeps no storage: fewer storages, never a wrong one. A family whose
    * criterion takes a value of a finite parameter family is converted under
    * the criteria of `parameterizedRepresentations`, a constructor only where
    * its premise is shown; one of an infinite parameter family, or taking
    * criterion parameters, is not converted yet. The criterion and every field
    * node pass the one admission (`admitted`).
    */
  def convertedValue(value: Term, criterion: Term): Option[Term] =
    representationNamed(criterion).flatMap(representation =>
      spine(value, Nil, maximumArity)
        .filter((_, fields) => admitted(criterion) && fields.forall(admitted))
        .flatMap((head, fields) =>
          layerValue(representation, head, fields)
            .map(storageOf(representation, _))
        )
    )

  /** Whether the storage's view is the unique spelling: every view is but a
    * list cell's whose tail is the term as given, neither a storage of the list
    * nor filtered by its criterion (the cell cons's native makes under the
    * default construction,
    * https://github.com/Atry/private-overlay/issues/2202).
    */
  def uniquelySpelled(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Boolean = (representation, value) match
    case (
          Representation.ListOf(_),
          NativeValue.Listed(ListRepresentation.Cell(_, tail))
        ) =>
      tailOf(tail, representation).isDefined
    case _ => true

  private lazy val listCriterion: Option[Term] =
    criteriaByFamily.get(Representation.listFamily) match
      case Some(Vector(only)) => Some(only)
      case _                  => None

  /** The array lists' criterion, when the facts name it by one. */
  private lazy val arrayListCriterion: Option[Term] =
    criteriaByFamily.get(Representation.arrayListFamily) match
      case Some(Vector(only)) => Some(only)
      case _                  => None

  /** The representation the criterion names under the conversion: one of
    * `parameterizedRepresentations`, a list's, or a family's that takes no
    * parameter and that this criterion alone names, so that the storage's view
    * writes this very criterion.
    */
  private def representationNamed(
      criterion: Term
  ): Option[Representation[Term]] =
    parameterizedRepresentations
      .get(criterion)
      .orElse(plainRepresentationNamed(criterion))

  private def plainRepresentationNamed(
      criterion: Term
  ): Option[Representation[Term]] = criterion match
    case JitValue.Apply(function, element)
        if listCriterion.exists(Value.same(_, function)) =>
      Some(Representation.ListOf(element))
    case JitValue.Apply(function, element)
        if arrayListCriterion.exists(Value.same(_, function)) =>
      arrayElementRepresentations
        .find(found => Value.same(criterionOf(found), element))
        .map(Representation.ArrayListOf(_))
    case _ =>
      criterionFamily
        .get(criterion)
        .filter(identity =>
          convertedFamilies
            .contains(identity) && Value.same(head(identity), criterion)
        )
        .map(Representation.Data(_, None))

  /** The families of data the conversion makes storages of: each family of a
    * criterion the facts name, with a codec of the backend, taking no
    * parameter, not held as written, and named by one criterion (a declared
    * family by its own). With the lists, these are the representations whose
    * storages of no value parameter a reader may read as `C ȳ` (`converts`),
    * and the ones `UniqueSpellingPremise.stored` checks the premise of;
    * `parameterizedRepresentations` holds the others.
    */
  lazy val convertedFamilies: Set[FamilyIdentity] =
    facts.criterionFamily.values.toSet.filter(identity =>
      facts.nativeBackend
        .family(identity)
        .exists(found =>
          found.parameterFamily.isEmpty && found.criterionArity == 0 && !found.heldAsWritten
        ) &&
        (identity match
          case FamilyIdentity.Declared(_) => true
          case _                          =>
            criteriaByFamily.getOrElse(identity, Vector.empty).size == 1)
    )

  /** The representations of the families whose criterion takes a value of a
    * finite parameter family, by the criterion each is written with
    * (`criterionOf`), the very term a storage's view writes: a parameter family
    * is finite when it takes no parameter and every one of its constructors has
    * no field, its values being those constructors (the booleans, for
    * `binary_set P`). A family converted so is not held as written, takes no
    * criterion parameter and is named by one criterion. A criterion spelled
    * otherwise, read through a fallback point say, is no key, so one term has
    * one storage. Built once for the facts.
    */
  lazy val parameterizedRepresentations: Map[Term, Representation[Term]] =
    val pairs = facts.nativeBackend.families.toVector.flatMap(found =>
      found.parameterFamily
        .flatMap(facts.nativeBackend.family)
        .filter(parameterFamily =>
          parameterFamily.parameterFamily.isEmpty && parameterFamily
            .constructors(None)
            .forall(_.fields.isEmpty) &&
            // Each value of the parameter is spelled by its bound constructor, so the criterion is a term.
            parameterFamily
              .constructors(None)
              .forall(constructor =>
                facts.boundDefine(constructor.native).isDefined
              ) &&
            !found.heldAsWritten && found.criterionArity == 0 && criteriaByFamily
              .getOrElse(found.identity, Vector.empty)
              .size == 1
        )
        .toVector
        .flatMap(parameterFamily =>
          parameterFamily
            .constructors(None)
            .indices
            .map(index =>
              val representation = Representation.Data(
                found.identity,
                Some(
                  found.parameterOf(
                    parameterFamily.built(None, DataLayer(index, Vector.empty))
                  )
                )
              )
              criterionOf(representation) -> representation
            )
        )
    )
    val table = pairs.toMap
    assert(
      table.size == pairs.size,
      s"two representations spell one criterion: $pairs"
    )
    table

  /** The representations of `parameterizedRepresentations`. */
  private lazy val parameterizedConverted: Set[Representation[Term]] =
    parameterizedRepresentations.values.toSet

  /** Whether the conversion makes storages of lists, of every element: the
    * facts name the lists' family by one criterion.
    */
  def convertsLists: Boolean = listCriterion.isDefined

  /** Whether the conversion makes storages of the representation: a list's, an
    * array list's of an element it makes, one of `convertedFamilies` with no
    * parameter, or one of `parameterizedRepresentations`.
    */
  def converts(representation: Representation[Term]): Boolean =
    representation match
      case Representation.ListOf(_)            => convertsLists
      case Representation.ArrayListOf(element) =>
        arrayListCriterion.isDefined && arrayElementRepresentations.contains(
          element
        )
      case Representation.Data(identity, None) =>
        convertedFamilies.contains(identity)
      case parameterized @ Representation.Data(_, Some(_)) =>
        parameterizedConverted.contains(parameterized)

  /** The terms one layer of the value holds as written, whose spelling a reader
    * reads when it eliminates the storage: a data layer's fields held as
    * written, and a list cell's item and tail. A field that is a storage the
    * encoding makes holds no term of the layer; nothing deeper is read, so the
    * cost is the layer's width.
    */
  def layerTerms(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Vector[Term] = (representation, value) match
    case (
          Representation.ListOf(_),
          NativeValue.Listed(ListRepresentation.Cell(item, tail))
        ) =>
      Vector(item, tail)
    case (Representation.ListOf(_) | Representation.ArrayListOf(_), _) =>
      Vector.empty
    case (Representation.Data(identity, parameter), _) =>
      family(identity).layer(parameter, value).fields.collect {
        case NativeValue.Unread(term) => term
      }

  /** The families the conversion makes storages of, those of no parameter and
    * those of a finite value parameter at each of their criteria, each with its
    * criterion, its constructors' defines and its most fields: the ones a graph
    * may build, one layer up from storage leaves, into a storage it keeps as a
    * leaf (`ConvertedTermConstruction.storageBuilt` keeps only those).
    */
  lazy val leafCriteria
      : Vector[(FamilyIdentity, Configured[C], Vector[Configured[C]], Int)] =
    def leafCriterion(
        identity: FamilyIdentity,
        representation: Representation[Term],
        criterion: Term,
        parameter: Option[FamilyParameter[Term]]
    ) =
      // A criterion is built from the facts' pure keys and a finite parameter's constructors: it holds no neutral value
      // and no suspension, so it is a term of the IR.
      Closed
        .configured(criterion)
        .map(term =>
          val constructors = family(identity).constructors(parameter)
          (
            identity,
            term,
            constructors.indices.toVector
              .map(constructorDefine(representation, _)),
            constructors.map(_.fields.size).foldLeft(0)(_ max _)
          )
        )
    convertedFamilies.toVector
      .sortBy(_.shown)
      .flatMap(identity =>
        val representation = Representation.Data(identity, None)
        leafCriterion(
          identity,
          representation,
          criterionOf(representation),
          None
        )
      ) ++ parameterizedRepresentations.toVector
      .sortBy(_._2.toString)
      .flatMap((criterion, representation) =>
        val Representation.Data(identity, parameter) =
          representation: @unchecked
        leafCriterion(identity, representation, criterion, parameter)
      )

  /** The most fields of any constructor the conversion reads: the bound on the
    * applications it strips, so that it reads one layer.
    */
  private lazy val maximumArity: Int =
    (facts.nativeBackend.families
      .filter(_.parameterFamily.isEmpty)
      .flatMap(_.constructors(None).map(_.fields.size)) ++
      parameterizedConverted.toVector.flatMap(representation =>
        family(representation.familyIdentity)
          .constructors(representation match
            case Representation.Data(_, parameter) => parameter
            case _                                 => None)
          .map(_.fields.size)
      )).foldLeft(2)(_ max _)

  /** The defines bound to a constructor: where the spine stops, a define being
    * itself any instruction, an application among them.
    */
  private lazy val constructorDefines: Set[Term] =
    definesBound
      .collect { case (NativeName.Constructor(_, _), defines) => defines }
      .flatten
      .toSet

  /** The constructor define the value applies and the fields, at most
    * `remaining` of them stripped; none when no constructor define heads it.
    */
  @scala.annotation.tailrec
  private def spine(
      value: Term,
      arguments: List[Term],
      remaining: Int
  ): Option[(Term, Vector[Term])] =
    value match
      case _ if constructorDefines.contains(value) =>
        Some((value, arguments.toVector))
      case JitValue.Apply(function, argument) =>
        if remaining == 0 then None
        else spine(function, argument :: arguments, remaining - 1)
      case _ => None

  private def layerValue(
      representation: Representation[Term],
      head: Term,
      fields: Vector[Term]
  ): Option[NativeValue[Term]] =
    representation match
      case Representation.ListOf(element) =>
        if Value.same(head, nilTerm) && fields.isEmpty then
          Some(NativeValue.Listed(ListRepresentation.Items(0, Vector.empty)))
        else if Value.same(head, consTerm) && fields.size == 2 then
          val Vector(itemNode, tailNode) = fields: @unchecked
          for
            item <- itemOf(itemNode, element)
            tail <- tailOf(tailNode, representation)
          yield NativeValue.Listed(ListRepresentation.Cell(item, tail))
        else None
      case Representation.Data(identity, None) =>
        val dataFamily = family(identity)
        val constructors = dataFamily.constructors(None)
        constructors.indices
          .find(index =>
            constructors(index).fields.size == fields.size && !dataFamily
              .excluded(None, index) &&
              boundDefine(constructors(index).native)
                .exists(Value.same(_, head))
          )
          .flatMap(index =>
            fieldValues(
              constructors(index).fields
                .map(_.representation(Option.empty[FamilyParameter[Term]]))
                .zip(fields)
            )
              .map(values => dataFamily.built(None, DataLayer(index, values)))
          )
      case Representation.ArrayListOf(element) =>
        if Value.same(head, nilTerm) && fields.isEmpty then
          Some(arrayList(representation, Vector.empty))
        else if Value.same(head, consTerm) && fields.size == 2 then
          val Vector(itemNode, tailNode) = fields: @unchecked
          for
            item <- storedThrough(itemNode).collect {
              case JitValue.Stored(storage: BinaryNaturalStorage)
                  if storage.representation == element =>
                storage.natural.bigInteger: ArrayItem
              case JitValue.Stored(storage: IntStorage)
                  if storage.representation == element =>
                storage.bits: ArrayItem
            }
            tail <- storedThrough(tailNode).collect {
              case JitValue.Stored(storage: ArrayListStorage)
                  if storage.representation == representation =>
                storage
            }
          yield arrayConsed(representation, item, tail.listed)
        else None
      case Representation.Data(identity, parameter @ Some(_))
          if parameterizedConverted.contains(representation) =>
        // A constructor is converted under the criterion when the backend's facts make it a member at the parameter
        // (`DataFamily.excluded`): the premise of section 23 is the facts' obligation, replayed in the tests.
        val dataFamily = family(identity)
        val constructors = dataFamily.constructors(parameter)
        constructors.indices
          .find(index =>
            constructors(index).fields.size == fields.size && !dataFamily
              .excluded(parameter, index) &&
              boundDefine(constructors(index).native)
                .exists(Value.same(_, head))
          )
          .flatMap(index =>
            fieldValues(
              constructors(index).fields
                .map(_.representation(parameter))
                .zip(fields)
            )
              .map(values =>
                dataFamily.built(parameter, DataLayer(index, values))
              )
          )
      case Representation.Data(_, Some(_)) => None

  private def fieldValues(
      fields: Vector[(Representation[Term], Term)]
  ): Option[Vector[NativeValue[Term]]] =
    fields.foldLeft(Option(Vector.empty[NativeValue[Term]])) {
      case (found, (fieldRepresentation, node)) =>
        found.flatMap(values =>
          fieldValue(fieldRepresentation, node).map(values :+ _)
        )
    }

  private def fieldValue(
      fieldRepresentation: Representation[Term],
      node: Term
  ): Option[NativeValue[Term]] =
    fieldRepresentation match
      case Representation.Data(identity, _)
          if facts.nativeBackend.family(identity).exists(_.heldAsWritten) =>
        Some(NativeValue.Unread(node))
      case filtered @ Representation.Data(FilteredFamily.identity, _) =>
        // The unique spelling's field node `f ∥ F`, F the field's own
        // criterion (as a list's tail, `tailOf`); a field without it, `C f ∥ T`,
        // is no unique spelling and gets no storage.
        node match
          case JitValue.Parallel(_, filter)
              if FilteredFamily.criterionOf(filtered).contains(filter) =>
            Some(NativeValue.Unread(node))
          case _ => None
      case _ =>
        storedThrough(node) match
          case Some(stored @ JitValue.Stored(storage))
              if storage.representation == fieldRepresentation =>
            Some(StorageOf.nativeValue(storage))
          case _ => None

  /** Whether a cell over the item and tail nodes is in the unique spelling of
    * the list, one layer looked at: the decode point's test, built on `itemOf`
    * and `tailOf`, which the construction's `layerValue` and `uniquelySpelled`
    * read as well.
    */
  def cellSpelled(
      item: Term,
      tail: Term,
      representation: Representation[Term]
  ): Boolean = representation match
    case Representation.ListOf(element) =>
      itemOf(item, element).isDefined && tailOf(tail, representation).isDefined
    case _ => false

  private def itemOf(node: Term, element: Term): Option[Term] =
    (storedThrough(node), node) match
      case (Some(stored @ JitValue.Stored(storage)), _)
          if Value.same(criterionOf(storage.representation), element) =>
        Some(stored)
      case (_, JitValue.Parallel(item, filter))
          if Value.same(filter, element) =>
        Some(item)
      case _ => None

  /** A cell's tail node in the unique spelling: a storage of the list, or
    * `t ∥ list_type E`, any t, the field not read: a cell is a one-layer
    * storage, whose fields need not be storages, unlike a specialized family's.
    */
  private def tailOf(
      node: Term,
      representation: Representation[Term]
  ): Option[Term] = (storedThrough(node), node) match
    case (Some(stored @ JitValue.Stored(storage)), _)
        if storage.representation == representation =>
      Some(stored)
    case (_, JitValue.Parallel(_, filter))
        if Value.same(filter, criterionOf(representation)) =>
      Some(node)
    case _ => None

  /** Whether the node is a tail node of the unique spelling of a cell of the
    * list: `t ∥ list_type E` or a storage of the list.
    */
  def holdsAsTail(node: Term, representation: Representation[Term]): Boolean =
    tailOf(node, representation).isDefined

  /** The terms the value holds as the JIT holds them: a list's items, and the
    * fields of its data layers kept unread. A constant value
    * (`RepresentedStorage.constantValue`) holds none: no constructor of its
    * family has a field that holds an unread term, so it is answered without
    * taking the value apart, whose layers are as many as its value or its
    * width.
    */
  def heldTerms(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Vector[Term] =
    // A work list in the order of the fields, read depth first: a term found,
    // or a value still to read by its representation, so that a value is read
    // with no frame of the stack a layer, however deep its layers go. A plain
    // tail-recursive loop, where `plainFields` and `fieldNodes` trampoline:
    // this one binds no result of a step, so it needs no continuation.
    @scala.annotation.tailrec
    def read(
        pending: List[Either[Term, (Representation[Term], NativeValue[Term])]],
        found: Vector[Term]
    ): Vector[Term] = pending match
      case Nil                              => found
      case Left(term) :: rest               => read(rest, found :+ term)
      case Right((next, nextValue)) :: rest =>
        read(layerItems(next, nextValue) ::: rest, found)
    read(List(Right((representation, value))), Vector.empty)

  /** One layer of the value, for `heldTerms`: the terms it holds at once, and
    * its fields still to read, in their order.
    */
  private def layerItems(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): List[Either[Term, (Representation[Term], NativeValue[Term])]] =
    (representation, value) match
      case (_, constant) if RepresentedStorage.constantValue(constant) => Nil
      case (
            Representation.ListOf(_),
            NativeValue.Listed(ListRepresentation.Cell(item, tail))
          ) =>
        List(Left(item), Left(tail))
      case (Representation.ListOf(_), NativeValue.Listed(list)) =>
        listItems(list).toList.map(Left(_))
      case (data @ Representation.Data(_, _), _) if holdsNoTerm(data) => Nil
      case (Representation.Data(identity, parameter), _)              =>
        val dataFamily = family(identity)
        val DataLayer(constructor, fields) = dataFamily.layer(parameter, value)
        dataFamily
          .constructors(parameter)(constructor)
          .fields
          .zip(fields)
          .toList
          .map {
            case (_, NativeValue.Unread(term)) => Left(term)
            case (_, NativeValue.Stored(term)) => Left(term)
            case (field, fieldValue)           =>
              Right((field.representation(parameter), fieldValue))
          }
      case _ => Nil

  /** Whether no value of the representation holds a term, by its family's
    * declaration alone, whatever the value: its family is one of
    * `termFreeFamilies`. One lookup, so a value of such a family is answered
    * without taking it apart. It relies on the codecs' contract that a field's
    * value is a value of the field's declared representation
    * (`DataFamily.taken`).
    */
  def holdsNoTerm(representation: Representation[Term]): Boolean =
    representation match
      case Representation.Data(identity, _) =>
        termFreeFamilies.contains(identity)
      case _ => false

  /** The backend's families no value of which holds a term: the greatest set of
    * codec families, none held as written (`DataFamily.heldAsWritten`),
    * filtered (`FilteredFamily`) or declared by facts (whose values may be
    * storages the JIT holds as terms), every field of whose constructors, at
    * the parameters where every constructor appears (`shapeParameters`), is of
    * a family of the set (no list). The greatest, so that a family whose fields
    * reach itself, or one another in a cycle, is in it. Computed once for the
    * encoding, at the cost of the families' declarations, whatever parameter a
    * representation carries.
    */
  private lazy val termFreeFamilies: Set[FamilyIdentity] =
    val families = facts.nativeBackend.families
    def fieldFamilies(family: DataFamily): Vector[Option[FamilyIdentity]] =
      family.shapeParameters.flatMap(parameter =>
        family
          .constructors(parameter)
          .flatMap(_.fields.map(_.representation(parameter) match
            case Representation.Data(identity, _) => Some(identity)
            case _                                => None))
      )
    val fields =
      families.map(family => family.identity -> fieldFamilies(family)).toMap
    val start = families.collect {
      case family
          if !family.heldAsWritten && family.identity != FilteredFamily.identity && (family.identity match
            case FamilyIdentity.Declared(_) => false
            case _ => true) =>
        family.identity
    }.toSet
    @scala.annotation.tailrec
    def narrowed(candidates: Set[FamilyIdentity]): Set[FamilyIdentity] =
      val kept = candidates.filter(identity =>
        fields(identity).forall(_.exists(candidates.contains))
      )
      if kept == candidates then kept else narrowed(kept)
    narrowed(start)

  /** The position of the value's outermost constructor in its family. */
  def constructorIndex(
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Int = (representation, value) match
    case (
          Representation.ListOf(_),
          NativeValue.Listed(ListRepresentation.Cell(_, _))
        ) =>
      ListCodec.position(ListConstructor.Cons)
    case (Representation.ListOf(_), NativeValue.Listed(list)) =>
      if listItems(list).nonEmpty then ListCodec.position(ListConstructor.Cons)
      else ListCodec.position(ListConstructor.Nil)
    case (Representation.ArrayListOf(_), listed: NativeValue.ArrayListed) =>
      ListCodec.position(if listed.nil then ListConstructor.Nil
      else ListConstructor.Cons)
    case (Representation.Data(identity, parameter), _) =>
      family(identity).layer(parameter, value).constructor
    case _ =>
      throw IllegalStateException(
        s"a value of another representation than ${representation.familyIdentity.shown}: $value"
      )

/** A storage as a term of every consumer whose layers admit its view. */
object RepresentedStorage:

  /** The storage of the value under the encoding, interned: a list's whole
    * items made into its cells first, each the storage of one layer of the
    * unique spelling, so that a list term has one storage however its value was
    * given (a native's whole list, a decoding's cell).
    */
  def apply[E <: StorageEncoding & Singleton](
      encoding: E,
      representation: Representation[JitValue[E]],
      value: NativeValue[JitValue[E]]
  ): RepresentedStorage[JitValue[E]] =
    // Interned when made, as every constructor is: outside the pool a storage is equal only to itself.
    val interned =
      encoding.operations.stored(stored(encoding, representation, value).result)
    StorageOf
      .typed[E](interned.representation)
      .getOrElse(
        throw IllegalStateException(s"a storage interned as $interned")
      )

  /** The storage of the value, a declared family's value made into one layer of
    * field nodes, each a field's storage or, for a field held as written, its
    * term. Only the layers of a value built anew are walked, on the heap, so
    * that a long chain of a recursive family does not grow the stack.
    */
  private def stored[E <: StorageEncoding & Singleton](
      encoding: E,
      representation: Representation[JitValue[E]],
      value: NativeValue[JitValue[E]]
  ): TailRec[RepresentedStorage[JitValue[E]]] =
    value match
      case NativeValue.Constructed(identity, constructor, fields) =>
        val parameter = representation match
          case Representation.Data(_, found) => found
          case other                         =>
            throw IllegalStateException(
              s"a declared family's value under $other"
            )
        val fieldRepresentations = encoding.operations.fieldRepresentations(
          identity,
          parameter,
          constructor
        )
        assert(
          fieldRepresentations.size == fields.size,
          s"the value $value has not the fields of its constructor"
        )
        fieldNodes(
          encoding,
          fieldRepresentations.zip(fields).toList,
          Vector.empty
        ).map(nodes => ConstructedStorage(representation, constructor, nodes))
      case _ =>
        done(
          unconstructed(representation, value)
            .orElse(
              encoding.facts.nativeBackend
                .family(representation.familyIdentity)
                .flatMap(
                  _.storageOf(
                    representation match
                      case Representation.Data(_, parameter) => parameter
                      case _                                 => None
                    ,
                    value
                  )
                )
            )
            .getOrElse(
              throw IllegalStateException(
                s"no storage class of ${representation.familyIdentity.shown} holds $value"
              )
            )
        )

  private def fieldNodes[E <: StorageEncoding & Singleton](
      encoding: E,
      fields: List[(Representation[JitValue[E]], NativeValue[JitValue[E]])],
      found: Vector[JitValue[E]]
  ): TailRec[Vector[JitValue[E]]] = fields match
    case Nil                                   => done(found)
    case (_, NativeValue.Unread(term)) :: rest =>
      tailcall(fieldNodes(encoding, rest, found :+ term))
    // A declared value already stored is that node, so that a layer over stored fields costs the layer's width.
    case (_, NativeValue.Stored(term)) :: rest =>
      tailcall(fieldNodes(encoding, rest, found :+ term))
    case (representation, value) :: rest =>
      tailcall(stored(encoding, representation, value)).flatMap(storage =>
        tailcall(
          fieldNodes(
            encoding,
            rest,
            found :+ com.yang_bo.gezi.ir.Value.of(encoding.operations.stored(storage))(using
              encoding
            )
          )
        )
      )

  /** Whether the value is one a constant storage (`ConstantStorage`) holds: the
    * values `unconstructed` stores as `NaturalStorage`, `TruthStorage`,
    * `BinaryNaturalStorage`, `WordStorage` and the JVM bits' storages.
    */
  def constantValue(value: NativeValue[?]): Boolean = value match
    case NativeValue.Natural(_) | NativeValue.Truth(_) | BinaryNatural(_) |
        Word(_, _) | JvmBits(8 | 16 | 32 | 64, _) =>
      true
    case _ => false

  /** The storage of a value of the framework's own codecs, each codec its own
    * class, the class chosen by the value and, where two codecs hold one kind
    * of value (the 32 bits, the binary naturals), by the representation; none
    * for any other value, a provider family's, which its family stores. Throws
    * `IllegalStateException` for a value under a representation that is not its
    * class's, a defect of the caller.
    */
  private def unconstructed[Term](
      representation: Representation[Term],
      value: NativeValue[Term]
  ): Option[RepresentedStorage[Term]] =
    def of(
        storage: RepresentedStorage[Term]
    ): Option[RepresentedStorage[Term]] =
      if storage.representation != representation then
        throw IllegalStateException(
          s"the value $value under $representation, its class's representation being ${storage.representation}"
        )
      Some(storage)
    value match
      case NativeValue.Natural(natural) => of(NaturalStorage(natural))
      case NativeValue.Truth(truth)     => of(TruthStorage(truth))
      case BinaryNatural(natural)       =>
        of(if representation == BinaryNaturalNatives.positive then
          PositiveBinaryNaturalStorage(natural)
        else CanonicalBinaryNaturalStorage(natural))
      case Word(width, bits) => of(WordStorage(width, bits))
      case JvmBits(8, bits)  => of(ByteStorage(bits.toByte))
      case JvmBits(16, bits) => of(ShortStorage(bits.toShort))
      case JvmBits(32, bits) =>
        of(if representation == JvmIntNatives.jvmInt then
          JvmIntStorage(bits.toInt)
        else Bits32Storage(bits.toInt))
      case JvmBits(64, bits) => of(LongStorage(bits))
      case NativeValue.Listed(ListRepresentation.Cell(item, tail)) =>
        Some(CellStorage(representation, item, tail))
      case NativeValue.Listed(ListRepresentation.Items(0, _)) =>
        Some(NilStorage(representation))
      case listed: NativeValue.ArrayListed =>
        require(
          listed.elements.representation == representation,
          s"an array list's storage of ${listed.elements.representation} under $representation"
        )
        Some(ArrayListStorage(listed.elements.representation, listed))
      case _ => None

  /** The canonical order of two storages of one representation, the order of a
    * group's members, read off their own data: a natural or a binary natural by
    * its value, a word by its bits, a JVM bit tuple by its bits read unsigned,
    * a boolean false first, each the same in every process; a general storage
    * (a declared family's value, a list's cell or nil) whose view is an
    * instruction by its constructor's position, then by the terms it holds, by
    * their content (`com.yang_bo.gezi.ir.ContentComparison`; a URI node's content being its
    * URI, a `file:` URI makes it depend on the checkout, which changes only
    * which choices form groups), never by a hash code, an identity. None for
    * two storages it does not order: of two kinds, a provider's values, a
    * general storage whose view holds a value of a reader; they form no group.
    */
  def canonicalOrder(
      first: RepresentedStorage[?],
      second: RepresentedStorage[?]
  ): Option[Int] = (first, second) match
    case (a: NaturalStorage, b: NaturalStorage) =>
      Some(a.natural.compare(b.natural))
    case (a: BinaryNaturalStorage, b: BinaryNaturalStorage) =>
      Some(a.natural.compare(b.natural))
    case (a: WordStorage, b: WordStorage) => Some(a.bits.compare(b.bits))
    case (a: ByteStorage, b: ByteStorage) =>
      Some(java.lang.Byte.compareUnsigned(a.bits, b.bits))
    case (a: ShortStorage, b: ShortStorage) =>
      Some(java.lang.Short.compareUnsigned(a.bits, b.bits))
    case (a: IntStorage, b: IntStorage) =>
      Some(Integer.compareUnsigned(a.bits, b.bits))
    case (a: LongStorage, b: LongStorage) =>
      Some(java.lang.Long.compareUnsigned(a.bits, b.bits))
    case (a: TruthStorage, b: TruthStorage) => Some(a.truth.compare(b.truth))
    case (a, b) if general(a) && general(b) && a.closed && b.closed =>
      if a eq b then Some(0)
      else if a.constructorPositionWithin != b.constructorPositionWithin then
        Some(
          Integer
            .compare(a.constructorPositionWithin, b.constructorPositionWithin)
        )
      else
        Some(
          com.yang_bo.gezi.ir.ContentComparison
            .compare(a.termChildren.toVector, b.termChildren.toVector)
        ).filter(_ != 0)
    case _ => None

  private def general(storage: RepresentedStorage[?]): Boolean = storage match
    case _: ConstructedStorage[?] | _: CellStorage[?] | _: NilStorage[?] => true
    case _ => false

/** A storage of a constant held as native data, whole: the e-graph keeps it as
  * a leaf (`leafInEGraph`), and it is an instruction, its view holding the
  * facts' constructors, storages of its own kind and its criterion, which is
  * the facts' instructions applied to the plain spelling of a value parameter,
  * all of them instructions.
  */
trait ConstantStorage extends RepresentedStorage[Nothing]:
  /** Nothing: a constant is native data alone. */
  protected def held: Vector[Any] = Vector.empty
  override def leafInEGraph: Boolean = true
  override def constantSize: Boolean = true

/** A natural of the family `big_integer`, held as its `BigInt`. */
final class NaturalStorage(val natural: BigInt)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] = Representation.BigInteger

  lazy val value: NativeValue[Nothing] = NativeValue.Natural(natural)

  protected lazy val constructorIndex: Int =
    BigIntegerFamily.taken(None, value).constructor
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: NaturalStorage => other.natural == natural
    case _                     => false

/** A boolean of the family `boolean`, held as its `Boolean`. */
final class TruthStorage(val truth: Boolean)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] = Representation.Truth

  lazy val value: NativeValue[Nothing] = NativeValue.Truth(truth)

  protected lazy val constructorIndex: Int =
    BooleanFamily.taken(None, value).constructor
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: TruthStorage => other.truth == truth
    case _                   => false

/** A binary natural of the family `binary_natural`, held as its `BigInt`: of
  * the canonical naturals or of the positive ones, each its own class
  * (`CanonicalBinaryNaturalStorage`, `PositiveBinaryNaturalStorage`), whose
  * representation is the parameter its class names.
  */
sealed abstract class BinaryNaturalStorage(val natural: BigInt)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  lazy val value: NativeValue[Nothing] = BinaryNatural(natural)

  protected lazy val constructorIndex: Int =
    BinaryNaturalFamily.layer(dataParameter, value).constructor
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: BinaryNaturalStorage => other.natural == natural
    case _                           => false

/** A binary natural of the canonical naturals
  * (`BinaryNaturalNatives.canonical`).
  */
final class CanonicalBinaryNaturalStorage(natural: BigInt)
    extends BinaryNaturalStorage(natural):
  def representation: Representation[Nothing] = BinaryNaturalNatives.canonical

/** A binary natural of the positive naturals (`BinaryNaturalNatives.positive`).
  */
final class PositiveBinaryNaturalStorage(natural: BigInt)
    extends BinaryNaturalStorage(natural):
  def representation: Representation[Nothing] = BinaryNaturalNatives.positive

/** A word of the family `word`, held as its width and bits; its width, the
  * codec's parameter, is its data.
  */
final class WordStorage(val width: BigInt, val bits: BigInt)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] =
    Representation.Data(WordFamily.identity, Some(WordWidth(width)))

  lazy val value: NativeValue[Nothing] = Word(width, bits)

  protected lazy val constructorIndex: Int =
    WordFamily.taken(dataParameter, value).constructor
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: WordStorage => other.width == width && other.bits == bits
    case _                  => false

/** The representations of the JVM bit tuples' families, one constant each. */
private object JvmBitsRepresentations:
  def of(width: Int): Representation[Nothing] = byWidth(width)

  private val byWidth: Map[Int, Representation[Nothing]] =
    JvmBitsFamily.all
      .map(family => family.width -> Representation.Data(family.identity, None))
      .toMap

/** A tuple of 8 bits (the family `jvm_bits_8`), held as the JVM's `byte`, read
  * unsigned when it is made a value.
  */
final class ByteStorage(val bits: Byte)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] = JvmBitsRepresentations.of(8)

  lazy val value: NativeValue[Nothing] =
    JvmBits(8, java.lang.Byte.toUnsignedLong(bits))

  // One constructor in its codec (`JvmBitsFamily`).
  protected lazy val constructorIndex: Int = 0
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: ByteStorage => other.bits == bits
    case _                  => false

/** A tuple of 16 bits (the family `jvm_bits_16`), held as the JVM's `short`,
  * read unsigned when it is made a value.
  */
final class ShortStorage(val bits: Short)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] = JvmBitsRepresentations.of(16)

  lazy val value: NativeValue[Nothing] =
    JvmBits(16, java.lang.Short.toUnsignedLong(bits))

  // One constructor in its codec (`JvmBitsFamily`).
  protected lazy val constructorIndex: Int = 0
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: ShortStorage => other.bits == bits
    case _                   => false

/** A value of 32 bits held as the JVM's `int`, read unsigned when it is made a
  * value: a tuple of 32 bits (the family `jvm_bits_32`, `Bits32Storage`), whose
  * interface is the Scott tuple of 32 booleans, or a 32-bit word (the family
  * `jvm_int`, `JvmIntStorage`), whose interface is one layer `word_cell` of its
  * least significant bit and the 31 bits above: each codec its own class.
  */
sealed abstract class IntStorage(val bits: Int)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  lazy val value: NativeValue[Nothing] =
    JvmBits(32, java.lang.Integer.toUnsignedLong(bits))

  // One constructor in each of its codecs (`JvmBitsFamily`, `JvmIntFamily`).
  protected lazy val constructorIndex: Int = 0
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: IntStorage => other.bits == bits
    case _                 => false

/** A tuple of 32 bits (the family `jvm_bits_32`). */
final class Bits32Storage(bits: Int) extends IntStorage(bits):
  def representation: Representation[Nothing] = JvmBitsRepresentations.of(32)

/** A 32-bit word held as a JVM `int` (the family `jvm_int`). */
final class JvmIntStorage(bits: Int) extends IntStorage(bits):
  def representation: Representation[Nothing] = JvmIntNatives.jvmInt

/** A tuple of 64 bits (the family `jvm_bits_64`), held as the JVM's `long`. */
final class LongStorage(val bits: Long)
    extends RepresentedStorage[Nothing]
    with ConstantStorage:
  def representation: Representation[Nothing] = JvmBitsRepresentations.of(64)

  lazy val value: NativeValue[Nothing] = JvmBits(64, bits)

  // One constructor in its codec (`JvmBitsFamily`).
  protected lazy val constructorIndex: Int = 0
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: LongStorage => other.bits == bits
    case _                  => false

/** The empty list of a list's family. */
final class NilStorage[+Term](val representation: Representation[Term])
    extends RepresentedStorage[Term]:
  protected def held: Vector[Any] = Vector.empty
  lazy val value: NativeValue[Nothing] =
    NativeValue.Listed(ListRepresentation.Items(0, Vector.empty))

  protected lazy val constructorIndex: Int =
    ListCodec.position(ListConstructor.Nil)
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case _: NilStorage[?] => true
    case _                => false

/** One cell of a list's family, holding its item's and its tail's nodes as
  * written, the one layer of a generic storage (`ListRepresentation.Cell`).
  */
final class CellStorage[+Term](
    val representation: Representation[Term],
    val item: Term,
    val tail: Term
) extends RepresentedStorage[Term]:
  protected def held: Vector[Any] = Vector(item, tail)
  lazy val value: NativeValue[Term] =
    NativeValue.Listed(ListRepresentation.Cell(item, tail))

  protected lazy val constructorIndex: Int =
    ListCodec.position(ListConstructor.Cons)

  /** The nodes compared as objects: they are interned, so equal nodes are one
    * object, and the comparison never walks the tail's cells (a long list whose
    * cells' hash codes collide would otherwise be compared to its end on the
    * stack).
    */
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: CellStorage[?] =>
      (other.item.asInstanceOf[AnyRef] eq item
        .asInstanceOf[AnyRef]) && (other.tail.asInstanceOf[AnyRef] eq tail
        .asInstanceOf[AnyRef])
    case _ => false

/** The elements of an array list, held once and shared by every suffix's value
  * and storage, compared by reference: a decode point, two equal vectors being
  * two holders. Every suffix's content hash code is given when the elements are
  * made (a cons's from its suffix's in one step, a relabelling's shared with
  * the elements it relabels), or else computed once, from the last element to
  * the first, when first asked: the immutable `lazy val` of a storage, so that
  * no suffix's hash recurses down its tail.
  */
final class ArrayElements(
    val values: Vector[ArrayItem],
    val representation: Representation[Nothing],
    known: Option[Vector[Int]]
):
  require(
    known.forall(_.size == values.size + 1),
    "known hash codes are one for every suffix"
  )

  /** The hash code of every suffix's elements, the empty suffix's last: given
    * when the elements were consed onto a suffix, whose own were then already
    * computed, else computed in one pass when first asked.
    */
  lazy val contentHashes: Vector[Int] =
    known.getOrElse(
      values.scanRight(ArrayElements.emptyHash(representation))((item, rest) =>
        31 * rest + item.hashCode
      )
    )

  /** The hash code of the elements from `start` on. */
  def contentHash(start: Int): Int = contentHashes(start)

  /** Whether the content's hash codes were given when the elements were made
    * (by a cons from its suffix's, or by a relabelling), not computed by a pass
    * over the elements.
    */
  def hashesGiven: Boolean = known.isDefined

object ArrayElements:

  /** The hash code of the empty suffix's elements: by the element's family, so
    * that lists of two kinds hash apart and the canonical and the positive
    * naturals' lists, of one family, share their content's hash codes.
    */
  def emptyHash(representation: Representation[Any]): Int = representation match
    case Representation.ArrayListOf(element) =>
      0x41727261 ^ element.familyIdentity.##
    case other =>
      throw IllegalStateException(s"an array list's elements under $other")

  /** Whether the item is of the kind an array list of the representation holds:
    * a `BigInteger` for the binary naturals, an `Int` for the 32-bit words.
    */
  def holds(representation: Representation[Any], item: ArrayItem): Boolean =
    (representation, item) match
      case (Representation.ArrayListOf(element), _: java.math.BigInteger) =>
        element.familyIdentity == BinaryNaturalFamily.identity
      case (Representation.ArrayListOf(element), _: Int) =>
        element.familyIdentity == JvmIntFamily.identity
      case _ => false

/** An array list's element: a binary natural as a `BigInteger`, or a 32-bit
  * word as a JVM `int`, its kind the list's element representation's.
  */
type ArrayItem = java.math.BigInteger | Int

/** An array list's suffix (`Representation.ArrayListOf`): the elements from
  * `start` on of a vector its suffixes share, a specialized storage holding no
  * term. Its view is `nil ∥ T`, or `cons s t ∥ T` with s the storage of its
  * first element and t the storage of the suffix after it, made when a reader
  * asks; its tail is the same elements at `start + 1`, one step.
  */
final class ArrayListStorage(
    val representation: Representation[Nothing],
    val listed: NativeValue.ArrayListed
) extends RepresentedStorage[Nothing]:
  protected def held: Vector[Any] = Vector.empty
  def value: NativeValue[Nothing] = listed

  protected lazy val constructorIndex: Int = ListCodec.position(
    if listed.nil then ListConstructor.Nil else ListConstructor.Cons
  )
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: ArrayListStorage => other.listed == listed
    case _                       => false

/** A value of a declared family, one layer: its constructor's index and its
  * fields' nodes, a field's storage or, for a field held as written
  * (`UnreadFamily`, `FilteredFamily`), the term `f` or `f ∥ F`. As a native
  * value it is its own term (`NativeValue.Stored`, `StorageOf.nativeValue`),
  * its fields read by its configuration one layer at a time, so that no
  * consumer reads past one layer. Its hash code, its view, its children and its
  * constructor are read off the nodes, each at the cost of the layer's width.
  */
final class ConstructedStorage[+Term](
    val representation: Representation[Term],
    val constructor: Int,
    val fields: Vector[Term]
) extends RepresentedStorage[Term]:

  /** None: a declared family's value is the storage itself, a term
    * (`NativeValue.Stored`), which only its configuration's reading gives
    * (`StorageOf.nativeValue`); its fields are terms of that configuration.
    * Throws `IllegalStateException`, a defect of a caller that reads a declared
    * storage's data as a codec's.
    */
  def value: NativeValue[Term] =
    throw IllegalStateException(
      s"a declared family's storage is its own term, read through StorageOf.nativeValue: $this"
    )

  protected def held: Vector[Any] = fields

  /** The hash code of the representation, the constructor and the fields'
    * nodes, each of which holds its own: one layer's width.
    */
  override lazy val contentHash: Int =
    31 * (31 * representation.## + constructor) + fields.##

  override protected lazy val constructorIndex: Int = constructor

  /** The field nodes compared as objects: they are interned, so equal nodes are
    * one object, and the comparison reads one layer, however long a chain of
    * layers is (compared by equality, a chain of 100000 layers overflowed the
    * stack when interned, each comparison going down to the next level).
    */
  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: ConstructedStorage[?] =>
      other.constructor == constructor && other.fields.size == fields.size &&
      other.fields
        .lazyZip(fields)
        .forall((left, right) =>
          left.asInstanceOf[AnyRef] eq right.asInstanceOf[AnyRef]
        )
    case _ => false

  override def toString: String =
    s"ConstructedStorage(${representation.familyIdentity.shown}, $constructor, ${fields.size} fields)"

/** A group of values of one representation, the term `(m1 + (… + mk)) ∥ T`: its
  * members are storages of one encoding and one representation, at least two,
  * in their canonical order (`RepresentedStorage.canonicalOrder`), so without
  * repetition, and T is their criterion. By the commutativity of ∥, its
  * distributivity over + (Lean
  * `ContextualPreorder.parallelChoiceDistributiveContextualEquivalence`,
  * `M ∥ (N + P) ≃_O (M ∥ N) + (M ∥ P)`) and `mi ∥ T = mi` it is the choice of
  * its members, which is how the JIT and the readers read it, one member at a
  * time. It is no value: it has no outermost constructor, and the e-graph reads
  * it through its view.
  *
  * It holds the interned choice `chain`, the storage run its members are
  * (`com.yang_bo.gezi.ir.Choice.storageRun`), which is its view's left side, so that making
  * it, its hash code (from the representation's and the chain's) and its
  * equality (one encoding, one representation and one chain, which interning
  * makes one object for one content) are constant time; its members are read
  * off the chain, O(k), when first asked. A later implementation holding its
  * members as raw data must be equal to this one when they have the same
  * members, which this class's equality, comparing chains, does not yet
  * provide.
  *
  * TODO: whether the e-graph's HM infers `(m1 + … + mk) ∥ T` for a choice of
  * typed values, the user's condition on this encoding, rests on the lemma
  * `unions_choice_typed` of step 1b; until it lands with a recorded extraction
  * that writes `(a + b) ∥ T`, that is a hypothesis.
  * https://github.com/Atry/private-overlay/issues/2188
  */
final class GroupStorage[+Term](
    val representation: Representation[Term],
    val chain: com.yang_bo.gezi.ir.Interned.Interned[com.yang_bo.gezi.ir.ValueLayer]
) extends com.yang_bo.gezi.ir.NativeStorage:

  /** The chain's first member, whose criterion every member shares: a member
    * precedes the next only when both are of this encoding and this
    * representation (`RepresentedStorage.canonicalOrder`).
    */
  private def firstMember: RepresentedStorage[?] = chain match
    case run: com.yang_bo.gezi.ir.Choice[?] =>
      (run.left: Any) match
        case first: RepresentedStorage[?] => first
        case other                        =>
          throw IllegalStateException(
            s"a group whose first member is no storage: $other"
          )
    case other =>
      throw IllegalStateException(s"a group whose chain is no choice: $other")

  chain match
    case run: com.yang_bo.gezi.ir.Choice[?] =>
      assert(
        run.storageRun >= 2,
        s"a group whose chain begins no storage run: $chain"
      )
      assert(
        firstMember.representation == representation,
        s"a group of another kind's members: $chain"
      )
    case other =>
      throw IllegalArgumentException(
        s"a group whose chain is no choice: $other"
      )

  /** The members, in their canonical order, read off the chain. */
  lazy val members: Vector[RepresentedStorage[Term]] =
    (chain: Any) match
      case run: com.yang_bo.gezi.ir.Choice[?] =>
        com.yang_bo.gezi.ir.StorageRun.members(run).map {
          // A member of a group of `Term`s holds `Term`s: the group was built of them (`StorageEncoding.grouped`).
          case member: RepresentedStorage[?] =>
            member.asInstanceOf[RepresentedStorage[Term]]
          case other =>
            throw IllegalStateException(
              s"a group's member is no storage of a representation: $other"
            )
        }
      case other =>
        throw IllegalStateException(s"a group whose chain is no choice: $other")

  protected lazy val termChildren: IArray[AnyRef] = IArray(
    chain.asInstanceOf[AnyRef]
  )

  /** Whether the chain holds no neutral value. */
  lazy val closed: Boolean = ConstructorIdentity.closed(chain)

  /** Whether the chain holds no value extension. */
  lazy val suspensionFree: Boolean = ConstructorIdentity.suspensionFree(chain)

  /** Whether every member may be handed over whole: a group at the top of a
    * program's value is the choice of its members
    * (`NativeStorage.handedOverWhole`); under a constructor its holder answers
    * false.
    */
  lazy val handedOverWhole: Boolean = members.forall(_.handedOverWhole)

  /** A group has no outermost constructor. */
  protected def constructorIndex: Int = throw IllegalStateException(
    s"a group of storages has no outermost constructor: $this"
  )

  val leafInEGraph: Boolean = false

  /** False: a group's size grows with its members'. */
  val constantSize: Boolean = false

  /** False: a group is a kind of its own, and precedes nothing. */
  def precedes(other: com.yang_bo.gezi.ir.NativeStorage): Boolean = false

  /** The hash code of the representation and of the chain of members, which
    * holds its own.
    */
  val contentHash: Int = 31 * representation.## + chain.##

  def sameContent(other: com.yang_bo.gezi.ir.NativeStorage): Boolean = other match
    case that: GroupStorage[?] =>
      that.contentHash == contentHash && that.representation == representation && (that.chain eq chain)
    case _ => false

  override def toString: String =
    s"GroupStorage(${representation.familyIdentity.shown})"

/** A value of a family a provider adds, held as its `NativeValue`: each
  * provider's family gives its own storage class, a subclass of this one
  * (`DataFamily.storageOf`), so that the class is the codec, and the subclass
  * gives the representation (with the parameter it holds, if its codec has one)
  * and the outermost constructor's position.
  */
abstract class ProviderStorage[+Term](val value: NativeValue[Term])
    extends RepresentedStorage[Term]:

  /** The terms the provider's value holds, its class's own answer
    * (`NativeValue.heldTerms`), with no configuration.
    */
  protected def held: Vector[Any] = value.heldTerms

  protected def sameData(that: RepresentedStorage[?]): Boolean = that match
    case other: ProviderStorage[?] => other.value == value
    case _                         => false

/** The one typed reading of a storage of this module (a registered conversion
  * of https://github.com/Atry/private-overlay/issues/2261, section 8): a
  * storage reached from a closed value of the configuration `C` holds terms of
  * `C`, since a storage is built only by `C`'s specializer, out of `C`'s terms,
  * and interning gives back the object `C` builds. Readers take the storage's
  * own data (its representation's parameters, its native data, the terms it
  * holds) from the typed object, and what depends on the configuration through
  * `C`.
  */
object StorageOf:

  /** The storage the closed value is, typed by its configuration, when it is
    * one.
    */
  def read[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](value: Closed[C])(using
      C
  ): Option[RepresentedStorage[JitValue[C]]] =
    typed[C](Closed.value(value).representation)

  /** The declared family's storage the storage is, typed by its configuration,
    * when it is one.
    */
  def constructed[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: RepresentedStorage[JitValue[C]]
  ): Option[ConstructedStorage[JitValue[C]]] = storage match
    case found: ConstructedStorage[?] =>
      Some(found.asInstanceOf[ConstructedStorage[JitValue[C]]])
    case _ => None

  /** The native value the storage stands for in its configuration: a declared
    * family's storage is its own term (`NativeValue.Stored`), any other
    * storage's its native data (`RepresentedStorage.value`).
    */
  def nativeValue[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: RepresentedStorage[JitValue[C]]
  ): NativeValue[JitValue[C]] =
    storage match
      case _: ConstructedStorage[?] => NativeValue.Stored(value(storage))
      case other                    => other.value

  /** The group of storages, typed by the configuration of the specializer that
    * reads it.
    */
  private[jit] def groupOfStorage[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      group: GroupStorage[?]
  ): GroupStorage[JitValue[C]] =
    group.asInstanceOf[GroupStorage[JitValue[C]]]

  /** The group of storages the closed value is, typed by its configuration,
    * when it is one.
    */
  def group[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](value: Closed[C])(using
      C
  ): Option[GroupStorage[JitValue[C]]] =
    (Closed.value(value).representation: AnyRef) match
      case found: GroupStorage[?] =>
        Some(found.asInstanceOf[GroupStorage[JitValue[C]]])
      case _ => None

  /** The storage typed by the configuration of the specializer that reads it
    * (`StorageEncoding`, which receives only its own terms' storages).
    */
  private[jit] def typed[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: AnyRef
  ): Option[RepresentedStorage[JitValue[C]]] =
    storage match
      case found: RepresentedStorage[?] =>
        Some(found.asInstanceOf[RepresentedStorage[JitValue[C]]])
      case _ => None

  /** The representation of a storage or a group of this module, typed by the
    * specializer's configuration.
    */
  private[jit] def representationOf[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: AnyRef
  ): Option[Representation[JitValue[C]]] = storage match
    case found: RepresentedStorage[?] =>
      Some(found.asInstanceOf[RepresentedStorage[JitValue[C]]].representation)
    case found: GroupStorage[?] =>
      Some(found.asInstanceOf[GroupStorage[JitValue[C]]].representation)
    case _ => None

  /** A storage that is a JIT head of the configuration `C`, typed by it: a head
    * is read off a value of `C`.
    */
  private[jit] def ofHead[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: RepresentedStorage[?]
  ): RepresentedStorage[JitValue[C]] =
    storage.asInstanceOf[RepresentedStorage[JitValue[C]]]

  /** The value of a storage typed by its configuration: the same object, a
    * storage being an interned term.
    */
  def value[C <: com.yang_bo.gezi.ir.NativeSpecializer & Singleton](
      storage: RepresentedStorage[JitValue[C]]
  ): JitValue[C] =
    storage.asInstanceOf[JitValue[C]]
