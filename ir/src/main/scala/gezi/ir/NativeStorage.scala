package gezi.ir

/** A native storage: an implementation of one interned term of the IR, the
  * parallel `v ∥ T` of a value v whose outermost layer is a constructor of
  * the data family of the criterion T, held in a native form. The IR is the
  * interface and a storage one of its implementations: the term a storage
  * stands for is its view, which the native specializer of the entry in scope
  * reads (`NativeSpecializer.viewOf`), since the view depends on the entry's
  * families and the storage holds no configuration; every other code sees the
  * storage as a leaf of its term's layer ([[IrLayer]]); the e-graph keeps a
  * storage that says `leafInEGraph` as a leaf and never reads its view
  * (`Store.expanded`, `heldAsLeaf`). Nothing without `∥ T` has a storage.
  *
  * A storage holds only what tells terms apart: its class (which is its
  * codec), the parameters that vary within its codec, a declared family's
  * criterion, and its native data. Within one entry, those determine the term
  * it stands for.
  *
  * A storage is an interned term itself, the pool keeping it as it is
  * given, and like every interned object it hashes by its identity and is
  * equal only to itself outside the pool. The pool reads its own data
  * instead (`contentHash`, `sameContent`): two storages are one object
  * exactly when their views are one term, and a storage is never one with a
  * constructor object, so the hash code comes from its representation and
  * native data, not from its view.
  *
  * No storage class and no conversion into a storage is in this module: a
  * backend defines them, and its [[NativeSpecializer]] converts before it interns
  * and is the only entry of a storage to the pool.
  */
trait NativeStorage:

  /** The hash code of the storage's representation and native data, which
    * the pool reads; never a view built.
    */
  def contentHash: Int

  /** Whether the other storage holds the same representation and data, its
    * view the same term, which the pool reads.
    */
  def sameContent(other: NativeStorage): Boolean

  // Inside the pool, the storage interned (bound by `Canonicalization.term`) answers by its data; outside it, by identity.
  final override def hashCode: Int = if Canonicalization.interning(this) then contentHash else System.identityHashCode(this)

  final override def equals(other: Any): Boolean = other match
    case that: NativeStorage =>
      (this eq that) || ((Canonicalization.interning(this) || Canonicalization.interning(that)) && sameContent(that))
    case _ => false

  // TODO: deleted: `viewValue` and `view`, the view read from the storage alone, and `isInstruction`. Wrong because the
  // view depends on the entry's families, which the storage does not hold, and `isInstruction` answered two questions
  // at once; issue https://github.com/Atry/private-overlay/issues/2261, design v38, sections 1 and 2. Read it back with
  // `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/NativeStorage.scala`.

  /** Whether the term holds no neutral value (a free variable a reader put in place of a binder): known when the
    * storage is made, from what it holds, which is made first, so that the question costs one field read.
    */
  def closed: Boolean

  /** Whether the term holds no suspension (a reader's thunk without holes, a delayed instance): known when the storage
    * is made, as `closed` is.
    */
  def suspensionFree: Boolean

  /** Whether the storage may be handed over whole as a Scott ADT value, with nothing below it to compute: true exactly
    * when no field, at any depth through the storages it holds, is an object other than a storage (a term held as
    * written, a parallel node) and no field holds a group of several members under a constructor. Read off the
    * storage's own data, with no configuration, so that one storage object has one answer under every entry.
    */
  def handedOverWhole: Boolean

  /** The interned terms this storage holds as objects, read with no configuration: a declared family's criterion, and
    * the fields of a storage that holds its constructor's fields as terms. A traversal that must not read the view
    * reads these.
    */
  protected def termChildren: IArray[AnyRef]

  /** `termChildren`, for code that holds the capability. */
  final def heldTerms(using StorageAccess): IArray[AnyRef] = termChildren

  /** The position of the value's outermost constructor in the family of the
    * criterion.
    */
  protected def constructorIndex: Int

  /** `constructorIndex`, for code that holds the capability. */
  final def constructorPosition(using StorageAccess): Int = constructorIndex

  /** Whether the e-graph keeps the storage as a leaf (`NoinlineLeaf`) and
    * never reads its view: true for a storage of a constant held as native
    * data (a natural, a boolean, a fixed-width word), whose view is the whole
    * value written out and which no lemma of a typed round rewrites; false
    * for a storage whose
    * fields may hold terms still to be rewritten (a declared family's value,
    * a list's cell), which enters through its one-layer view, its fields
    * becoming classes.
    */
  def leafInEGraph: Boolean

  /** Whether a round that stops at storages of constant size
    * (`gezi.egraph.EGraph.constantStorageStop`) stops at this one, taking its
    * class as usually optimal and matching no lemma below it: a boolean or a
    * word of a fixed width, whose data are of one size, and also a natural
    * or a word of any width, whose data grow with the logarithm of its value.
    * For the latter the stop is an approximation: a large value whose class
    * also holds a smaller spelling (a power written as an application) is
    * not rewritten further, which costs size, never an answer. False for a
    * storage whose size grows with its value's count of members, an array
    * list's or a group's, which a round goes on rewriting.
    */
  def constantSize: Boolean

  // TODO: deleted: `criterionTerm` and `criterion`, the criterion read from the storage alone. Wrong because a codec's
  // criterion is the entry's configuration (`NativeSpecializer.criterionOf`); issue
  // https://github.com/Atry/private-overlay/issues/2261, design v38, section 2. Read it back with
  // `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/NativeStorage.scala`.

  /** The held terms and the constructor's position, for the content order of storages within ir
    * (`ContentComparison`), which reads no view.
    */
  private[ir] final def comparedTerms: IArray[AnyRef] = termChildren
  private[ir] final def comparedConstructor: Int = constructorIndex

  /** Whether this storage comes strictly before the other in the canonical
    * order of the storages a group may hold together: both of one encoding,
    * one representation and one kind, a group being a kind of its own that
    * precedes and follows nothing. A strict order read off the storages' own
    * data and the content of the terms they hold (`ContentComparison`),
    * never a hash code, which is an identity; false for two storages it does
    * not order, which then form no group: storages of two kinds. The order is
    * the same wherever the same terms are made; a URI node's content is its
    * URI, so a general storage whose view holds a `file:` URI may be ordered
    * differently in two checkouts, which changes only which choices form
    * groups.
    */
  def precedes(other: NativeStorage): Boolean

object NativeStorage:

  /** Whether the term is held by a storage: one class test, which reads no
    * layer.
    */
  def stored(term: AnyRef): Boolean = term match
    case _: NativeStorage => true
    case _                => false
