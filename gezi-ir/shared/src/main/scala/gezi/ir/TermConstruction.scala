package gezi.ir

/** How a configuration builds the terms it interns: the instruction of one
  * layer over instructions already built. A configuration that converts terms
  * into native storages converts here, before the term is interned, so that a
  * term with a storage is interned only as the storage (the plan's B1,
  * conversion before interning); the pool keeps every term as it is given
  * (`Canonicalization`). The e-graph's write-back and the extraction's spelling
  * build through the construction of the graph's store (`Store.construction`),
  * so that a round's outputs have no plain twin of a storage.
  *
  * A construction is built bottom up: a layer's children are built first, so
  * that converting a layer reads one layer and the classes of its children.
  */
trait TermConstruction[C <: NativeSpecializer & Singleton]:

  /** The native specializer of the configuration, which builds every term the
    * graph writes back.
    */
  def specializer: C

  /** The capability with which the graph reads a storage's view, granted where
    * the configuration is set up.
    */
  def storageAccess: StorageAccess

  /** The term of one layer over instructions the graph holds, built by the
    * native specializer (`NativeSpecializer.layerBuilt`).
    */
  final def instruction[Child](layer: LayerWith[Child, Configured[C]])(
      term: Child => Configured[C]
  ): Configured[C] =
    specializer.built(layer)(term)

  /** The criteria under which a graph may build, one layer up from storage
    * leaves, the storage of `C s1 … sk ∥ T` (`storageBuilt`); none for a
    * construction that converts nothing.
    */
  def storageCriteria: Vector[Configured[C]] = Vector.empty

  /** The defines of the constructors whose applications to storages a graph may
    * build into a storage under one of `storageCriteria`.
    */
  def storageConstructors: Vector[Configured[C]] = Vector.empty

  /** The most fields of a constructor of `storageConstructors`: how far up from
    * a storage leaf a graph looks for the parallel it may build.
    */
  def storageArity: Int = 0

  /** The storage the graph keeps as a leaf (`NativeStorage.leafInEGraph`) of
    * `constructor fields… ∥ criterion`, when that term is the unique spelling
    * of one under this construction, the fields storages; none otherwise. The
    * term is the storage by the storage's definition.
    */
  def storageBuilt(
      constructor: Configured[C],
      fields: Vector[NativeStorage],
      criterion: Configured[C]
  ): Option[Configured[C]] =
    None

  /** The defines bound to natives a graph may fold an application of: a native
    * of a function whose every parameter and whose result are each one
    * representation, the result's storage one the graph keeps as a leaf; none
    * for a construction that converts nothing.
    */
  def foldingDefines: Vector[Configured[C]] = Vector.empty

  /** The most parameters of a native of `foldingDefines`. */
  def foldingArity: Int = 0

  /** The native's result as a storage, with the native's name, when the define
    * is bound to a native of `foldingDefines` and each argument is a storage of
    * exactly the representation of its parameter's place: the native called on
    * single values (`native = define` holds on them), its result a value of its
    * result's representation, `r ∥ B = r`. None otherwise.
    */
  def folded(
      define: Configured[C],
      arguments: Vector[NativeStorage]
  ): Option[(Configured[C], String)] = None

object TermConstruction:

  /** The construction of a configuration whose specializer converts nothing a
    * graph may build into a storage one layer up from its leaves (no
    * `storageCriteria`, no `foldingDefines`): `TermConstruction(NoFacts)` for a
    * configuration with no facts, whose terms are as written, canonical only
    * because `NoFacts` declares no storage. A store under facts that declare
    * storages takes their construction, never this one.
    */
  def apply[C <: NativeSpecializer & Singleton](
      configurationSpecializer: C
  ): TermConstruction[C] = new TermConstruction[C]:
    def specializer: C = configurationSpecializer

    // A graph whose construction builds no storage reads none through this capability.
    val storageAccess: StorageAccess = StorageAccess.granted()
