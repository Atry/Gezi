package gezi.ir

/** The constructors of the IR's layers, each a class of its own over
  * children of type `Child`, shared by every consumer that admits it in its
  * union ([[Interned]]): the IR's terms, the codes, the patterns of lemmas,
  * the e-graph's nodes over classes, and the readers' and the JIT's terms.
  * Every layer but a parallel of terms is interned when it is made, and
  * outside the pool it is equal only to itself ([[ConstructorIdentity]]);
  * a parallel of terms is made as it is, for a construction site to convert
  * it to a native storage before it interns it (`Interned(layer)`).
  */
final case class Apply[+Child] private (function: Child, argument: Child) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer's term holds no neutral value ([[ConstructorIdentity.closed]]). */
  val closed: Boolean = ConstructorIdentity.closed(function) && ConstructorIdentity.closed(argument)

  /** Whether the layer's term holds no suspension and no other value extension ([[ConstructorIdentity.suspensionFree]]). */
  val suspensionFree: Boolean = ConstructorIdentity.suspensionFree(function) && ConstructorIdentity.suspensionFree(argument)

  /** The head of the application's spine: the function under every
    * application on the function's side, the function itself when it is no
    * application. The
    * layer's identity stays its function and argument, the spine's prefix
    * and its last argument, so that every prefix of a spine is a canonical
    * term (a table of the tabled reader, a class of the e-graph); the spine
    * is kept flat beside it, so that an argument is read by its index and
    * not by walking the prefixes. Over children that are no terms (the
    * e-graph's classes) the function is no application and the spine is the
    * layer itself. Computed when first read, by one walk along the prefixes
    * (`spineWalked`), so that a layer whose spine is never read holds no
    * copy of it: stored eagerly, the copies made the retained heap of the
    * library's expansions 5.2% larger, 73 bytes for each application
    * (measured 2026-11-20).
    */
  def spineHead: Child = spineWalked._1

  /** The arguments of the application's spine, the first applied first,
    * computed with `spineHead`.
    */
  def spineArguments: Vector[Child] = spineWalked._2

  /** The head and the arguments, found by one walk down the function's
    * side, in a loop so that a spine of any length costs no JVM stack.
    */
  private lazy val spineWalked: (Child, Vector[Child]) =
    @scala.annotation.tailrec
    def walked(current: Child, arguments: List[Child]): (Child, Vector[Child]) = current match
      case inner: Apply[Child @unchecked] => walked(inner.function, inner.argument :: arguments)
      case head                           => (head, arguments.toVector)
    walked(function, List(argument))

  /** The facts of the code this layer is the root of ([[Code.facts]]),
    * computed once; read only through `Code.facts`, on a code's layer.
    */
  private[ir] lazy val codeFacts: CodeFacts =
    Code.computedFacts(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

  /** The tail plans of the code this layer is the root of
    * ([[Code.tailPlans]]), computed once when first asked; read only through
    * `Code.tailPlans`, on a code's layer.
    */
  private[ir] lazy val codeTailPlans: Map[Int, TailPlan] =
    Code.computedTailPlans(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

/** A parallel of two sides. */
final case class Parallel[+Child] private (left: Child, right: Child) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer's term holds no neutral value ([[ConstructorIdentity.closed]]). */
  val closed: Boolean = ConstructorIdentity.closed(left) && ConstructorIdentity.closed(right)

  /** Whether the layer's term holds no suspension and no other value extension ([[ConstructorIdentity.suspensionFree]]). */
  val suspensionFree: Boolean = ConstructorIdentity.suspensionFree(left) && ConstructorIdentity.suspensionFree(right)

  /** The facts of the code this layer is the root of ([[Code.facts]]),
    * computed once; read only through `Code.facts`, on a code's layer.
    */
  private[ir] lazy val codeFacts: CodeFacts =
    Code.computedFacts(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

  /** The tail plans of the code this layer is the root of
    * ([[Code.tailPlans]]), computed once when first asked; read only through
    * `Code.tailPlans`, on a code's layer.
    */
  private[ir] lazy val codeTailPlans: Map[Int, TailPlan] =
    Code.computedTailPlans(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

object Parallel:
  /** The parallel of two children that cannot be terms of the IR (class numbers of the e-graph, codes, patterns),
    * interned when it is made. A child type that can hold an instruction is refused at compile time: a parallel of
    * terms is made only by a `NativeSpecializer`, which converts it into its storage first when it is the unique spelling
    * of one, so that no unspecialized object of a node that has a storage is ever made.
    */
  // TODO: deleted: the guard `(using scala.util.NotGiven[Instruction <:< Child])` of `Parallel.apply`. Wrong because
  // the guard is a negative implicit, and `Configured[C]` and `Value[C]` are opaque types with no upper bound, outside
  // `ir` it cannot infer `Instruction <:< Configured[C]` and lets such a child through, so it stands where the types
  // should say which configuration a child belongs to; issue https://github.com/Atry/private-overlay/issues/2261,
  // design v38, sections 1 and 6.
  // Read it back with `git show 7669694cc:gezi/ir/src/main/scala/gezi/ir/Constructors.scala`.
  def apply[Child](left: Child, right: Child)(using NotTerm[Child]): Parallel[Child] =
    Interned.canonicalLayer(new Parallel(left, right))


  /** The parallel of two terms, not interned: only `Interned.parallelOfTerms` calls it, for a `NativeSpecializer`. */
  private[ir] def ofTerms[Child](left: Child, right: Child): Parallel[Child] = new Parallel(left, right)

/** A binary choice, not a list (`CONTRIBUTING.md`, "Terms"):
  * a chain of several members nests to the right ([[ChoiceSpine]]), and
  * there is no empty choice.
  */
final case class Choice[+Child] private (left: Child, right: Child) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer's term holds no neutral value ([[ConstructorIdentity.closed]]). */
  val closed: Boolean = ConstructorIdentity.closed(left) && ConstructorIdentity.closed(right)

  /** Whether the layer's term holds no suspension and no other value extension ([[ConstructorIdentity.suspensionFree]]). */
  val suspensionFree: Boolean = ConstructorIdentity.suspensionFree(left) && ConstructorIdentity.suspensionFree(right)

  /** The number of members of the storage run this choice begins: the
    * members of its right spine when each is a native storage that precedes
    * the next in their canonical order (`NativeStorage.precedes`), two or
    * more; 0 for any other choice. Computed when the layer is made, from its
    * two sides in one step (the right side's run, or its storage), so that a
    * construction site tells in constant time whether `c ∥ T` is a group of
    * storages. A field of the body, not of the constructor: the layer's hash
    * code and equality read its two sides only. It reads only the storages'
    * own order (their native data, constructor positions and hash codes, the
    * first time a hash code is asked paid once per storage), no type.
    */
  val storageRun: Int = StorageRun.of(left, right)

  /** The facts of the code this layer is the root of ([[Code.facts]]),
    * computed once; read only through `Code.facts`, on a code's layer.
    */
  private[ir] lazy val codeFacts: CodeFacts =
    Code.computedFacts(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

  /** The tail plans of the code this layer is the root of
    * ([[Code.tailPlans]]), computed once when first asked; read only through
    * `Code.tailPlans`, on a code's layer.
    */
  private[ir] lazy val codeTailPlans: Map[Int, TailPlan] =
    Code.computedTailPlans(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))


object Choice:
  /** The canonical Choice: a layer that no construction site converts is interned when it is made. */
  def apply[Child](left: Child, right: Child)(using NotTerm[Child]): Choice[Child] =
    Interned.canonicalLayer(new Choice(left, right))

  /** The choice of two terms: only the native specializer and the value layer of this module call it. */
  private[ir] def ofTerms[Child](left: Child, right: Child): Choice[Child] = Interned.canonicalLayer(new Choice(left, right))

/** A thunk, a lambda chain: its code, the hole of each binder in lambda order,
  * and the fillings of the code's other slots in slot order. Inside a code,
  * an inner thunk's fillings are codes read with the enclosing code's slots.
  */
final case class Thunk[+Child] private (code: Code, holes: Vector[Hole], fillings: Vector[Child]) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer's term holds no neutral value ([[ConstructorIdentity.closed]]). */
  val closed: Boolean = fillings.forall(ConstructorIdentity.closed)

  /** Whether the layer's term holds no suspension and no other value extension ([[ConstructorIdentity.suspensionFree]]). */
  val suspensionFree: Boolean = fillings.forall(ConstructorIdentity.suspensionFree)

  /** The facts of the code this layer is the root of ([[Code.facts]]),
    * computed once; read only through `Code.facts`, on a code's layer.
    */
  private[ir] lazy val codeFacts: CodeFacts =
    Code.computedFacts(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

  /** The tail plans of the code this layer is the root of
    * ([[Code.tailPlans]]), computed once when first asked; read only through
    * `Code.tailPlans`, on a code's layer.
    */
  private[ir] lazy val codeTailPlans: Map[Int, TailPlan] =
    Code.computedTailPlans(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))


object Thunk:
  /** The canonical Thunk: a layer that no construction site converts is interned when it is made. */
  def apply[Child](code: Code, holes: Vector[Hole], fillings: Vector[Child])(using NotTerm[Child]): Thunk[Child] =
    Interned.canonicalLayer(new Thunk(code, holes, fillings))

  /** The thunk over terms: only the native specializer and the value layer of this module call it. */
  private[ir] def ofTerms[Child](code: Code, holes: Vector[Hole], fillings: Vector[Child]): Thunk[Child] =
    Interned.canonicalLayer(new Thunk(code, holes, fillings))

/** A URI node: a term named by an absolute URI, equal to its expansion by
  * the front end's equation ([[Instruction]], `CONTRIBUTING.md`, "Terms";
  * the front end supports absolute URIs only). Opaque: its layer is no part of the IR. A URI is an
  * identity only; nothing but the front end's expansion reads any part of it.
  */
final case class UriNode private (uri: java.net.URI) extends InternedConstructor:
  if !uri.isAbsolute then throw IllegalArgumentException(s"a URI node's URI is absolute: $uri")
  override def toString: String = s"uri node $uri"

/** An opaque term, named by a string, whose layer is not known: the noinline
  * terms of an exported fixture, which the exporter wrote without their
  * layers, and those of generated stores.
  */
final case class Opaque private (name: String) extends InternedConstructor:
  override def toString: String = s"opaque instruction $name"


object Opaque:
  /** The canonical Opaque: a layer that no construction site converts is interned when it is made. */
  def apply(name: String): Opaque = Interned.canonicalLayer(new Opaque(name))

/** A reference to the slot of the index, inside a code. */
final case class Slot private (index: Int) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

  /** The facts of the code this layer is the root of ([[Code.facts]]),
    * computed once; read only through `Code.facts`, on a code's layer.
    */
  private[ir] lazy val codeFacts: CodeFacts =
    Code.computedFacts(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))

  /** The tail plans of the code this layer is the root of
    * ([[Code.tailPlans]]), computed once when first asked; read only through
    * `Code.tailPlans`, on a code's layer.
    */
  private[ir] lazy val codeTailPlans: Map[Int, TailPlan] =
    Code.computedTailPlans(Interned.ofCanonicalLayer[CodeLayer](this.asInstanceOf[CodeLayer[Code]]))


object Slot:
  /** The canonical Slot: a layer that no construction site converts is interned when it is made. */
  def apply(index: Int): Slot = Interned.canonicalLayer(new Slot(index))

/** A noinline leaf: a term the e-graph never unfolds, a node of its own. */
final case class NoinlineLeaf[+Term] private (term: Term) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)


object NoinlineLeaf:
  /** The canonical NoinlineLeaf: a layer that no construction site converts is interned when it is made. */
  def apply[Term](term: Term): NoinlineLeaf[Term] = Interned.canonicalLayer(new NoinlineLeaf(term))

/** A metavariable of a lemma's side, by its index. */
final case class Metavariable private (index: Int) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)


object Metavariable:
  /** The canonical Metavariable: a layer that no construction site converts is interned when it is made. */
  def apply(index: Int): Metavariable = Interned.canonicalLayer(new Metavariable(index))

/** The eta-shaped lambda `\x. M x` of a lemma's side, read as the class of
  * the metavariable M of the index holding a closure state.
  */
final case class ClosureMetavariable private (index: Int) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)


object ClosureMetavariable:
  /** The canonical ClosureMetavariable: a layer that no construction site converts is interned when it is made. */
  def apply(index: Int): ClosureMetavariable = Interned.canonicalLayer(new ClosureMetavariable(index))

/** The operations every layer shares, as extensions in the companion of
  * [[Apply]]: every union of layers admits `Apply`, so its companion is in the
  * implicit scope of each and no call site imports them.
  */
object Apply:

  /** The canonical Apply: a layer that no construction site converts is interned when it is made. */
  def apply[Child](function: Child, argument: Child)(using NotTerm[Child]): Apply[Child] =
    Interned.canonicalLayer(new Apply(function, argument))

  /** The application of terms: only the native specializer and the value layer of this module call it. */
  private[ir] def ofTerms[Child](function: Child, argument: Child): Apply[Child] =
    Interned.canonicalLayer(new Apply(function, argument))


  extension [Child](layer: Layer[Child] | IrLayer[Child])
    /** The children, in the order a layer is built: function before argument,
      * left before right, fillings in order; none under a leaf, a URI node or
      * an opaque term.
      */
    def children: Vector[Child] = layer match
      case Apply(function, argument)                => Vector(function, argument)
      case Parallel(left, right)                    => Vector(left, right)
      case Choice(left, right)                      => Vector(left, right)
      case Thunk(_, _, fillings)                    => fillings
      case StorageView(value, criterion)            => Vector(value, criterion)
      // A storage is a leaf of its term's layer: its view is read only with `StorageAccess`.
      case NoinlineLeaf(_) | UriNode(_) | Opaque(_) | (_: NativeStorage) => Vector.empty

  extension [Child, Leaf](layer: LayerWith[Child, Leaf])
    /** The layer with its children replaced, in the order of `children`.
      * Throws `IllegalArgumentException` when their number is not the
      * layer's.
      */
    def over[Result](replaced: Vector[Result])(using NotTerm[Result]): LayerWith[Result, Leaf] =
      require(replaced.size == layer.children.size, s"${replaced.size} children for the layer $layer")
      layer match
        case Apply(_, _) =>
          val Vector(function, argument) = replaced: @unchecked
          // The using clause names the public construction: in this companion the case class's own `apply` is visible too.
          Apply(function, argument)(using summon[NotTerm[Result]])
        case Parallel(_, _) =>
          val Vector(left, right) = replaced: @unchecked
          Parallel(left, right)
        case Choice(_, _) =>
          val Vector(left, right) = replaced: @unchecked
          Choice(left, right)
        case Thunk(code, holes, _) => Thunk(code, holes, replaced)
        case StorageView(_, _) =>
          val Vector(value, criterion) = replaced: @unchecked
          StorageView(value, criterion)
        case leaf @ NoinlineLeaf(_) => leaf

    /** The layer with each child mapped. */
    def map[Result](mapping: Child => Result)(using NotTerm[Result]): LayerWith[Result, Leaf] = layer match
      case Apply(function, argument)    => Apply(mapping(function), mapping(argument))(using summon[NotTerm[Result]])
      case Parallel(left, right)        => Parallel(mapping(left), mapping(right))
      case Choice(left, right)          => Choice(mapping(left), mapping(right))
      case Thunk(code, holes, fillings) => Thunk(code, holes, fillings.map(mapping))
      case StorageView(value, criterion) => StorageView(mapping(value), mapping(criterion))
      case leaf @ NoinlineLeaf(_)       => leaf

/** The operations of an [[Instruction]] beyond its layer, as extensions in
  * the companion of [[UriNode]], a constructor of [[IrLayer]], which puts them
  * in the implicit scope of `Instruction`.
  */
object UriNode:

  /** The canonical UriNode: a layer that no construction site converts is interned when it is made. */
  def apply(uri: java.net.URI): UriNode = Interned.canonicalLayer(new UriNode(uri))


  extension (instruction: Instruction)
    /** Whether the instruction is opaque: named, its layer no part of the IR.
      * A URI node is opaque. A native storage is not, and is answered by a
      * class test, its view not read.
      */
    def opaque: Boolean = !NativeStorage.stored(instruction) && (instruction.layer match
      case UriNode(_) | Opaque(_) => true
      case _                      => false
    )

    /** Whether the e-graph holds the instruction as a leaf whose layer it
      * never reads: an opaque instruction, or a native storage it keeps as a
      * leaf (`NativeStorage.leafInEGraph`). A walk of the terms the graph
      * holds stops at it, by a class test and one layer read at most.
      */
    def heldAsLeaf: Boolean = (instruction: AnyRef) match
      case storage: NativeStorage => storage.leafInEGraph
      case _                      => opaque

    /** The URI of a URI node; none for any other instruction, a native
      * storage answered by a class test, its view not read.
      */
    def uri: Option[java.net.URI] = if NativeStorage.stored(instruction) then None else instruction.layer match
      case UriNode(uri) => Some(uri)
      case _            => None

    /** The instruction's layer as a layer of the IR proper, the e-graph's
      * [[Layer]]: a native storage a leaf, its view read only with the capability. Throws `IllegalStateException` for
      * an opaque instruction, a URI node included, whose layer is no part of the IR.
      */
    def layered: Layer[Instruction] = instruction.layer match
      case application @ Apply(_, _) => application
      case parallel @ Parallel(_, _) => parallel
      case choice @ Choice(_, _)     => choice
      case thunk @ Thunk(_, _, _)    => thunk
      case _: NativeStorage          => NoinlineLeaf(instruction)
      case UriNode(_) | Opaque(_)    => throw IllegalStateException(s"the $instruction has no layer")

/** The storage runs of choices (`Choice.storageRun`). */
object StorageRun:

  /** The run a choice of the two sides begins: 2 when both are storages and
    * the left precedes the right, one more than the right's run when the left
    * precedes the right's first member, 0 otherwise.
    */
  def of(left: Any, right: Any): Int = left match
    case first: NativeStorage =>
      right match
        case second: NativeStorage if first.precedes(second) => 2
        case rest: Choice[?] if rest.storageRun > 0 =>
          rest.left match
            case next: NativeStorage if first.precedes(next) => rest.storageRun + 1
            case _                                           => 0
        case _ => 0
    case _ => 0

  /** The members of the run the choice begins, in order: its left side, and
    * the run's members of its right side. Throws `IllegalArgumentException`
    * for a choice that begins no run.
    */
  def members(choice: Choice[?]): Vector[NativeStorage] =
    if choice.storageRun < 2 then throw IllegalArgumentException(s"the choice begins no storage run: $choice")
    @scala.annotation.tailrec
    def collected(current: Any, found: Vector[NativeStorage]): Vector[NativeStorage] = current match
      case run: Choice[?] if run.storageRun > 0 =>
        run.left match
          case storage: NativeStorage => collected(run.right, found :+ storage)
          case other                  => throw IllegalStateException(s"a storage run whose member is no storage: $other")
      case last: NativeStorage => found :+ last
      case other               => throw IllegalStateException(s"a storage run that ends in no storage: $other")
    collected(choice, Vector.empty)
