package gezi.ir

/** The constructors of the IR's layers, each a class of its own over
  * children of type `Child`, shared by every consumer that admits it in its
  * union ([[Interned]]): the IR's terms, the codes, the patterns of lemmas,
  * the e-graph's nodes over classes, and the readers' and the JIT's terms.
  * A layer is a value, equal by content ([[ConstructorIdentity]]); its
  * canonical term is `Interned(layer)`.
  */
final case class Apply[+Child](function: Child, argument: Child):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer is an instruction's ([[ConstructorIdentity.isInstruction]]). */
  val isInstruction: Boolean = ConstructorIdentity.isInstruction(function) && ConstructorIdentity.isInstruction(argument)

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
final case class Parallel[+Child](left: Child, right: Child):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer is an instruction's ([[ConstructorIdentity.isInstruction]]). */
  val isInstruction: Boolean = ConstructorIdentity.isInstruction(left) && ConstructorIdentity.isInstruction(right)

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

/** A binary choice, not a list (`CONTRIBUTING.md`, "Terms"):
  * a chain of several members nests to the right ([[ChoiceSpine]]), and
  * there is no empty choice.
  */
final case class Choice[+Child](left: Child, right: Child):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer is an instruction's ([[ConstructorIdentity.isInstruction]]). */
  val isInstruction: Boolean = ConstructorIdentity.isInstruction(left) && ConstructorIdentity.isInstruction(right)

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

/** A thunk, a lambda chain: its code, the hole of each binder in lambda order,
  * and the fillings of the code's other slots in slot order. Inside a code,
  * an inner thunk's fillings are codes read with the enclosing code's slots.
  */
final case class Thunk[+Child](code: Code, holes: Vector[Hole], fillings: Vector[Child]):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether the layer is an instruction's ([[ConstructorIdentity.isInstruction]]). */
  val isInstruction: Boolean = fillings.forall(ConstructorIdentity.isInstruction)

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

/** A URI node: a term named by an absolute URI, equal to its expansion by
  * the front end's equation ([[Instruction]], `CONTRIBUTING.md`, "Terms";
  * the front end supports absolute URIs only). Opaque: its layer is no part of the IR. A URI is an
  * identity only; nothing but the front end's expansion reads any part of it.
  */
final case class UriNode(uri: java.net.URI):
  if !uri.isAbsolute then throw IllegalArgumentException(s"a URI node's URI is absolute: $uri")
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = s"uri node $uri"

/** An opaque term, named by a string, whose layer is not known: the noinline
  * terms of an exported fixture, which the exporter wrote without their
  * layers, and those of generated stores.
  */
final case class Opaque(name: String):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = s"opaque instruction $name"

/** A reference to the slot of the index, inside a code. */
final case class Slot(index: Int):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
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

/** A noinline leaf: a term the e-graph never unfolds, a node of its own. */
final case class NoinlineLeaf[+Term](term: Term):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** A metavariable of a lemma's side, by its index. */
final case class Metavariable(index: Int):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The eta-shaped lambda `\x. M x` of a lemma's side, read as the class of
  * the metavariable M of the index holding a closure state.
  */
final case class ClosureMetavariable(index: Int):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The operations every layer shares, as extensions in the companion of
  * [[Apply]]: every union of layers admits `Apply`, so its companion is in the
  * implicit scope of each and no call site imports them.
  */
object Apply:

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
      case NoinlineLeaf(_) | UriNode(_) | Opaque(_) => Vector.empty

  extension [Child](layer: Layer[Child])
    /** The layer with its children replaced, in the order of `children`.
      * Throws `IllegalArgumentException` when their number is not the
      * layer's.
      */
    def over[Result](replaced: Vector[Result]): Layer[Result] =
      require(replaced.size == layer.children.size, s"${replaced.size} children for the layer $layer")
      layer match
        case Apply(_, _) =>
          val Vector(function, argument) = replaced: @unchecked
          Apply(function, argument)
        case Parallel(_, _) =>
          val Vector(left, right) = replaced: @unchecked
          Parallel(left, right)
        case Choice(_, _) =>
          val Vector(left, right) = replaced: @unchecked
          Choice(left, right)
        case Thunk(code, holes, _) => Thunk(code, holes, replaced)
        case leaf @ NoinlineLeaf(_) => leaf

    /** The layer with each child mapped. */
    def map[Result](mapping: Child => Result): Layer[Result] = layer match
      case Apply(function, argument)    => Apply(mapping(function), mapping(argument))
      case Parallel(left, right)        => Parallel(mapping(left), mapping(right))
      case Choice(left, right)          => Choice(mapping(left), mapping(right))
      case Thunk(code, holes, fillings) => Thunk(code, holes, fillings.map(mapping))
      case leaf @ NoinlineLeaf(_)       => leaf

/** The operations of an [[Instruction]] beyond its layer, as extensions in
  * the companion of [[UriNode]], a constructor of [[IrLayer]], which puts them
  * in the implicit scope of `Instruction`.
  */
object UriNode:

  extension (instruction: Instruction)
    /** Whether the instruction is opaque: named, its layer no part of the IR.
      * A URI node is opaque.
      */
    def opaque: Boolean = instruction.layer match
      case UriNode(_) | Opaque(_) => true
      case _                      => false

    /** The URI of a URI node; none for any other instruction. */
    def uri: Option[java.net.URI] = instruction.layer match
      case UriNode(uri) => Some(uri)
      case _            => None

    /** The instruction's layer as a layer of the IR proper, the e-graph's
      * [[Layer]]. Throws `IllegalStateException` for an opaque instruction,
      * a URI node included, whose layer is no part of the IR.
      */
    def layered: Layer[Instruction] = instruction.layer match
      case application @ Apply(_, _) => application
      case parallel @ Parallel(_, _) => parallel
      case choice @ Choice(_, _)     => choice
      case thunk @ Thunk(_, _, _)    => thunk
      case UriNode(_) | Opaque(_)    => throw IllegalStateException(s"the $instruction has no layer")
