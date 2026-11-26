package gezi.ir

/** Every term is interned, and no term that is not interned is supported:
  * an `Interned[Layer]` is the one live object
  * whose content equals a layer of the constructors `Layer` admits, its
  * children themselves interned. Each constructor is a class of its own, and a
  * consumer states which constructors it accepts by a union type, with no
  * enum and no marker trait: the IR's `IrLayer`, and the readers' and the
  * JIT's wider unions over the same classes, all in one Caffeine weak
  * interner.
  *
  * At run time an interned term is the constructor object itself, with no
  * wrapper: an opaque type, not an `AnyVal`.
  * The parameter is covariant, so a term of a narrower union is a term of a
  * wider one with no conversion: an IR instruction is a term of every
  * consumer whose union includes `IrLayer` at every layer.
  *
  * Two terms are one term exactly when they are one object (`eq`), since
  * only `apply` makes one and it returns the canonical object. A term no
  * longer reachable is collected, so reference equality holds between two
  * terms only while both are reachable (an identity kept across a
  * collection needs a strong reference to the term). The pool is
  * `Canonicalization`'s: Caffeine's weak interner on the JVM, and under
  * Scala.js a map of weak references of this repository
  * (`ir-js/src/main/scala/gezi/ir/Canonicalization.scala`). Code
  * compares terms by `==`, which ends at `eq` or at a differing hash code.
  */
object Interned:

  opaque type Interned[+Layer[_]] <: AnyRef = AnyRef

  /** The canonical term of the layer, whose children are canonical terms. */
  def apply[Layer[_]](layer: Layer[Interned[Layer]]): Interned[Layer] =
    Canonicalization.term(layer.asInstanceOf[AnyRef])

  /** The term whose layer is the object, which must be a canonical term's
    * layer (a constructor object reached through `layer`, or `this` of such
    * an object): the inverse of `layer`.
    */
  private[ir] def ofCanonicalLayer[Layer[_]](layer: Layer[Interned[Layer]]): Interned[Layer] =
    layer.asInstanceOf[AnyRef]

  extension [Layer[_]](term: Interned[Layer])
    /** The term's layer: the constructor object itself. Sound because an
      * `Interned[Layer]` is made only by `apply` from a `Layer` over
      * `Interned[Layer]` children.
      */
    inline def layer: Layer[Interned[Layer]] = term.asInstanceOf[Layer[Interned[Layer]]]

/** The structural equality and the hash code every constructor class shares:
  * equal when the same object, or of the same class with the same hash code
  * and fields equal by `==`. Between canonical terms a child's `==` is
  * decided by its hash code unless two different terms collide, so that
  * comparing a layer costs its width. The hash code is the case class's, from
  * its name and its fields' hash codes, computed once by each class and the
  * same in every process when the fields' are.
  */
object ConstructorIdentity:

  def hash(product: Product): Int = scala.util.hashing.MurmurHash3.caseClassHash(product)

  /** Whether the term is an instruction: a layer of the IR's constructors
    * whose parts are instructions, a URI node or an opaque term. Each layer
    * with parts computes it when it is made, from its parts' (which were
    * made before it), so the question costs one field read whatever the
    * term's size. False for a layer of any other constructor (a neutral
    * value, a value of the JIT's own, a class of the e-graph), and for an
    * inner thunk of a code, whose fillings are codes.
    */
  def isInstruction(term: Any): Boolean = term match
    case application: Apply[?]  => application.isInstruction
    case parallel: Parallel[?]  => parallel.isInstruction
    case choice: Choice[?]      => choice.isInstruction
    case thunk: Thunk[?]        => thunk.isInstruction
    case _: UriNode | _: Opaque => true
    case _                      => false

  def equal(product: Product & AnyRef, other: Any): Boolean = other match
    case that: (Product & AnyRef) =>
      (product eq that) || ((product.getClass eq that.getClass) && product.hashCode == that.hashCode &&
        (0 until product.productArity).forall(index => product.productElement(index) == that.productElement(index)))
    case _ => false

  /** The constructor's name and its hash code in hexadecimal, then its
    * fields: a hole as itself, a vector field element by element, any other
    * case class (a child term) by its name and hash code, and anything else
    * (an index, a name, a class of the e-graph) as itself. One layer,
    * deterministic and short whatever the term's depth.
    */
  def shown(product: Product): String =
    def child(element: Any): String = element match
      case hole: Hole           => hole.toString
      case vector: Vector[?]    => vector.map(child).mkString("[", ", ", "]")
      case constructor: Product => s"${constructor.productPrefix}#${constructor.hashCode.toHexString}"
      case other                => other.toString
    (0 until product.productArity)
      .map(index => child(product.productElement(index)))
      .mkString(s"${product.productPrefix}#${product.hashCode.toHexString}(", ", ", ")")
