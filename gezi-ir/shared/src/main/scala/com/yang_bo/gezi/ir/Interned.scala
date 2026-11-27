package com.yang_bo.gezi.ir

/** Every term is interned, and no term that is not interned is supported: an
  * `Interned[Layer]` is the one live object whose content equals a layer of the
  * constructors `Layer` admits, its children themselves interned. Each
  * constructor is a class of its own, and a consumer states which constructors
  * it accepts by a union type, with no enum and no marker trait: the IR's
  * `IrLayer`, and the readers' and the JIT's wider unions over the same
  * classes, all in one Caffeine weak interner.
  *
  * At run time an interned term is the constructor object itself, with no
  * wrapper: an opaque type, not an `AnyVal`. The parameter is covariant, so a
  * term of a narrower union is a term of a wider one with no conversion: an IR
  * instruction is a term of every consumer whose union includes `IrLayer` at
  * every layer.
  *
  * Two terms are one term exactly when they are one object (`eq`), since only
  * `apply` makes one and it returns the canonical object. A term no longer
  * reachable is collected, so reference equality holds between two terms only
  * while both are reachable (an identity kept across a collection needs a
  * strong reference to the term). The pool is `Canonicalization`'s: Caffeine's
  * weak interner on the JVM, and under Scala.js a map of weak references of
  * this repository (`ir-js/src/main/scala/gezi/ir/Canonicalization.scala`).
  * Outside the pool `==` of two interned constructor objects is `eq`.
  */
object Interned:

  opaque type Interned[+Layer[_]] <: AnyRef = AnyRef

  /** The canonical term of the layer, whose children are canonical terms. */
  def apply[Layer[_]](layer: Layer[Interned[Layer]]): Interned[Layer] =
    layer.asInstanceOf[AnyRef] match
      case constructor: InternedConstructor =>
        constructor // interned when it was made (its companion's apply)
      case other => Canonicalization.term(other)

  /** The parallel of two terms as written, interned: only a `NativeSpecializer`
    * calls it, after finding that the parallel is the unique spelling of no
    * storage.
    */
  private[ir] def parallelOfTerms[Layer[_]](
      left: Interned[Layer],
      right: Interned[Layer]
  ): Interned[Layer] =
    Canonicalization.term(Parallel.ofTerms(left, right))

  /** The canonical term of a native storage that a consumer made directly (a
    * native's result), interned through the pool as every term is: one object
    * per storage, compared only with storages. The storage's view must be a
    * layer the consumer's `Layer` admits.
    */
  private[ir] def stored[Layer[_]](storage: NativeStorage): Interned[Layer] =
    Canonicalization.term(storage)

  /** The canonical object of a layer whose children are leaves, not terms, such
    * as the e-graph's layers over class numbers: interned through the pool as
    * every term is, so that two such layers equal by content are one object
    * while either is reachable.
    */
  def canonicalLayer[Layer <: AnyRef](layer: Layer): Layer =
    Canonicalization.term(layer).asInstanceOf[Layer]

  /** The term whose layer is the object, which must be a canonical term's layer
    * (a constructor object reached through `layer`, or `this` of such an
    * object): the inverse of `layer`.
    */
  private[ir] def ofCanonicalLayer[Layer[_]](
      layer: Layer[Interned[Layer]]
  ): Interned[Layer] =
    layer.asInstanceOf[AnyRef]

  extension [Layer[_]](term: Interned[Layer])
    /** The term's layer: the constructor object itself, a native storage
      * included, which is a leaf of its term's layer (a consumer's union admits
      * it as `IrLayer` does). Sound because an `Interned[Layer]` is made only
      * by `apply` from a `Layer` over `Interned[Layer]` children, or is a
      * storage a `NativeSpecializer` made.
      */
    inline def layer: Layer[Interned[Layer]] =
      term.asInstanceOf[Layer[Interned[Layer]]]

/** The hash code and the equality of the interned constructors. Outside the
  * pool an interned object is equal only to itself and hashes by its identity:
  * every constructor object a consumer holds is canonical, so two equal by
  * content are one object, but for a parallel of terms not yet interned
  * (`Parallel.apply`) and a storage's view, which a consumer compares by its
  * sides. The pool (`Canonicalization`) asks the object it interns for its
  * single layer's hash code and equality instead (`singleLayerHash`,
  * `singleLayerEqual`): its fields that are constructor objects by their
  * identity, since they are canonical, so that interning a layer costs its
  * width, reads no field's term below it, and caches nothing. A native
  * storage's hash code and equality are its own, by its representation and
  * native data (`com.yang_bo.gezi.jit.RepresentedStorage`), and a storage equals storages
  * only.
  *
  * Identity hash codes differ from one run to the next, so no output may depend
  * on an order of hash codes: an order of terms is by their content
  * (`com.yang_bo.gezi.extraction.ContentOrder`).
  *
  * The single-layer hash folds the fields in order from the name's string hash,
  * each step `F(a, r) = c0 + c1·a + c2·r + c3·a·r` modulo the prime p = 2^31^ −
  * 1, a the value so far and r the field's hash reduced modulo p: the term
  * `c3·a·r` makes a field's factor depend on the fields before it, so that two
  * layers whose fields are a permutation of each other's differ. Collisions
  * cost speed only: equality reads the fields.
  */
object ConstructorIdentity:

  /** The prime the raw values are residues modulo: 2^31^ − 1. */
  private val modulus: Long = 2147483647L

  /** The constants of a step `F(a, r) = c0 + c1·a + c2·r + c3·a·r`: residues
    * that are no small multiples of one another (c1, c2 and c3 primitive roots
    * modulo p).
    */
  private val constant: Long = 1013904223L
  private val factorOfSoFar: Long = 48271L
  private val factorOfField: Long = 69621L
  private val factorOfBoth: Long = 16807L

  /** `F(a, r) = c0 + c2·r + a·(c1 + c3·r)` modulo p, a and r residues: three
    * products, each below 2^62^, and no division.
    */
  private def step(accumulated: Int, fieldRaw: Int): Int =
    val factor = mersenne(factorOfSoFar + mersenne(factorOfBoth * fieldRaw))
    mersenne(
      constant + mersenne(
        factorOfField * fieldRaw
      ) + factor.toLong * accumulated
    )

  /** The residue of a 32-bit value, read as unsigned, modulo p. */
  private def reduced(value: Int): Int = mersenne(value.toLong & 0xffffffffL)

  /** The residue modulo p = 2^31^ − 1 of a value below 2^63^, without a
    * division: 2^31^ ≡ 1, so the high bits fold onto the low ones, twice, and
    * one subtraction leaves a residue.
    */
  private def mersenne(value: Long): Int =
    val once = (value & modulus) + (value >>> 31)
    val twice = (once & modulus) + (once >>> 31)
    (if twice >= modulus then twice - modulus else twice).toInt

  /** The value of a hash code in the hash: the hash code reduced modulo p,
    * which a constructor's hash code, a residue, already is.
    */
  def raw(hash: Int): Int = reduced(hash)

  /** Whether the term holds no neutral value: a layer of the IR's constructors
    * whose parts hold none, a URI node, an opaque term, a native storage that
    * holds none, or a value extension that says so (a suspension does, a
    * neutral value does not). Each layer with parts computes it when it is
    * made, from its parts' (made before it), so the question costs one field
    * read whatever the term's size. False for anything else (a class of the
    * e-graph, an inner thunk of a code, whose fillings are codes).
    */
  def closed(term: Any): Boolean = term match
    case application: Apply[?]        => application.closed
    case parallel: Parallel[?]        => parallel.closed
    case choice: Choice[?]            => choice.closed
    case thunk: Thunk[?]              => thunk.closed
    case _: UriNode | _: Opaque       => true
    case storage: NativeStorage       => storage.closed
    case extension: ValueExtension[?] => extension.closed
    case _                            => false

  /** Whether the term holds no value extension at all (no suspension, no
    * neutral value, no sharing cell), so that it is a term of the IR: computed
    * as `closed` is, a value extension answering false by `ValueExtension`'s
    * final definition.
    */
  def suspensionFree(term: Any): Boolean = term match
    case application: Apply[?]  => application.suspensionFree
    case parallel: Parallel[?]  => parallel.suspensionFree
    case choice: Choice[?]      => choice.suspensionFree
    case thunk: Thunk[?]        => thunk.suspensionFree
    case _: UriNode | _: Opaque => true
    case storage: NativeStorage => storage.suspensionFree
    case _                      => false

  /** The single-layer hash code the pool reads: the constructor's name and its
    * fields, a field that is an interned constructor by its identity, a vector
    * field element by element, any other field (an index, a class number, a
    * name, a hole, a native storage) by its own hash code.
    */
  def singleLayerHash(product: Product): Int =
    @scala.annotation.tailrec
    def fields(index: Int, accumulated: Int): Int =
      if index == product.productArity then accumulated
      else
        fields(
          index + 1,
          step(accumulated, raw(fieldHash(product.productElement(index))))
        )
    fields(0, reduced(product.productPrefix.hashCode))

  private def fieldHash(field: Any): Int = field match
    case interned: InternedConstructor => System.identityHashCode(interned)
    case vector: Vector[?]             =>
      vector.foldLeft(reduced(vector.size))((accumulated, element) =>
        step(accumulated, raw(fieldHash(element)))
      )
    case other => other.##

  /** The single-layer equality the pool reads: of the same class, each pair of
    * fields the same, a field that is an interned constructor by identity, a
    * vector element by element, any other of one class and by `==` (a native
    * storage, interned when made, by its identity). Two layers whose
    * constructor fields are canonical, as every constructor object passed to a
    * constructor is, are equal by it exactly when equal by content.
    */
  def singleLayerEqual(product: Product & AnyRef, other: Any): Boolean =
    other match
      case that: (Product & AnyRef) =>
        (product eq that) || ((product.getClass eq that.getClass) &&
          (0 until product.productArity).forall(index =>
            sameField(product.productElement(index), that.productElement(index))
          ))
      case _ => false

  private def sameField(left: Any, right: Any): Boolean = (left, right) match
    case (interned: InternedConstructor, other: AnyRef)  => interned eq other
    case (leftVector: Vector[?], rightVector: Vector[?]) =>
      leftVector.size == rightVector.size && leftVector
        .lazyZip(rightVector)
        .forall(sameField)
    // Of one class first: Scala's == is cooperative between numbers, so that
    // `Apply(0, 1)` over class numbers and `Apply(BigInt(0), BigInt(1))`, one
    // model's costs, would be one object of the wrong children otherwise.
    case (leftValue: AnyRef, rightValue: AnyRef) =>
      (leftValue.getClass eq rightValue.getClass) && leftValue == rightValue
    case _ => left == right

  /** The constructor's name, then its fields: a hole as itself, a vector field
    * element by element, any other case class (a child term) by its name, and
    * anything else (an index, a name, a class of the e-graph) as itself. One
    * layer, deterministic and short whatever the term's depth; no hash code, an
    * identity, is shown.
    */
  def shown(product: Product): String =
    def child(element: Any): String = element match
      case hole: Hole           => hole.toString
      case vector: Vector[?]    => vector.map(child).mkString("[", ", ", "]")
      case constructor: Product => constructor.productPrefix
      case other                => other.toString
    (0 until product.productArity)
      .map(index => child(product.productElement(index)))
      .mkString(s"${product.productPrefix}(", ", ", ")")

/** The hash code and the equality of every interned constructor class, one
  * definition for all: the object's identity, except while the pool interns
  * this very object (`Canonicalization.interning`), when they are its single
  * layer's (`ConstructorIdentity.singleLayerHash`, `singleLayerEqual`). An
  * implementation shared by the constructor classes, not a type: no consumer's
  * union is written with it.
  */
trait InternedConstructor extends Product:

  override def hashCode: Int =
    if Canonicalization.interning(this) then
      ConstructorIdentity.singleLayerHash(this)
    else System.identityHashCode(this)

  override def equals(other: Any): Boolean = other match
    case that: AnyRef =>
      (this eq that) || ((Canonicalization.interning(this) || Canonicalization
        .interning(that)) && ConstructorIdentity.singleLayerEqual(this, that))
    case _ => false
