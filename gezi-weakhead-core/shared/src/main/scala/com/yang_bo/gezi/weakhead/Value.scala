package com.yang_bo.gezi.weakhead

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.ConstructorIdentity
import com.yang_bo.gezi.ir.InternedConstructor
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.Interned.Interned
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.Opaque
import com.yang_bo.gezi.ir.UriNode
import com.yang_bo.gezi.ir.{
  Closed,
  Configured,
  NativeSpecializer,
  Value,
  ValueExtension,
  ValueLayer
}

/** The variable of a neutral value: a value that the reader who makes the
  * neutral value chooses (a normal-form reader names its bound variables by
  * their depth, a codec its cases by its decoding), compared by `==`, so two
  * neutral values have the same variable exactly when their variables are equal
  * values. Each reader defines its own variables as case classes or case
  * objects of flat fields; the evaluator never looks inside one.
  */
trait NeutralVariable:

  /** Whether a neutral value of this variable applied to no argument stands for
    * a closed term, every read of which is closed: false unless the reader that
    * made the variable knows it to be such a leaf. The normal-form reader asks
    * it where it decides that a head is closed (`NormalForms`, the rule of a
    * closed head beside an opened variable). Answering true for a leaf that
    * holds an opened variable makes that rule read ∅ where the set has reads;
    * answering false only keeps the rule from sparing the reading of the heads.
    */
  def closedLeaf: Boolean = false

/** The free variable applied to the arguments, a head nothing reduces: an
  * extension of the readers' values beside the IR's layers
  * (`com.yang_bo.gezi.ir.ValueExtension`), not closed. A neutral value lives only in the
  * evaluator and its readers: it is no layer of the IR, of the e-graph or of
  * the index (`CONTRIBUTING.md`, "Types live only in the term").
  */
final case class Neutral[+Child] private (
    variable: NeutralVariable,
    arguments: Vector[Child]
) extends InternedConstructor
    with ValueExtension[Child]:
  override def toString: String = ConstructorIdentity.shown(this)

  /** False: a neutral value is a free variable. */
  def closed: Boolean = false

object Neutral:

  /** The canonical Neutral layer. */
  def apply[Child](
      variable: NeutralVariable,
      arguments: Vector[Child]
  ): Neutral[Child] =
    Interned.canonicalLayer(new Neutral(variable, arguments))

  extension [C <: NativeSpecializer & Singleton](head: Head[C])(using C)
    /** The head as a value: the interned value whose layer it is. */
    def value: Value[C] = head match
      case com.yang_bo.gezi.weakhead.Neutral(variable, arguments) =>
        NeutralValue(variable, arguments)
      case thunk @ com.yang_bo.gezi.ir.Thunk(_, _, _) => Head.lambdaValue(thunk)

/** A suspension: a code all of whose holes are filled, its instance delayed
  * until a reader reads it (today's reading is a call of the code). An
  * extension of the readers' values, no term of the IR: a thunk with no holes
  * built as a term would pass a computation for a term. Closed when its
  * fillings are.
  */
final case class Suspension[+Child] private (
    code: Code,
    fillings: Vector[Child]
) extends InternedConstructor
    with ValueExtension[Child]:
  override def toString: String = ConstructorIdentity.shown(this)

  /** Whether its fillings hold no neutral value, computed when it is made. */
  val closed: Boolean = fillings.forall(ConstructorIdentity.closed)

object Suspension:

  /** The canonical Suspension layer. */
  def apply[Child](code: Code, fillings: Vector[Child]): Suspension[Child] =
    Interned.canonicalLayer(new Suspension(code, fillings))

/** A neutral value as a value of a configuration, and its parts. */
object NeutralValue:
  def apply[C <: NativeSpecializer & Singleton](
      variable: NeutralVariable,
      arguments: Vector[Value[C]]
  )(using C): Value[C] =
    Value.extension(Neutral(variable, arguments))

  def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Option[(NeutralVariable, Vector[Value[C]])] =
    value.layer match
      case Neutral(variable, arguments) => Some((variable, arguments))
      case _                            => None

/** A suspension as a value of a configuration, and its parts. */
object SuspensionValue:
  def apply[C <: NativeSpecializer & Singleton](
      code: Code,
      fillings: Vector[Value[C]]
  )(using C): Value[C] =
    Value.extension(Suspension(code, fillings))

  def unapply[C <: NativeSpecializer & Singleton](value: Value[C])(using
      C
  ): Option[(Code, Vector[Value[C]])] =
    value.layer match
      case Suspension(code, fillings) => Some((code, fillings))
      case _                          => None

// TODO: deleted: `WeakHeadLayer`, the type `Value` as `Interned[WeakHeadLayer]` with no configuration, the extractors
// and untyped constructions of `object Value`, and `opaqueInstruction`. Wrong because a value of no configuration
// could take the children of any; the value is `com.yang_bo.gezi.ir.Value[C]` with its typed constructions, the IR's extractors on
// it, and `NeutralValue` and `SuspensionValue` here; issue https://github.com/Atry/private-overlay/issues/2261, design
// v38, sections 1 and 6. Read it back with
// `git show 7669694cc:gezi/weakhead-core/src/main/scala/gezi/weakhead/Value.scala`.

/** A head of a closed term (weak_head.pl, HEADS): an abstraction, a thunk with
  * a hole; or a neutral value. Never a parallel or a choice: the evaluator
  * evaluates both sides of a parallel, and what it answers is a `ParallelSet`
  * of heads. A head is the layer of an interned value (`Head.Lambda` and
  * `Head.Neutral` make the canonical one), and its value is that value
  * (`value`).
  *
  * FIXME (2026-11-11): the evaluator's answers are by design a set of sets
  * https://github.com/Atry/private-overlay/issues/1949 of abstractions, and a
  * neutral value is no abstraction. It is here because the readers that open a
  * binder put a free variable in its place (`NormalForms.BoundVariable`, the
  * codecs of the module `weakhead`, the knowledge reading, the JIT's readers of
  * Scott data); a closed program has none. Each of those uses was reviewed and
  * kept, with its argument at its declaration: each stands for a bound variable
  * of the value read, which an open body cannot be read without. A use of a
  * neutral value is an exception the user assents to, and the user has not
  * replied to these.
  */
type Head[C <: NativeSpecializer & Singleton] = com.yang_bo.gezi.ir.Thunk[Value[C]] |
  Neutral[Value[C]]

/** The constructions and the parts of heads. */
object Head:

  /** A head that is a thunk with at least one hole, as a type. */
  type Lambda[C <: NativeSpecializer & Singleton] = com.yang_bo.gezi.ir.Thunk[Value[C]]

  /** A head that is a neutral value, as a type. */
  type Neutral[C <: NativeSpecializer & Singleton] =
    com.yang_bo.gezi.weakhead.Neutral[Value[C]]

  /** The value of a head that is a thunk: the same object. */
  def lambdaValue[C <: NativeSpecializer & Singleton](
      thunk: com.yang_bo.gezi.ir.Thunk[Value[C]]
  )(using C): Value[C] = Value.ofHeadLayer(thunk)

  /** A thunk with at least one hole, the layer of its canonical value, built
    * through the specializer.
    */
  object Lambda:
    def apply[C <: NativeSpecializer & Singleton](
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Value[C]]
    )(using
        specializer: C
    ): Head[C] =
      Value.thunkLayer(specializer)(
        code,
        com.yang_bo.gezi.ir.NonEmptyHoles
          .of(holes)
          .getOrElse(
            throw IllegalArgumentException(
              s"a head of no hole, a suspension: $code"
            )
          ),
        fillings
      )

    def unapply[C <: NativeSpecializer & Singleton](head: Head[C])(using
        C
    ): Option[(Code, Vector[Hole], Vector[Value[C]])] =
      head match
        case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
          Some((code, holes, fillings))
        case _ => None

  /** A neutral value, the layer of its canonical value. */
  object Neutral:
    def apply[C <: NativeSpecializer & Singleton](
        variable: NeutralVariable,
        arguments: Vector[Value[C]]
    )(using C): Head[C] =
      com.yang_bo.gezi.weakhead.Neutral(variable, arguments)

    def unapply[C <: NativeSpecializer & Singleton](head: Head[C])(using
        C
    ): Option[(NeutralVariable, Vector[Value[C]])] =
      head match
        case com.yang_bo.gezi.weakhead.Neutral(variable, arguments) =>
          Some((variable, arguments))
        case _ => None

/** The parallel of a set of heads: one answer of the evaluator. The value of a
  * closed term under the weak head is a set of these, the choice of its
  * members, each member the parallel of its heads, a set without duplicates,
  * the parallel inside not reduced: a disjunctive normal form, the choice
  * outside and the parallel inside.
  *
  * A SET, because the parallel is idempotent, commutative and associative (M ∥
  * M = M, equations (3) and (4) of `CONTRIBUTING.md`, "Terms"): two parallel
  * sets are equal when they hold the same heads, in whatever order they were
  * found. Heads are compared as `Head` compares them, by their spelling, so two
  * spellings of one abstraction are two heads; that keeps a head more, never a
  * head less. The heads are not combined further: `{λx. A, λx. B}` is not
  * rewritten to `λx. (A ∥ B)`.
  *
  * THE EMPTY SET is the parallel of nothing, the least term of the contextual
  * preorder ⊑_O, a term such as Ω that has no head: it is below every term, so
  * every answer is its answer. Only an evaluation that knows such terms answers
  * it (`KnownExtremes`). The choice of nothing, no parallel set at all, is the
  * greatest term of ⊑_O, a term such as top: no answer.
  *
  * A SMALL SET IS SCANNED. A head holds its hash code, computed when it was
  * made (`com.yang_bo.gezi.ir.ConstructorIdentity`), but every parallel of two sets makes a
  * new set, whose hashed set would be built again; a set of at most
  * `scannedSize` heads is therefore searched by equality, head by head, which
  * compares the held hash codes first, and only a larger one by a hashed set.
  *
  * @param heads
  *   the heads, each once, in the order first found: a function of the
  *   computation, never of hash codes
  */
final class ParallelSet[C <: NativeSpecializer & Singleton] private (
    val heads: Vector[Head[C]]
):

  /** The heads as a hashed set, made when a set larger than `scannedSize` is
    * first searched.
    */
  private lazy val members: Set[Head[C]] = heads.toSet

  /** Whether the set is empty: the least term, below every term. */
  def isBottom: Boolean = heads.isEmpty

  /** Whether the head is one of the set's. */
  def holds(head: Head[C]): Boolean =
    if heads.size <= ParallelSet.scannedSize then scannedFrom(0, head)
    else members.contains(head)

  /** Whether the head is one of the heads from the index on, scanned by index:
    * `Vector.contains` makes an iterator at each call, and the tabled reader
    * asks at every parallel set it adds (JFR, 2026-11-19: vector iterators were
    * 11.6% of the bytes the knowledge reading allocates).
    */
  @scala.annotation.tailrec
  private def scannedFrom(index: Int, head: Head[C]): Boolean =
    index < heads.size && (heads(index) == head || scannedFrom(index + 1, head))

  /** Whether every head of the other set is one of this set's, scanned by index
    * as `holds` scans.
    */
  def holdsAll(other: ParallelSet[C]): Boolean =
    @scala.annotation.tailrec
    def from(index: Int): Boolean = index >= other.heads.size || (holds(
      other.heads(index)
    ) && from(index + 1))
    from(0)

  /** The parallel of this set and the other: the heads of both. */
  def parallel(other: ParallelSet[C]): ParallelSet[C] =
    if heads.isEmpty then other
    else
      val added = other.heads.filterNot(holds)
      if added.isEmpty then this else ParallelSet(heads ++ added)

  /** How an observer that reads the sides of a parallel sees the set, the
    * parallel of the others built through the reading's specializer.
    */
  def view(specializer: C): ParallelView[C] =
    given C = specializer
    heads match
      case Vector()                  => ParallelView.Bottom()
      case Vector(single)            => ParallelView.Single(single)
      case first +: (middle :+ last) =>
        ParallelView.Several(
          first.value,
          ParallelSet.sidesValue(specializer)(middle, last)
        )
      case others =>
        throw IllegalStateException(
          s"a vector of two or more heads has a first and a last head, but ${others.size} heads matched none"
        )

  /** The set as a value: its head's value, or the parallel of its heads' values
    * nested to the right; nothing for the empty set, which no value spells.
    */
  def value(specializer: C): Option[Value[C]] = heads match
    case earlier :+ last =>
      Some(ParallelSet.sidesValue(specializer)(earlier, last))
    case _ => None

  override def equals(other: Any): Boolean = other match
    // The other set's configuration is not known here; its heads are compared as objects, a set holding a head of
    // another configuration holding a different object.
    case that: ParallelSet[?] =>
      heads.size == that.heads.size && that.heads.forall(head =>
        if heads.size <= ParallelSet.scannedSize then heads.contains(head)
        else members.asInstanceOf[Set[Any]].contains(head)
      )
    case _ => false

  /** The hash of the heads whatever their order, computed once: a parallel set
    * is a table's answer, hashed at every lookup of the answers found.
    */
  override lazy val hashCode: Int =
    scala.util.hashing.MurmurHash3.unorderedHash(heads, ParallelSet.hashSeed)

  override def toString: String = heads.mkString("ParallelSet(", ", ", ")")

/** The constructions of parallel sets. */
object ParallelSet:

  /** The most heads of a set that is searched by equality, head by head (A
    * SMALL SET IS SCANNED). A choice: a parallel set of a program is a handful
    * of heads, and a scan of sixteen is cheaper than building a hashed set for
    * each new set.
    */
  val scannedSize: Int = 16

  private val hashSeed: Int = "ParallelSet".hashCode

  /** The empty set, the least term. */
  def bottom[C <: NativeSpecializer & Singleton](using C): ParallelSet[C] =
    ParallelSet(Vector.empty)

  /** The set of one head. */
  def single[C <: NativeSpecializer & Singleton](head: Head[C])(using
      C
  ): ParallelSet[C] = ParallelSet(Vector(head))

  /** The set of the heads, each kept once, in the order given. */
  def of[C <: NativeSpecializer & Singleton](
      heads: Vector[Head[C]]
  )(using C): ParallelSet[C] =
    heads.foldLeft(bottom[C])((set, head) =>
      if set.holds(head) then set else ParallelSet(set.heads :+ head)
    )

  /** The parallel of the earlier heads' values and the last one's, nested to
    * the right, built through the reading's specializer: a parallel of closed
    * values is specialized there as any other.
    */
  private def sidesValue[C <: NativeSpecializer & Singleton](
      specializer: C
  )(earlier: Vector[Head[C]], last: Head[C]): Value[C] =
    given C = specializer
    earlier.foldRight(last.value)((head, right) =>
      Value.parallel(specializer)(head.value, right)
    )

/** A parallel set as an observer that reads a parallel side by side sees it
  * (`ParallelSet.view`).
  */
enum ParallelView[C <: NativeSpecializer & Singleton]:

  /** The empty set: the least term, of which every answer is an answer. */
  case Bottom()

  /** One head. */
  case Single(head: Head[C])

  /** Two heads or more: the first head as a value, and the parallel of the
    * others as a value, whose heads the evaluator gives again when asked.
    */
  case Several(left: Value[C], right: Value[C])

/** A value the evaluator cannot evaluate or a reader cannot read, the Prolog
  * evaluator's `lambda_error(Reason)`. The message names the reason's kind
  * only: a reason may hold a value thousands of levels deep.
  */
final case class EvaluationError(reason: EvaluationErrorReason)
    extends RuntimeException:
  override def getMessage: String = s"lambda_error(${reason.productPrefix})"

/** Why the evaluator or a reader throws. */
enum EvaluationErrorReason:

  /** A code reads a slot its instance's fillings do not reach: the slot and the
    * number of fillings.
    */
  case SlotWithoutValue(slot: Int, fillingCount: Int)

  /** A normal-form reader met a neutral value that no binder of its reading
    * opened: the variable and the reading's depth.
    */
  case NeutralValueNotOpened(variable: NeutralVariable, depth: Int)

  /** A normal form read at depth 0 is not a closed thunk. */
  case OpenNormalForm

  /** A filling of an inner thunk of an open normal form is neither a neutral
    * leaf nor a closed thunk.
    */
  case NotAnOpenNormalFormFilling

  /** A witness that is no neutral value without arguments. */
  case NotAWitness(witness: Interned[ValueLayer])

  /** A budget in seconds that is not positive. */
  case NotABudget(seconds: Double)

  /** A codec's constructor is bound to no define, or to more than one: the
    * constructor and the defines bound.
    */
  case CodecConstructor(constructor: String, instructions: Vector[com.yang_bo.gezi.ir.Pure])
