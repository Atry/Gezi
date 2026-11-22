package gezi.weakhead

import gezi.ir.Code
import gezi.ir.ConstructorIdentity
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Interned
import gezi.ir.Interned.Interned
import gezi.ir.IrLayer
import gezi.ir.Opaque
import gezi.ir.UriNode

/** The variable of a neutral value: a value that the reader who makes the
  * neutral value chooses (a normal-form reader names its bound variables by
  * their depth, a codec its cases by its decoding), compared by `==`, so two
  * neutral values have the same variable exactly when their variables are
  * equal values. Each reader defines its own variables as case classes or
  * case objects of flat fields; the evaluator never looks inside one.
  */
trait NeutralVariable:

  /** Whether a neutral value of this variable applied to no argument stands
    * for a closed term, every read of which is closed: false unless the
    * reader that made the variable knows it to be such a leaf. The
    * normal-form reader asks it where it decides that a head is closed
    * (`NormalForms`, the rule of a closed head beside an opened variable).
    * Answering true for a leaf that holds an opened variable makes that rule
    * read ∅ where the set has reads; answering false only keeps the rule from
    * sparing the reading of the heads.
    */
  def closedLeaf: Boolean = false

/** The free variable applied to the arguments, a head nothing reduces: the
  * one constructor of the weak-head evaluator's own, beside the IR's. A
  * neutral value lives only in the evaluator and its readers: it is no layer
  * of the IR, of the e-graph or of the index (`CONTRIBUTING.md`, "Types live
  * only in the term").
  */
final case class Neutral[+Child](variable: NeutralVariable, arguments: Vector[Child]):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The operations of a head (`Head`), as extensions in the companion of
  * [[Neutral]], a constructor of the union, which puts them in its implicit
  * scope.
  */
object Neutral:

  extension (head: Head)
    /** The head as a value: the interned term whose layer it is. */
    def value: Value = Interned[WeakHeadLayer](head)

/** One layer of a run-time value of the weak-head evaluator: a layer of the
  * IR (an application, a parallel, a choice, a thunk, a URI node, an opaque
  * term) or a neutral value.
  */
type WeakHeadLayer[+Child] = IrLayer[Child] | Neutral[Child]

/** A run-time value of the weak-head evaluator: an interned term
  * ([[gezi.ir.Interned]]) over the IR's constructors and the neutral
  * value, every term interned, none supported uninterned. An instruction is a value as it is, with no
  * conversion: the IR's layers are among a value's. Two values are one term
  * exactly when they are one object. A thunk's code is a code: a body over
  * slots.
  */
type Value = Interned[WeakHeadLayer]

/** The constructions and the parts of values, each made through the pool. */
object Value:

  /** The canonical value of the layer. */
  def apply(layer: WeakHeadLayer[Value]): Value = Interned[WeakHeadLayer](layer)

  /** The canonical application, and its parts. */
  object Apply:
    def apply(function: Value, argument: Value): Value = Value(gezi.ir.Apply(function, argument))

    def unapply(value: Value): Option[(Value, Value)] = value.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** The canonical parallel of two sides, and its sides. */
  object Parallel:
    def apply(left: Value, right: Value): Value = Value(gezi.ir.Parallel(left, right))

    def unapply(value: Value): Option[(Value, Value)] = value.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** The canonical binary choice, as the IR's, and its two sides. */
  object Choice:
    def apply(left: Value, right: Value): Value = Value(gezi.ir.Choice(left, right))

    def unapply(value: Value): Option[(Value, Value)] = value.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                               => None

  /** A lambda chain: its code; the hole of each binder still to be applied,
    * in lambda order; and the values of the code's other slots, in slot
    * order. With no hole it is the instance of its code under its fillings.
    */
  object Thunk:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[Value]): Value =
      Value(gezi.ir.Thunk(code, holes, fillings))

    def unapply(value: Value): Option[(Code, Vector[Hole], Vector[Value])] = value.layer match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

  /** The free variable applied to the arguments. */
  object Neutral:
    def apply(variable: NeutralVariable, arguments: Vector[Value]): Value =
      Value(gezi.weakhead.Neutral(variable, arguments))

    def unapply(value: Value): Option[(NeutralVariable, Vector[Value])] = value.layer match
      case gezi.weakhead.Neutral(variable, arguments) => Some((variable, arguments))
      case _                                               => None

  /** The instruction a value whose layer is a URI node or an opaque term
    * is: such a layer has no part, so the interned object is an
    * instruction's (the cast is sound: one pool interns both, and a value
    * with no neutral value anywhere in it is an instruction); none for any
    * other value.
    */
  def opaqueInstruction(value: Value): Option[Instruction] = value.layer match
    case UriNode(_) | Opaque(_) => Some(value.asInstanceOf[Instruction])
    case _                      => None

/** A head of a closed term (weak_head.pl, HEADS): an abstraction, a thunk
  * with a hole; or a neutral value. Never a parallel or a choice: the
  * evaluator evaluates both sides of a parallel, and what it answers is a
  * `ParallelSet` of heads. A head is the layer of an interned value
  * (`Head.Lambda` and `Head.Neutral` make the canonical one), and its value is
  * that value (`value`).
  *
  * FIXME (2026-11-11): the evaluator's answers are by design a set of sets https://github.com/Atry/private-overlay/issues/1949
  * of abstractions, and a neutral value is no abstraction. It is here because
  * the readers that open a binder put a free variable in its place
  * (`NormalForms`, the codecs of the module `weakhead`, the knowledge
  * reading); a closed program has none. Whether those readers keep a free
  * variable or read another way is not settled.
  */
type Head = gezi.ir.Thunk[Value] | Neutral[Value]

/** The constructions and the parts of heads. */
object Head:

  /** A head that is a thunk with at least one hole, as a type. */
  type Lambda = gezi.ir.Thunk[Value]

  /** A head that is a neutral value, as a type. */
  type Neutral = gezi.weakhead.Neutral[Value]

  /** A thunk with at least one hole, the layer of its canonical value. */
  object Lambda:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[Value]): Head =
      Value.Thunk(code, holes, fillings).layer match
        case thunk @ gezi.ir.Thunk(_, _, _) => thunk
        case other => throw IllegalStateException(s"the pool gave $other for a thunk")

    def unapply(head: Head): Option[(Code, Vector[Hole], Vector[Value])] = head match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

  /** A neutral value, the layer of its canonical value. */
  object Neutral:
    def apply(variable: NeutralVariable, arguments: Vector[Value]): Head =
      Value.Neutral(variable, arguments).layer match
        case neutral @ gezi.weakhead.Neutral(_, _) => neutral
        case other => throw IllegalStateException(s"the pool gave $other for a neutral value")

    def unapply(head: Head): Option[(NeutralVariable, Vector[Value])] = head match
      case gezi.weakhead.Neutral(variable, arguments) => Some((variable, arguments))
      case _                                               => None

/** The parallel of a set of heads: one answer of the evaluator. The value of
  * a closed term under the weak head is a set of these, the choice of its
  * members, each member the parallel of its heads, a set without
  * duplicates, the parallel inside not reduced: a disjunctive normal form, the choice outside and the parallel inside.
  *
  * A SET, because the parallel is idempotent, commutative and associative
  * (M ∥ M = M, equations (3) and (4) of `CONTRIBUTING.md`, "Terms"): two parallel sets are
  * equal when they hold the same heads, in whatever order they were found.
  * Heads are compared as `Head` compares them, by their spelling, so two
  * spellings of one abstraction are two heads; that keeps a head more, never
  * a head less. The heads are not combined further: `{λx. A, λx. B}` is not
  * rewritten to `λx. (A ∥ B)`.
  *
  * THE EMPTY SET is the parallel of nothing, the least term of the
  * contextual preorder ⊑_O, a term such as Ω that has no head: it is below
  * every term, so every answer is its answer. Only an evaluation that knows
  * such terms answers it (`KnownExtremes`). The choice of nothing, no
  * parallel set at all, is the greatest term of ⊑_O, a term such as top: no
  * answer.
  *
  * A SMALL SET IS SCANNED. A head holds its hash code, computed when it was
  * made (`gezi.ir.ConstructorIdentity`), but every parallel of two sets
  * makes a new set, whose hashed set would be built again; a set of at most
  * `scannedSize` heads is therefore searched by equality, head by head,
  * which compares the held hash codes first, and only a larger one by a
  * hashed set.
  *
  * @param heads
  *   the heads, each once, in the order first found: a function of the
  *   computation, never of hash codes
  */
final class ParallelSet private (val heads: Vector[Head]):

  /** The heads as a hashed set, made when a set larger than `scannedSize`
    * is first searched.
    */
  private lazy val members: Set[Head] = heads.toSet

  /** Whether the set is empty: the least term, below every term. */
  def isBottom: Boolean = heads.isEmpty

  /** Whether the head is one of the set's. */
  def holds(head: Head): Boolean =
    if heads.size <= ParallelSet.scannedSize then scannedFrom(0, head) else members.contains(head)

  /** Whether the head is one of the heads from the index on, scanned by
    * index: `Vector.contains` makes an iterator at each call, and the tabled
    * reader asks at every parallel set it adds (JFR, 2026-11-19: vector
    * iterators were 11.6% of the bytes the knowledge reading allocates).
    */
  @scala.annotation.tailrec
  private def scannedFrom(index: Int, head: Head): Boolean =
    index < heads.size && (heads(index) == head || scannedFrom(index + 1, head))

  /** Whether every head of the other set is one of this set's, scanned by
    * index as `holds` scans.
    */
  def holdsAll(other: ParallelSet): Boolean =
    @scala.annotation.tailrec
    def from(index: Int): Boolean = index >= other.heads.size || (holds(other.heads(index)) && from(index + 1))
    from(0)

  /** The parallel of this set and the other: the heads of both. */
  def parallel(other: ParallelSet): ParallelSet =
    if heads.isEmpty then other
    else
      val added = other.heads.filterNot(holds)
      if added.isEmpty then this else ParallelSet(heads ++ added)

  /** How an observer that reads the sides of a parallel sees the set. */
  def view: ParallelView = heads match
    case Vector()       => ParallelView.Bottom
    case Vector(single) => ParallelView.Single(single)
    case first +: (middle :+ last) => ParallelView.Several(first.value, ParallelSet.sidesValue(middle, last))
    case others =>
      throw IllegalStateException(
        s"a vector of two or more heads has a first and a last head, but ${others.size} heads matched none"
      )

  /** The set as a value: its head's value, or the parallel of its heads'
    * values nested to the right; nothing for the empty set, which no value
    * spells.
    */
  def value: Option[Value] = heads match
    case earlier :+ last => Some(ParallelSet.sidesValue(earlier, last))
    case _               => None

  override def equals(other: Any): Boolean = other match
    case that: ParallelSet => heads.size == that.heads.size && holdsAll(that)
    case _                 => false

  /** The hash of the heads whatever their order, computed once: a parallel
    * set is a table's answer, hashed at every lookup of the answers found.
    */
  override lazy val hashCode: Int = scala.util.hashing.MurmurHash3.unorderedHash(heads, ParallelSet.hashSeed)

  override def toString: String = heads.mkString("ParallelSet(", ", ", ")")

/** The constructions of parallel sets. */
object ParallelSet:

  /** The most heads of a set that is searched by equality, head by head (A
    * SMALL SET IS SCANNED). A choice: a parallel set of a program is a
    * handful of heads, and a scan of sixteen is cheaper than building a
    * hashed set for each new set.
    */
  val scannedSize: Int = 16

  private val hashSeed: Int = "ParallelSet".hashCode

  /** The empty set, the least term. */
  val bottom: ParallelSet = ParallelSet(Vector.empty)

  /** The set of one head. */
  def single(head: Head): ParallelSet = ParallelSet(Vector(head))

  /** The set of the heads, each kept once, in the order given. */
  def of(heads: Vector[Head]): ParallelSet =
    heads.foldLeft(bottom)((set, head) => if set.holds(head) then set else ParallelSet(set.heads :+ head))

  /** The parallel of the values of the earlier heads and of the last one,
    * nested to the right.
    */
  private def sidesValue(earlier: Vector[Head], last: Head): Value =
    earlier.foldRight(last.value)((head, right) => Value.Parallel(head.value, right))

/** A parallel set as an observer that reads a parallel side by side sees it
  * (`ParallelSet.view`).
  */
enum ParallelView:

  /** The empty set: the least term, of which every answer is an answer. */
  case Bottom

  /** One head. */
  case Single(head: Head)

  /** Two heads or more: the first head as a value, and the parallel of the
    * others as a value, whose heads the evaluator gives again when asked.
    */
  case Several(left: Value, right: Value)

/** A value the evaluator cannot evaluate or a reader cannot read, the Prolog
  * evaluator's `lambda_error(Reason)`. The message names the reason's kind
  * only: a reason may hold a value thousands of levels deep.
  */
final case class EvaluationError(reason: EvaluationErrorReason)
    extends RuntimeException:
  override def getMessage: String = s"lambda_error(${reason.productPrefix})"

/** Why the evaluator or a reader throws. */
enum EvaluationErrorReason:

  /** A code reads a slot its instance's fillings do not reach: the slot and
    * the number of fillings.
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
  case NotAWitness(witness: Value)

  /** A budget in seconds that is not positive. */
  case NotABudget(seconds: Double)

  /** A codec's constructor is bound to no define, or to more than one: the
    * constructor and the defines bound.
    */
  case CodecConstructor(constructor: String, instructions: Vector[Instruction])
