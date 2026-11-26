package gezi.jit

import gezi.weakhead.ListRepresentation
import gezi.weakhead.ListTail
import gezi.weakhead.Mode
import gezi.weakhead.Neutral
import gezi.weakhead.NeutralVariable
import gezi.strategies.DispatchDecision
import gezi.strategies.DispatchStrategy
import gezi.ir.Code
import gezi.ir.ConstructorIdentity
import gezi.ir.Instruction
import gezi.ir.Interned
import gezi.ir.Interned.Interned
import gezi.ir.Hole

/** A representation of the backend (jit.pl, THE BACKEND'S
  * REPRESENTATIONS): the values of a data family of the backend's
  * `NativeBackend`, named by the family's identity (`FamilyIdentity`), at a parameter when the
  * family takes one, or the lists of one element
  * filter as host vectors (list(Key) in the Prolog JIT, Key the element
  * filter's instruction; here the element filter itself, an interned value),
  * the framework's own family `list`. Equal by its cases' fields.
  */
enum Representation:
  case Data(family: FamilyIdentity, parameter: Option[NativeValue])
  case ListOf(element: JitValue)

  /** The identity of the family the representation belongs to. */
  def familyIdentity: FamilyIdentity = this match
    case Data(family, _) => family
    case ListOf(_)       => Representation.listFamily

/** The framework's family of lists and the standard set's two data
  * families' representations.
  */
object Representation:

  /** The framework's family of lists, a codec named `list`. */
  val listFamily: FamilyIdentity.Codec = FamilyIdentity.Codec("list")

  /** The representation of the standard set's naturals. */
  val BigInteger: Representation = Data(BigIntegerFamily.identity, None)

  /** The representation of the standard set's booleans. */
  val Truth: Representation = Data(BooleanFamily.identity, None)

/** A value of a representation, held as its family chooses: the standard
  * set's natural as a `BigInt` and boolean as a `Boolean`, the framework's
  * list as `ListRepresentation` over the JIT's run-time values (its items
  * kept unevaluated, a cell's tail unread), and a value of a data family a
  * backend adds as a class of its own that extends this trait. Equality is
  * the class's.
  */
trait NativeValue

/** The values of the standard set's families and of the framework's lists. */
object NativeValue:

  /** A natural of the family `big_integer`. */
  final case class Natural(value: BigInt) extends NativeValue

  /** A boolean of the family `boolean`. */
  final case class Truth(value: Boolean) extends NativeValue

  /** A list of the framework's family `list`. */
  final case class Listed(list: ListRepresentation[JitValue]) extends NativeValue

  /** A value of a data family declared by facts with `jvm_type(generic)`
    * (`DeclaredFamily`): the family's identity, its constructor's index in
    * the order of the cases, and the values of its fields.
    */
  final case class Constructed(family: FamilyIdentity, constructor: Int, fields: Vector[NativeValue]) extends NativeValue

  /** The parameters of a data family declared by facts whose parameters are
    * criteria: the representation each criterion of its filter
    * `C @ P1 @ … @ Pk` names, in order, read from the filter as written.
    */
  final case class CriterionParameters(criteria: Vector[Representation]) extends NativeValue

  /** A field of the family `unread` (`UnreadFamily`), the term as it is
    * written, unevaluated. It stands only in the fields of another family's
    * value: a head is never a value of `unread`.
    */
  final case class Unread(term: JitValue) extends NativeValue

/** The value a native takes or gives at one place of its calling convention
  * (jit.pl, THE NATIVE'S REPRESENTATIONS): a value of a representation; a
  * list's item, a run-time value kept as given; or a list's tail, a list of
  * the representation or a term nothing has read.
  */
enum NativeArgument:
  case Represented(value: NativeValue)
  case Item(item: JitValue)
  case Tail(tail: ListTail[JitValue])

/** `represented(Representation, Value)`: the value of the representation,
  * standing for the term it encodes; its own head.
  */
final case class Represented(representation: Representation, value: NativeValue):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** `evaluated(Written, Mode, Heads)`: the operand of a fallback point as
  * written, holding no `Evaluated` value, the dispatch mode its check read
  * under and the heads the check found (jit.pl, THE CHECK'S EVALUATION IS
  * PASSED ON); its heads under that mode are those heads, under any other
  * those of the written operand.
  */
final case class Evaluated[+Child](written: Child, mode: DispatchMode, heads: Vector[JitHead]):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** A cell over the value (`JitRules.shared`): the instance of
  * `JitRules.cellCode` under the one filling, whose heads the instance table
  * keeps, so that a value an instance reads more than once is read once. The
  * JIT's own constructor, not the IR's thunk it stands for: a value that
  * holds a cell is no instruction, so the readbacks walk into it and take the
  * cell off (`JitValues.plain`), where an instruction is a leaf.
  */
final case class Cell[+Child](inner: Child):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The choice of no member, which a typed outcome of no value gives
  * (`JitRules.oneOrChoice`): no head when evaluated, and top, the term of no
  * answer, when read back (`JitValues.plain`). The JIT's own constructor: the
  * IR has no empty choice, and top evaluated by the JIT reads a lambda head,
  * not none.
  */
case object EmptyChoice

/** The empty parallel set: the head of a listed least term of ⊑_O, such as
  * Ω, under the reading's known extremes (`gezi.weakhead.KnownExtremes`),
  * whatever it is applied to, as the weak head's machines give it
  * (`WeakHead.knownExtreme`). The JIT's own head: a least term is not
  * evaluated, and no layer of a value gives this head.
  */
case object EmptyParallel

/** One layer of a run-time value of the JIT: the IR's own layers (`IrLayer`:
  * application, parallel, binary choice, thunk, URI node, opaque term), the
  * reference's neutral value, and the JIT's own four, a value of a
  * representation, the evaluation a fallback point's check passes on, a
  * cell and the choice of no member.
  * Every layer of the IR is one, so an instruction is a value of the JIT as
  * it is: one pool holds both, and a value the JIT builds that equals an
  * instruction by content is that instruction.
  */
type JitLayer[+Child] =
  gezi.ir.IrLayer[Child] | Neutral[Child] | Represented | Evaluated[Child] | Cell[Child] | EmptyChoice.type

/** A run-time value of the JIT (jit.pl, AN EVALUATOR OVER THE REFERENCE'S
  * VALUES): an interned term ([[gezi.ir.Interned]]) of `JitLayer`, every
  * value interned, as every IR term is.
  */
type JitValue = Interned[JitLayer]

/** The constructions and the parts of the JIT's values, each made through the
  * pool.
  */
object JitValue:

  private def of(layer: JitLayer[JitValue]): JitValue = Interned[JitLayer](layer)

  /** A value that is an instruction, a term of the IR's layers alone
    * (`ConstructorIdentity.isInstruction`, one field read), whoever built
    * it: the program's syntax, read one layer when reached (`Jit.layer`),
    * and the identity a native-bound library file's term is found by.
    */
  object Instruction:
    def unapply(value: JitValue): Option[gezi.ir.Instruction] =
      // Sound: one pool interns both, and a value made of the IR's
      // constructors only is an instruction.
      Option.when(ConstructorIdentity.isInstruction(value))(value.asInstanceOf[gezi.ir.Instruction])

  /** An application. */
  object Apply:
    def apply(function: JitValue, argument: JitValue): JitValue = of(gezi.ir.Apply(function, argument))

    def unapply(value: JitValue): Option[(JitValue, JitValue)] = value.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** The parallel of two sides. */
  object Parallel:
    def apply(left: JitValue, right: JitValue): JitValue = of(gezi.ir.Parallel(left, right))

    def unapply(value: JitValue): Option[(JitValue, JitValue)] = value.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** The choice of the members, in order: the IR's binary choice, a chain of
    * several nested to the right (`gezi.ir.ChoiceSpine`), so that its
    * heads are its members' heads in order. A choice's parts are its two
    * sides, not the chain flattened: a fallback point `v + (v ∥ c)` that is
    * the right side of another choice is a node of its own, read when that
    * side is read (`fallbackMembers` reads two parts). A choice of one
    * member is that member, whose heads are the choice's; a choice of none
    * is [[EmptyChoice]], whose parts are none.
    */
  object Choice:
    def apply(members: Vector[JitValue]): JitValue = members match
      case Vector()       => of(EmptyChoice)
      case Vector(member) => member
      case _              => members.init.foldRight(members.last)((member, rest) => of(gezi.ir.Choice(member, rest)))

    def unapply(value: JitValue): Option[Vector[JitValue]] = value.layer match
      case gezi.ir.Choice(left, right) => Some(Vector(left, right))
      case EmptyChoice                      => Some(Vector.empty)
      case _                                => None

  /** A lambda chain: its code, the holes still to be applied, the fillings. */
  object Thunk:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[JitValue]): JitValue =
      of(gezi.ir.Thunk(code, holes, fillings))

    def unapply(value: JitValue): Option[(Code, Vector[Hole], Vector[JitValue])] = value.layer match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

  /** The free variable applied to the arguments. */
  object Neutral:
    def apply(variable: NeutralVariable, arguments: Vector[JitValue]): JitValue =
      of(gezi.weakhead.Neutral(variable, arguments))

    def unapply(value: JitValue): Option[(NeutralVariable, Vector[JitValue])] = value.layer match
      case gezi.weakhead.Neutral(variable, arguments) => Some((variable, arguments))
      case _                                               => None

  /** A value of a representation, its own head. */
  object Represented:
    def apply(representation: Representation, value: NativeValue): JitValue =
      of(gezi.jit.Represented(representation, value))

    def unapply(value: JitValue): Option[(Representation, NativeValue)] = value.layer match
      case gezi.jit.Represented(representation, native) => Some((representation, native))
      case _                                                 => None

  /** The evaluation a fallback point's check passes on. */
  object Evaluated:
    def apply(written: JitValue, mode: DispatchMode, heads: Vector[JitHead]): JitValue =
      of(gezi.jit.Evaluated(written, mode, heads))

    def unapply(value: JitValue): Option[(JitValue, DispatchMode, Vector[JitHead])] = value.layer match
      case gezi.jit.Evaluated(written, mode, heads) => Some((written, mode, heads))
      case _                                             => None

  /** A cell over the value ([[gezi.jit.Cell]]). */
  object Cell:
    def apply(inner: JitValue): JitValue = of(gezi.jit.Cell(inner))

    def unapply(value: JitValue): Option[JitValue] = value.layer match
      case gezi.jit.Cell(inner) => Some(inner)
      case _                         => None

/** A native of the backend's `NativeBackend`, bound to a define: its name
  * and the number of its parameters.
  */
final case class BoundNative(name: NativeName, parameterCount: Int)

/** `native_application(Handle, Predicate, Missing, Arguments)`: the head of
  * the define at the instruction, bound to the native of at least one parameter,
  * with the arguments so far and the number still missing; never a value.
  */
final case class NativeApplication(instruction: Instruction, native: BoundNative, missing: Int, arguments: Vector[JitValue]):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** `elimination(Representation, Value, Cases)`: the represented value
  * applied to fewer arguments than its codec takes before it chooses a
  * branch; never a value.
  */
final case class Elimination(representation: Representation, value: NativeValue, cases: Vector[JitValue]):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** A head of the JIT (jit.pl's heads): the reference's kinds (a lambda, a
  * neutral value and a parallel), each the layer of an interned value, and
  * the JIT's own: a represented value, a native's define taken before its
  * parameters are all there, and a represented value applied to fewer
  * arguments than its codec takes. Equal by content.
  */
type JitHead =
  gezi.ir.Thunk[JitValue] | Neutral[JitValue] | gezi.ir.Parallel[JitValue] | Represented | NativeApplication |
    Elimination | EmptyParallel.type

/** The constructions and the parts of the JIT's heads. */
object JitHead:

  /** A thunk with at least one hole. */
  object Lambda:
    def apply(code: Code, holes: Vector[Hole], fillings: Vector[JitValue]): JitHead =
      gezi.ir.Thunk(code, holes, fillings)

    def unapply(head: JitHead): Option[(Code, Vector[Hole], Vector[JitValue])] = head match
      case gezi.ir.Thunk(code, holes, fillings) => Some((code, holes, fillings))
      case _                                        => None

  /** A neutral value. */
  object Neutral:
    def apply(variable: NeutralVariable, arguments: Vector[JitValue]): JitHead =
      gezi.weakhead.Neutral(variable, arguments)

    def unapply(head: JitHead): Option[(NeutralVariable, Vector[JitValue])] = head match
      case gezi.weakhead.Neutral(variable, arguments) => Some((variable, arguments))
      case _                                               => None

  /** A parallel, its sides not evaluated. */
  object Parallel:
    def apply(left: JitValue, right: JitValue): JitHead = gezi.ir.Parallel(left, right)

    def unapply(head: JitHead): Option[(JitValue, JitValue)] = head match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** A value of a representation, its own head. */
  object Represented:
    def apply(representation: Representation, value: NativeValue): JitHead =
      gezi.jit.Represented(representation, value)

    def unapply(head: JitHead): Option[(Representation, NativeValue)] = head match
      case gezi.jit.Represented(representation, value) => Some((representation, value))
      case _                                                => None

  /** The head of a bound define, its parameters not all there. */
  object NativeApplication:
    def apply(instruction: Instruction, native: BoundNative, missing: Int, arguments: Vector[JitValue]): JitHead =
      gezi.jit.NativeApplication(instruction, native, missing, arguments)

    def unapply(head: JitHead): Option[(Instruction, BoundNative, Int, Vector[JitValue])] = head match
      case gezi.jit.NativeApplication(instruction, native, missing, arguments) => Some((instruction, native, missing, arguments))
      case _                                                                  => None

  /** A represented value applied to fewer arguments than its codec takes. */
  object Elimination:
    def apply(representation: Representation, value: NativeValue, cases: Vector[JitValue]): JitHead =
      gezi.jit.Elimination(representation, value, cases)

    def unapply(head: JitHead): Option[(Representation, NativeValue, Vector[JitValue])] = head match
      case gezi.jit.Elimination(representation, value, cases) => Some((representation, value, cases))
      case _                                                       => None

/** The operations of a JIT head (`JitHead`), as extensions in the companion
  * of [[NativeApplication]], a constructor of that union alone, which puts
  * them in its implicit scope.
  */
object NativeApplication:

  extension (head: JitHead)
    /** The head as a run-time value. Throws `IllegalStateException` for the
      * two heads that are never values.
      */
    def asValue: JitValue = head match
      case thunk @ gezi.ir.Thunk(_, _, _)           => Interned[JitLayer](thunk)
      case neutral @ gezi.weakhead.Neutral(_, _)    => Interned[JitLayer](neutral)
      case parallel @ gezi.ir.Parallel(_, _)        => Interned[JitLayer](parallel)
      case represented @ gezi.jit.Represented(_, _) => Interned[JitLayer](represented)
      case other => throw IllegalStateException(s"the head ${other.productPrefix} is never a value")

/** The mode the JIT evaluates under (jit.pl's `jit_dispatch_set/1`): none,
  * which reads as a strategy deciding `untyped`, or a dispatch strategy
  * chosen when the program was compiled (jit.pl, DISPATCH STRATEGIES): a
  * value of `gezi.strategies.DispatchStrategy` that baseline or entry
  * code gives, with its decision at a fallback point whose check does not
  * hold, `Untyped` running the untyped path and `Rejected` throwing
  * `TypedVersionDomain`. This module names no strategy.
  */
enum DispatchMode:
  case NoDispatch
  case Dispatch(strategy: DispatchStrategy)

  /** The decision at a fallback point whose check does not hold. */
  def outsideDecided: DispatchDecision = this match
    case NoDispatch         => DispatchDecision.Untyped
    case Dispatch(strategy) => strategy.outsideDecided

/** A fallback point's check under a strategy deciding `rejected` found its
  * operand outside the typed version's domain (the Prolog JIT's
  * `error(domain_error(typed_version_domains([R]), Written), _)`): the
  * representation and the operand as written. The message names the
  * representation only, the operand may be deep.
  */
final case class TypedVersionDomain(representation: Representation, written: JitValue)
    extends RuntimeException:
  override def getMessage: String = s"typed_version_domains([${representation.familyIdentity.shown}])"

/** A value of the JIT's own carried through the terms a reader builds from
  * the JIT's heads (a filling of a lambda head, an argument of a neutral
  * head, a side of a parallel head): an opaque leaf that the reader hands
  * back to the JIT whole, inside a term whose heads it asks for, and that
  * the JIT reads as the value it carries. It is no free variable: the JIT
  * takes it apart before it evaluates anything, so a reader never meets it
  * as a head (a normal-form reader would throw `NeutralValueNotOpened` on
  * it). The Prolog JIT's run-time values sat in the reader's terms as they
  * are, Prolog terms being an open universe; `gezi.weakhead.Value` is
  * closed, and its one open kind is the neutral variable, which a reader
  * never looks inside.
  *
  * It answers whether it stands for a closed term (`closedLeaf`), which only
  * the JIT can tell: the carried value may hold a variable the reader
  * opened (the filling of λy. x y holds x), or be top (the filling of
  * λx. top ∥ x, top's head), which the normal-form reader must see as closed to
  * read top's body as ∅ (`NormalForms`, the rule of a closed head beside an
  * opened variable).
  *
  * A neutral value by its type only, kept as an exception argued here:
  * it stands for no
  * binder and no name, so it is not the neutral value that is rejected
  * (`CONTRIBUTING.md`, "Types live only in the term"), the variable a reader puts in place of a binder
  * it opens.
  */
final case class JitCarried(value: JitValue) extends NeutralVariable:

  /** Whether the carried value holds no neutral value other than a leaf
    * that itself stands for a closed term, and no value of a representation,
    * walked as a tree within `JitCarried.closedWalkLimit` values; false
    * where the walk does not decide (the limit spent, a represented value),
    * never true by default.
    */
  override lazy val closedLeaf: Boolean = JitCarried.closed(List(value), JitCarried.closedWalkLimit)

object JitCarried:

  /** The most values the walk of `closedLeaf` takes before it answers false:
    * the normal-form reader's own limit for a plain value
    * (`NormalForms.closedWalkLimit`, 4,096), so that a carried value is
    * walked as far as the same value held plain would be. top carried, the
    * filling of its head λx. top ∥ x, is 5 values (an application of two
    * thunks, each with one filling of no filling; counted from the JIT's
    * head of top as a probe printed it, 2026-11-13).
    */
  val closedWalkLimit: Int = 4096

  @scala.annotation.tailrec
  private def closed(pending: List[JitValue], remaining: Int): Boolean =
    pending match
      case Nil                 => true
      case _ if remaining <= 0 => false
      case value :: rest =>
        value match
          case JitValue.Instruction(_)              => closed(rest, remaining - 1)
          case JitValue.Apply(function, argument)   => closed(function :: argument :: rest, remaining - 1)
          case JitValue.Parallel(left, right)       => closed(left :: right :: rest, remaining - 1)
          case JitValue.Choice(members)             => closed(members.toList ::: rest, remaining - 1)
          case JitValue.Thunk(_, _, fillings)       => closed(fillings.toList ::: rest, remaining - 1)
          case JitValue.Evaluated(written, _, _)    => closed(written :: rest, remaining - 1)
          case JitValue.Cell(inner)                 => closed(inner :: rest, remaining - 1)
          case JitValue.Neutral(variable, arguments) =>
            if arguments.isEmpty && variable.closedLeaf then closed(rest, remaining - 1) else false
          case JitValue.Represented(_, _) => false
