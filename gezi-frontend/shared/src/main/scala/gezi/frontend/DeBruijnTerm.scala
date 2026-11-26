package gezi.frontend

import gezi.ir.ConstructorIdentity
import gezi.ir.Instruction
import gezi.ir.Interned
import gezi.ir.Interned.Interned
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A term of the front end with de Bruijn indices, the Prolog front end's
  * `variable/1`, `lambda/1`, `apply/2`, `constant/1`, `choice/1` and
  * `parallel/2`. Every written form of the object language (the Scala HOAS
  * of `Term`, lambdalattice text) is
  * translated to it, and `Defunctionalization` translates it to the IR;
  * nothing after the front end sees it (`CONTRIBUTING.md`, "Types live only
  * in the term").
  *
  * The term is locally nameless: a variable an abstraction of the term binds
  * is a de Bruijn index (`Variable`), and a name no abstraction of the term
  * binds is that name (`Free`) (J. McKinna and R. Pollack, "Some Lambda
  * Calculus and Type Theory Formalized", 1999; A. Charguéraud, "The Locally
  * Nameless Representation", 2012). A free name is rejected
  * (`FreeNames`): no reading and no conversion gives
  * or takes one unless its call says so, lambdalattice text by
  * `FreeNames.Allowed`, the HOAS by `Term.locallyNamelessTerm`, the
  * conversion by the names given to `Defunctionalization.thunkInstruction`;
  * every other consumer of a term either handles `Free` or throws
  * `IllegalArgumentException` for it.
  *
  * Every term is interned ([[gezi.ir.Interned]]): two terms are one term
  * exactly when they are one object.
  */
type DeBruijnTerm = Interned[DeBruijnLayer]

/** One layer of a de Bruijn term: a variable, an abstraction, the IR's
  * application, choice and parallel, a constant, a free name.
  */
type DeBruijnLayer[+Child] =
  Variable | Lambda[Child] | gezi.ir.Apply[Child] | Constant | Free | gezi.ir.Choice[Child] |
    gezi.ir.Parallel[Child]

/** The variable bound by the abstraction `index` levels out, 0 the
  * innermost. A negative index names no binder; the term is then not closed.
  */
final case class Variable(index: Int):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** An abstraction. */
final case class Lambda[+Child](body: Child):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** A reference to a library name, or to an interned closed term: the instruction
  * of its layer.
  */
final case class Constant(instruction: Instruction):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** A name no abstraction of the term binds, looked up by
  * `Defunctionalization.thunkInstruction` in the names it is given. A
  * blacklisted feature (`FreeNames`): no new code builds or reads one before
  * its design has been discussed.
  */
final case class Free(name: String):
  override val hashCode: Int = ConstructorIdentity.hash(this)
  override def equals(other: Any): Boolean = ConstructorIdentity.equal(this, other)
  override def toString: String = ConstructorIdentity.shown(this)

/** The constructions and the parts of de Bruijn terms, each made through the
  * pool.
  */
object DeBruijnTerm:

  private def of(layer: DeBruijnLayer[DeBruijnTerm]): DeBruijnTerm = Interned[DeBruijnLayer](layer)

  /** Whether the term reads a variable bound by one of the `count`
    * abstractions right outside it.
    */
  private[frontend] def readsBelow(term: DeBruijnTerm, count: Int): Boolean =
    def reads(current: DeBruijnTerm, depth: Int): TailRec[Boolean] = current match
      case DeBruijnTerm.Variable(index) => done(index >= depth && index < depth + count)
      case DeBruijnTerm.Lambda(body)    => tailcall(reads(body, depth + 1))
      case DeBruijnTerm.Apply(left, right) =>
        tailcall(reads(left, depth)).flatMap(found => if found then done(true) else tailcall(reads(right, depth)))
      case DeBruijnTerm.Choice(left, right) =>
        tailcall(reads(left, depth)).flatMap(found => if found then done(true) else tailcall(reads(right, depth)))
      case DeBruijnTerm.Parallel(left, right) =>
        tailcall(reads(left, depth)).flatMap(found => if found then done(true) else tailcall(reads(right, depth)))
      case _ => done(false)
    reads(term, 0).result

  /** The term with each variable bound outside the `count` abstractions right
    * outside it made `count` shallower, those abstractions removed: the body
    * of a partial function's literal as the reader reads it, which it shifts
    * past the bits (`Literals.partialFunction`). The term reads none of the
    * `count` abstractions' variables (`readsBelow`).
    */
  private[frontend] def shiftedDown(term: DeBruijnTerm, count: Int): DeBruijnTerm =
    def shifted(current: DeBruijnTerm, depth: Int): TailRec[DeBruijnTerm] = current match
      case DeBruijnTerm.Variable(index) => done(if index >= depth then DeBruijnTerm.Variable(index - count) else current)
      case DeBruijnTerm.Lambda(body)    => tailcall(shifted(body, depth + 1)).map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Apply(left, right) =>
        for leftShifted <- tailcall(shifted(left, depth)); rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Apply(leftShifted, rightShifted)
      case DeBruijnTerm.Choice(left, right) =>
        for leftShifted <- tailcall(shifted(left, depth)); rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Choice(leftShifted, rightShifted)
      case DeBruijnTerm.Parallel(left, right) =>
        for leftShifted <- tailcall(shifted(left, depth)); rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Parallel(leftShifted, rightShifted)
      case _ => done(current)
    shifted(term, 0).result

  /** The variable bound by the abstraction `index` levels out. */
  object Variable:
    def apply(index: Int): DeBruijnTerm = of(gezi.frontend.Variable(index))

    def unapply(term: DeBruijnTerm): Option[Int] = term.layer match
      case gezi.frontend.Variable(index) => Some(index)
      case _                                  => None

  /** An abstraction. */
  object Lambda:
    def apply(body: DeBruijnTerm): DeBruijnTerm = of(gezi.frontend.Lambda(body))

    def unapply(term: DeBruijnTerm): Option[DeBruijnTerm] = term.layer match
      case gezi.frontend.Lambda(body) => Some(body)
      case _                               => None

  /** An application. */
  object Apply:
    def apply(function: DeBruijnTerm, argument: DeBruijnTerm): DeBruijnTerm = of(gezi.ir.Apply(function, argument))

    def unapply(term: DeBruijnTerm): Option[(DeBruijnTerm, DeBruijnTerm)] = term.layer match
      case gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                     => None

  /** A reference to a library name, or to an interned closed term. */
  object Constant:
    def apply(instruction: Instruction): DeBruijnTerm = of(gezi.frontend.Constant(instruction))

    def unapply(term: DeBruijnTerm): Option[Instruction] = term.layer match
      case gezi.frontend.Constant(instruction) => Some(instruction)
      case _                                   => None

  /** A name no abstraction of the term binds (a blacklisted feature,
    * `FreeNames`).
    */
  object Free:
    def apply(name: String): DeBruijnTerm = of(gezi.frontend.Free(name))

    def unapply(term: DeBruijnTerm): Option[String] = term.layer match
      case gezi.frontend.Free(name) => Some(name)
      case _                             => None

  /** The binary choice; a chain of several members is right-nested, as in
    * the IR.
    */
  object Choice:
    def apply(left: DeBruijnTerm, right: DeBruijnTerm): DeBruijnTerm = of(gezi.ir.Choice(left, right))

    def unapply(term: DeBruijnTerm): Option[(DeBruijnTerm, DeBruijnTerm)] = term.layer match
      case gezi.ir.Choice(left, right) => Some((left, right))
      case _                               => None

  /** The parallel of two sides. */
  object Parallel:
    def apply(left: DeBruijnTerm, right: DeBruijnTerm): DeBruijnTerm = of(gezi.ir.Parallel(left, right))

    def unapply(term: DeBruijnTerm): Option[(DeBruijnTerm, DeBruijnTerm)] = term.layer match
      case gezi.ir.Parallel(left, right) => Some((left, right))
      case _                                 => None

  /** The members of the term's right `+` spine
    * ([[gezi.ir.ChoiceSpine.members]]).
    */
  def choiceMembers(term: DeBruijnTerm): Vector[DeBruijnTerm] =
    gezi.ir.ChoiceSpine.members[DeBruijnTerm](term, Choice.unapply)

  /** The members nested to the right ([[gezi.ir.ChoiceSpine.nested]]);
    * none throws.
    */
  def nestedChoice(members: Vector[DeBruijnTerm]): DeBruijnTerm =
    gezi.ir.ChoiceSpine.nested[DeBruijnTerm](members, Choice(_, _))

  /** The term written out whole: each node's case name, its atom when it
    * holds one (a variable's index, a constant's instruction, a free name), and its
    * parts in order, `Lambda(Apply(Variable(0), Variable(0)))`, written
    * without recursion on the JVM stack (a derived `toString` overflowed it
    * on a deep generated term in an assertion's message, judge tests,
    * 2026-10-31). A term's own `toString` writes one layer
    * (`gezi.ir.ConstructorIdentity.shown`); this is the whole term,
    * walked as a tree.
    */
  def written(term: DeBruijnTerm): String =
    @scala.annotation.tailrec
    def rendered(pending: List[Either[String, DeBruijnTerm]], written: Vector[String]): String =
      pending match
        case Nil                => written.mkString
        case Left(text) :: rest => rendered(rest, written :+ text)
        case Right(node) :: rest =>
          val (name, atom, parts) = node.layer match
            case gezi.frontend.Variable(index)     => ("Variable", Some(index.toString), Vector.empty)
            case gezi.frontend.Lambda(body)        => ("Lambda", None, Vector(body))
            case gezi.ir.Apply(function, argument) => ("Apply", None, Vector(function, argument))
            case gezi.frontend.Constant(instruction)    => ("Constant", Some(instruction.toString), Vector.empty)
            case gezi.frontend.Free(free)          => ("Free", Some(free), Vector.empty)
            case gezi.ir.Choice(left, right)       => ("Choice", None, Vector(left, right))
            case gezi.ir.Parallel(left, right)     => ("Parallel", None, Vector(left, right))
          val shown: Vector[Either[String, DeBruijnTerm]] = atom.map(Left(_)).toVector ++ parts.map(Right(_))
          if shown.isEmpty then rendered(rest, written :+ name)
          else
            val separated = shown.head +: shown.tail.flatMap(piece => Vector(Left(", "), piece))
            rendered((Left(name + "(") +: separated :+ Left(")")).toList ++ rest, written)
    rendered(List(Right(term)), Vector.empty)
