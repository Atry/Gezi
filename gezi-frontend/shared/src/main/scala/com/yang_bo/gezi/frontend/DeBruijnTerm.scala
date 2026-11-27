package com.yang_bo.gezi.frontend

import com.yang_bo.gezi.ir.ConstructorIdentity
import com.yang_bo.gezi.ir.InternedConstructor
import com.yang_bo.gezi.ir.Instruction
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.Interned.Interned
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A term of the front end with de Bruijn indices, the Prolog front end's
  * `variable/1`, `lambda/1`, `apply/2`, `constant/1`, `choice/1` and
  * `parallel/2`. Every written form of the object language (the Scala HOAS of
  * `Term`, lambdalattice text) is translated to it, and `Defunctionalization`
  * translates it to the IR; nothing after the front end sees it
  * (`CONTRIBUTING.md`, "Types live only in the term").
  *
  * The term is locally nameless: a variable an abstraction of the term binds is
  * a de Bruijn index (`Variable`), and a name no abstraction of the term binds
  * is that name (`Free`) (J. McKinna and R. Pollack, "Some Lambda Calculus and
  * Type Theory Formalized", 1999; A. Charguéraud, "The Locally Nameless
  * Representation", 2012). A free name is rejected (`FreeNames`): no reading
  * and no conversion gives or takes one unless its call says so, lambdalattice
  * text by `FreeNames.Allowed`, the HOAS by `Term.locallyNamelessTerm`, the
  * conversion by the names given to `Defunctionalization.thunkInstruction`;
  * every other consumer of a term either handles `Free` or throws
  * `IllegalArgumentException` for it.
  *
  * Every term is interned ([[com.yang_bo.gezi.ir.Interned]]): two terms are one term
  * exactly when they are one object.
  */
type DeBruijnTerm = DeBruijnTermOf[Nothing]

/** A de Bruijn term whose constants are terms of type `ConstantTerm`, covariant
  * in it: a term with no constant (`DeBruijnTerm`, what every parser gives) is
  * a term whose constants are of any type, and a term whose constants are
  * `Configured[C]` is converted under the configuration `C` only
  * (`Defunctionalization.thunkInstruction`), so that no term of one
  * configuration enters another's through a constant.
  */
type DeBruijnTermOf[+ConstantTerm] =
  Interned[[Child] =>> DeBruijnLayer[ConstantTerm, Child]]

/** One layer of a de Bruijn term: a variable, an abstraction, the IR's
  * application, choice and parallel, a constant, a free name.
  */
type DeBruijnLayer[+ConstantTerm, +Child] =
  Variable | Lambda[Child] | com.yang_bo.gezi.ir.Apply[Child] | Constant[ConstantTerm] |
    Free | com.yang_bo.gezi.ir.Choice[Child] | com.yang_bo.gezi.ir.Parallel[Child]

/** A de Bruijn term's child is no term of the IR, so the IR's public
  * constructors build its layers.
  */
given [ConstantTerm]: com.yang_bo.gezi.ir.NotTerm[DeBruijnTermOf[ConstantTerm]] =
  com.yang_bo.gezi.ir.NotTerm.granted

/** The variable bound by the abstraction `index` levels out, 0 the innermost. A
  * negative index names no binder; the term is then not closed.
  */
final case class Variable private (index: Int) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

object Variable:
  /** The canonical Variable: a layer that no construction site converts is
    * interned when it is made.
    */
  def apply(index: Int): Variable = Interned.canonicalLayer(new Variable(index))

/** An abstraction. */
final case class Lambda[+Child] private (body: Child)
    extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

object Lambda:
  /** The canonical Lambda: a layer that no construction site converts is
    * interned when it is made.
    */
  def apply[Child](body: Child): Lambda[Child] =
    Interned.canonicalLayer(new Lambda(body))

/** A reference to a library name, or to an interned closed term: the
  * instruction of its layer.
  */
final case class Constant[+ConstantTerm] private (term: ConstantTerm)
    extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

object Constant:
  /** The canonical Constant: a layer that no construction site converts is
    * interned when it is made.
    */
  def apply[ConstantTerm](term: ConstantTerm): Constant[ConstantTerm] =
    Interned.canonicalLayer(new Constant(term))

/** A name no abstraction of the term binds, looked up by
  * `Defunctionalization.thunkInstruction` in the names it is given. A
  * blacklisted feature (`FreeNames`): no new code builds or reads one before
  * its design has been discussed.
  */
final case class Free private (name: String) extends InternedConstructor:
  override def toString: String = ConstructorIdentity.shown(this)

object Free:
  /** The canonical Free: a layer that no construction site converts is interned
    * when it is made.
    */
  def apply(name: String): Free = Interned.canonicalLayer(new Free(name))

/** The constructions and the parts of de Bruijn terms, each made through the
  * pool.
  */
object DeBruijnTerm:

  private def of[K](
      layer: DeBruijnLayer[K, DeBruijnTermOf[K]]
  ): DeBruijnTermOf[K] =
    Interned[[Child] =>> DeBruijnLayer[K, Child]](layer)

  /** Whether the term reads a variable bound by one of the `count` abstractions
    * right outside it.
    */
  private[frontend] def readsBelow[K](
      term: DeBruijnTermOf[K],
      count: Int
  ): Boolean =
    def reads(current: DeBruijnTermOf[K], depth: Int): TailRec[Boolean] =
      current match
        case DeBruijnTerm.Variable(index) =>
          done(index >= depth && index < depth + count)
        case DeBruijnTerm.Lambda(body)       => tailcall(reads(body, depth + 1))
        case DeBruijnTerm.Apply(left, right) =>
          tailcall(reads(left, depth)).flatMap(found =>
            if found then done(true) else tailcall(reads(right, depth))
          )
        case DeBruijnTerm.Choice(left, right) =>
          tailcall(reads(left, depth)).flatMap(found =>
            if found then done(true) else tailcall(reads(right, depth))
          )
        case DeBruijnTerm.Parallel(left, right) =>
          tailcall(reads(left, depth)).flatMap(found =>
            if found then done(true) else tailcall(reads(right, depth))
          )
        case _ => done(false)
    reads(term, 0).result

  /** The term with each variable bound outside the `count` abstractions right
    * outside it made `count` shallower, those abstractions removed: the body of
    * a partial function's literal as the reader reads it, which it shifts past
    * the bits (`Literals.partialFunction`). The term reads none of the `count`
    * abstractions' variables (`readsBelow`).
    */
  private[frontend] def shiftedDown[K](
      term: DeBruijnTermOf[K],
      count: Int
  ): DeBruijnTermOf[K] =
    def shifted(
        current: DeBruijnTermOf[K],
        depth: Int
    ): TailRec[DeBruijnTermOf[K]] = current match
      case DeBruijnTerm.Variable(index) =>
        done(if index >= depth then DeBruijnTerm.Variable[K](index - count)
        else current)
      case DeBruijnTerm.Lambda(body) =>
        tailcall(shifted(body, depth + 1)).map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Apply(left, right) =>
        for
          leftShifted <- tailcall(shifted(left, depth));
          rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Apply(leftShifted, rightShifted)
      case DeBruijnTerm.Choice(left, right) =>
        for
          leftShifted <- tailcall(shifted(left, depth));
          rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Choice(leftShifted, rightShifted)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          leftShifted <- tailcall(shifted(left, depth));
          rightShifted <- tailcall(shifted(right, depth))
        yield DeBruijnTerm.Parallel(leftShifted, rightShifted)
      case _ => done(current)
    shifted(term, 0).result

  /** The term with each constant mapped and every other layer as it is: each
    * shared node mapped once, by a work list in post order, so that a term of
    * any depth costs no frame of the JVM stack. What carries a term whose
    * constants are of one configuration into another (an adapter's cell, its
    * constants crossed into the entry's configuration).
    */
  def constantsMapped[K, L](
      term: DeBruijnTermOf[K],
      mapping: K => L
  ): DeBruijnTermOf[L] =
    def parts(node: DeBruijnTermOf[K]): List[DeBruijnTermOf[K]] = node match
      case DeBruijnTerm.Lambda(body)          => List(body)
      case DeBruijnTerm.Apply(left, right)    => List(left, right)
      case DeBruijnTerm.Choice(left, right)   => List(left, right)
      case DeBruijnTerm.Parallel(left, right) => List(left, right)
      case _                                  => Nil
    def rebuilt(
        node: DeBruijnTermOf[K],
        made: Map[DeBruijnTermOf[K], DeBruijnTermOf[L]]
    ): DeBruijnTermOf[L] = node match
      case DeBruijnTerm.Variable(index)    => DeBruijnTerm.Variable[L](index)
      case DeBruijnTerm.Lambda(body)       => DeBruijnTerm.Lambda(made(body))
      case DeBruijnTerm.Apply(left, right) =>
        DeBruijnTerm.Apply(made(left), made(right))
      case DeBruijnTerm.Choice(left, right) =>
        DeBruijnTerm.Choice(made(left), made(right))
      case DeBruijnTerm.Parallel(left, right) =>
        DeBruijnTerm.Parallel(made(left), made(right))
      case DeBruijnTerm.Constant(constant) =>
        DeBruijnTerm.Constant(mapping(constant))
      case DeBruijnTerm.Free(name) => DeBruijnTerm.Free[L](name)
      case other                   =>
        throw IllegalStateException(
          s"a de Bruijn term of no known layer: $other"
        )
    @scala.annotation.tailrec
    def mapped(
        pending: List[DeBruijnTermOf[K]],
        made: Map[DeBruijnTermOf[K], DeBruijnTermOf[L]]
    ): Map[DeBruijnTermOf[K], DeBruijnTermOf[L]] =
      pending match
        case Nil                                 => made
        case node :: rest if made.contains(node) => mapped(rest, made)
        case node :: rest                        =>
          parts(node).filterNot(made.contains) match
            case Nil => mapped(rest, made.updated(node, rebuilt(node, made)))
            case missing => mapped(missing ::: pending, made)
    mapped(List(term), Map.empty)(term)

  /** The variable bound by the abstraction `index` levels out. */
  object Variable:
    def apply[K](index: Int): DeBruijnTermOf[K] =
      of[K](com.yang_bo.gezi.frontend.Variable(index))

    def unapply[K](term: DeBruijnTermOf[K]): Option[Int] = term.layer match
      case com.yang_bo.gezi.frontend.Variable(index) => Some(index)
      case _                             => None

  /** An abstraction. */
  object Lambda:
    def apply[K](body: DeBruijnTermOf[K]): DeBruijnTermOf[K] =
      of[K](com.yang_bo.gezi.frontend.Lambda(body))

    def unapply[K](term: DeBruijnTermOf[K]): Option[DeBruijnTermOf[K]] =
      term.layer match
        case com.yang_bo.gezi.frontend.Lambda(body) => Some(body)
        case _                          => None

  /** An application. */
  object Apply:
    def apply[K](
        function: DeBruijnTermOf[K],
        argument: DeBruijnTermOf[K]
    ): DeBruijnTermOf[K] = of[K](com.yang_bo.gezi.ir.Apply(function, argument))

    def unapply[K](
        term: DeBruijnTermOf[K]
    ): Option[(DeBruijnTermOf[K], DeBruijnTermOf[K])] = term.layer match
      case com.yang_bo.gezi.ir.Apply(function, argument) => Some((function, argument))
      case _                                 => None

  /** A reference to a library name, or to an interned closed term. */
  object Constant:
    def apply[K](term: K): DeBruijnTermOf[K] =
      of[K](com.yang_bo.gezi.frontend.Constant(term))

    def unapply[K](term: DeBruijnTermOf[K]): Option[K] = term.layer match
      case com.yang_bo.gezi.frontend.Constant(constant) => Some(constant)
      case _                                => None

  /** A name no abstraction of the term binds (a blacklisted feature,
    * `FreeNames`).
    */
  object Free:
    def apply[K](name: String): DeBruijnTermOf[K] =
      of[K](com.yang_bo.gezi.frontend.Free(name))

    def unapply[K](term: DeBruijnTermOf[K]): Option[String] = term.layer match
      case com.yang_bo.gezi.frontend.Free(name) => Some(name)
      case _                        => None

  /** The binary choice; a chain of several members is right-nested, as in the
    * IR.
    */
  object Choice:
    def apply[K](
        left: DeBruijnTermOf[K],
        right: DeBruijnTermOf[K]
    ): DeBruijnTermOf[K] = of[K](com.yang_bo.gezi.ir.Choice(left, right))

    def unapply[K](
        term: DeBruijnTermOf[K]
    ): Option[(DeBruijnTermOf[K], DeBruijnTermOf[K])] = term.layer match
      case com.yang_bo.gezi.ir.Choice(left, right) => Some((left, right))
      case _                           => None

  /** The parallel of two sides. */
  object Parallel:
    def apply[K](
        left: DeBruijnTermOf[K],
        right: DeBruijnTermOf[K]
    ): DeBruijnTermOf[K] = of[K](com.yang_bo.gezi.ir.Parallel(left, right))

    def unapply[K](
        term: DeBruijnTermOf[K]
    ): Option[(DeBruijnTermOf[K], DeBruijnTermOf[K])] = term.layer match
      case com.yang_bo.gezi.ir.Parallel(left, right) => Some((left, right))
      case _                             => None

  /** The members of the term's right `+` spine
    * ([[com.yang_bo.gezi.ir.ChoiceSpine.members]]).
    */
  def choiceMembers[K](term: DeBruijnTermOf[K]): Vector[DeBruijnTermOf[K]] =
    com.yang_bo.gezi.ir.ChoiceSpine.members[DeBruijnTermOf[K]](term, Choice.unapply[K])

  /** The members nested to the right ([[com.yang_bo.gezi.ir.ChoiceSpine.nested]]); none
    * throws.
    */
  def nestedChoice[K](members: Vector[DeBruijnTermOf[K]]): DeBruijnTermOf[K] =
    com.yang_bo.gezi.ir.ChoiceSpine.nested[DeBruijnTermOf[K]](members, Choice[K](_, _))

  /** The term written out whole: each node's case name, its atom when it holds
    * one (a variable's index, a constant's instruction, a free name), and its
    * parts in order, `Lambda(Apply(Variable(0), Variable(0)))`, written without
    * recursion on the JVM stack (a derived `toString` overflowed it on a deep
    * generated term in an assertion's message, judge tests, 2026-10-31). A
    * term's own `toString` writes one layer
    * (`com.yang_bo.gezi.ir.ConstructorIdentity.shown`); this is the whole term, walked as a
    * tree.
    */
  def written[K](term: DeBruijnTermOf[K]): String =
    @scala.annotation.tailrec
    def rendered(
        pending: List[Either[String, DeBruijnTermOf[K]]],
        written: Vector[String]
    ): String =
      pending match
        case Nil                 => written.mkString
        case Left(text) :: rest  => rendered(rest, written :+ text)
        case Right(node) :: rest =>
          val (name, atom, parts) = node.layer match
            case com.yang_bo.gezi.frontend.Variable(index) =>
              ("Variable", Some(index.toString), Vector.empty)
            case com.yang_bo.gezi.frontend.Lambda(body) => ("Lambda", None, Vector(body))
            case com.yang_bo.gezi.ir.Apply(function, argument) =>
              ("Apply", None, Vector(function, argument))
            case com.yang_bo.gezi.frontend.Constant(constant) =>
              ("Constant", Some(constant.toString), Vector.empty)
            case com.yang_bo.gezi.frontend.Free(free) => ("Free", Some(free), Vector.empty)
            case com.yang_bo.gezi.ir.Choice(left, right) =>
              ("Choice", None, Vector(left, right))
            case com.yang_bo.gezi.ir.Parallel(left, right) =>
              ("Parallel", None, Vector(left, right))
          val shown: Vector[Either[String, DeBruijnTermOf[K]]] =
            atom.map(Left(_)).toVector ++ parts.map(Right(_))
          if shown.isEmpty then rendered(rest, written :+ name)
          else
            val separated = shown.head +: shown.tail.flatMap(piece =>
              Vector(Left(", "), piece)
            )
            rendered(
              (Left(name + "(") +: separated :+ Left(")")).toList ++ rest,
              written
            )
    rendered(List(Right(term)), Vector.empty)
