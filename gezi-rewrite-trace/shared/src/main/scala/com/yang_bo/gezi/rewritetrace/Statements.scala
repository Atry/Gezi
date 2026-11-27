package com.yang_bo.gezi.rewritetrace

import scala.annotation.tailrec

import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.ir.BindingNormalForm
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir.NotTerm
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.StorageView
import com.yang_bo.gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** A side of an equation: a term with named variables over terms `Term` it
  * holds as they are (a lemma's closed fillings, the terms of an article). A
  * layer of a side is no term of the IR: a thunk of no hole is a side of the
  * body equation, which the article states and a replay never instantiates
  * (`Statements.instance` refuses it).
  */
enum StatementTerm[+Term]:
  case Variable(name: String)
  case Stored(term: Term)
  case Layered(layer: Layer[StatementTerm[Term]])

object StatementTerm:
  /** A side of an equation is no IR term. */
  given [Term]: NotTerm[StatementTerm[Term]] = NotTerm.granted

/** An equation `left = right` whose variables are universally quantified. */
final case class Statement[+Term](
    left: StatementTerm[Term],
    right: StatementTerm[Term]
):

  /** The variables, each once, in the order they first occur, left side first:
    * the order a command's bindings index (`TraceCommand.Rewrite`).
    */
  def variables: Vector[String] =
    (Statements.variables(left) ++ Statements.variables(right)).distinct

  /** The side a step in the direction replaces, and the side it puts there. */
  def oriented(
      direction: RewriteDirection
  ): (StatementTerm[Term], StatementTerm[Term]) = direction match
    case RewriteDirection.Forward  => (left, right)
    case RewriteDirection.Backward => (right, left)

  /** The provenance of the variables, in the order of `variables`, from the
    * left side to the right side. Each side is walked once for all its
    * variables (`Statements.occurrencesByName`): the β rule of a thunk of n
    * fillings has n variables, and walking the sides once for each made a step
    * of a program's top-level thunk cost n² (2,468 fillings on
    * `contest-entries-solo`'s repeated_library_hotspots calls_1000 point).
    */
  def provenance: Vector[Provenance] =
    val onLeft = Statements.occurrencesByName(left)
    val onRight = Statements.occurrencesByName(right)
    variables.map(name =>
      Provenance(
        name,
        onLeft.getOrElse(name, Vector.empty),
        onRight.getOrElse(name, Vector.empty)
      )
    )

/** The equations a step instantiates, stated as the article states them
  * (`com.yang_bo.gezi.proofs.ArticleStore.axiomStatement`, which reads them from here): the
  * numbered equations of the formal definition, the defunctionalized β rule,
  * body equation and η rule of a thunk, and a lemma stated from its two closed
  * sides; and the instance of a side, the bindings a side has in a term, and
  * the positions of a variable.
  */
object Statements:

  /** The numbered equations (1) to (6) and (8) to (10), the IR's choice and
    * parallel standing for + and ∥, over the variables M, N, P, A and B, the
    * names the design record gives them. Throws `IllegalArgumentException` for
    * another number.
    */
  def setEquation(number: Int): Statement[Nothing] =
    val first = StatementTerm.Variable("M")
    val second = StatementTerm.Variable("N")
    val third = StatementTerm.Variable("P")
    val firstArgument = StatementTerm.Variable("A")
    val secondArgument = StatementTerm.Variable("B")
    def choice(
        left: StatementTerm[Nothing],
        right: StatementTerm[Nothing]
    ): StatementTerm[Nothing] =
      StatementTerm.Layered(Choice(left, right))
    def parallel(
        left: StatementTerm[Nothing],
        right: StatementTerm[Nothing]
    ): StatementTerm[Nothing] =
      StatementTerm.Layered(Parallel(left, right))
    def apply(
        function: StatementTerm[Nothing],
        argument: StatementTerm[Nothing]
    ): StatementTerm[Nothing] =
      StatementTerm.Layered(Apply(function, argument))
    number match
      case 1 => Statement(choice(first, second), choice(second, first))
      case 2 =>
        Statement(
          choice(choice(first, second), third),
          choice(first, choice(second, third))
        )
      case 3 => Statement(parallel(first, second), parallel(second, first))
      case 4 =>
        Statement(
          parallel(parallel(first, second), third),
          parallel(first, parallel(second, third))
        )
      case 5 => Statement(parallel(first, choice(first, second)), first)
      case 6 => Statement(choice(first, parallel(first, second)), first)
      case 8 =>
        Statement(
          apply(choice(first, second), third),
          choice(apply(first, third), apply(second, third))
        )
      case 9 =>
        Statement(
          apply(parallel(first, second), third),
          parallel(apply(first, third), apply(second, third))
        )
      case 10 =>
        Statement(
          choice(
            apply(first, firstArgument),
            apply(first, choice(firstArgument, secondArgument))
          ),
          apply(first, choice(firstArgument, secondArgument))
        )
      case _ =>
        throw IllegalArgumentException(s"no numbered equation ($number)")

  /** The highest slot of the enclosing thunk that the code reads, -1 when none.
    * A nested thunk's code numbers its own slots; its fillings read the
    * enclosing thunk's. Every slot below the highest is read somewhere, since
    * the front end numbers slots by first occurrence.
    */
  def highestSlot(code: Code): Int = code.layer match
    case Slot(index)               => index
    case Apply(function, argument) =>
      highestSlot(function) max highestSlot(argument)
    case Parallel(left, right) => highestSlot(left) max highestSlot(right)
    case Choice(left, right)   => highestSlot(left) max highestSlot(right)
    case Thunk(_, _, fillings) =>
      fillings.map(highestSlot).maxOption.getOrElse(-1)

  /** The number of fillings of a thunk of the code with the holes: the code's
    * slots that are no hole. Throws `IllegalArgumentException` when it would be
    * negative.
    */
  def thunkArity(code: Code, holes: Vector[Hole]): Int =
    val arity = highestSlot(code) + 1 - holes.count {
      case Hole.Bound(_) => true
      case Hole.Ignored  => false
    }
    if arity < 0 then
      throw IllegalArgumentException(
        s"the code $code reads fewer slots than the holes $holes bind"
      )
    arity

  /** A thunk of the code with the holes has a defunctionalized η rule equation:
    * its body is `apply(slot(F), slot(H))`, its one hole is H, and F is another
    * slot.
    */
  def etaShaped(code: Code, holes: Vector[Hole]): Boolean = holes match
    case Vector(Hole.Bound(hole)) =>
      code.layer match
        case Apply(function, argument) =>
          (function.layer, argument.layer) match
            case (Slot(functionSlot), Slot(argumentSlot)) =>
              argumentSlot == hole && functionSlot != hole
            case _ => false
        case _ => false
    case _ => false

  /** The variables `stem0`, `stem1`, ..., as many as the count. */
  def numberedVariables(
      stem: String,
      count: Int
  ): Vector[StatementTerm[Nothing]] =
    Vector.tabulate(count)(index => StatementTerm.Variable(s"$stem$index"))

  /** The defunctionalized β rule of a thunk of the code with the holes, the
    * first hole taking the argument: `apply(thunk(code, holes, filling0 …),
    * argument)` equals the thunk of the other holes whose fillings take the
    * argument at the first hole's slot, or drop it for a hole that is ignored.
    * Throws `IllegalArgumentException` for no hole.
    */
  def fill(code: Code, holes: Vector[Hole]): Statement[Nothing] =
    val fillings = numberedVariables("filling", thunkArity(code, holes))
    val argument = StatementTerm.Variable("argument")
    val left = StatementTerm.Layered(
      Apply(StatementTerm.Layered(Thunk(code, holes, fillings)), argument)
    )
    val right: StatementTerm[Nothing] = holes match
      case Hole.Ignored +: rest =>
        StatementTerm.Layered(Thunk(code, rest, fillings))
      case Hole.Bound(slot) +: rest =>
        val position = Defunctionalization.fillingPosition(rest, slot)
        StatementTerm.Layered(
          Thunk(code, rest, fillings.patch(position, Vector(argument), 0))
        )
      case _ =>
        throw IllegalArgumentException(
          s"the equation of a fill has a hole, not $holes"
        )
    Statement(left, right)

  /** The equation of a thunk with no hole and its code's body, the slots read
    * as the fillings: an equation of the article's logic, whose thunk constant
    * of no hole is a HOL constant and no term of the IR, so that its left side
    * is a side of a statement only, never instantiated as a term (`instance`
    * refuses it); a trace joins the β rule's step into the thunk of no hole to
    * this one and replays the two as one (`betaBody`).
    */
  def body(code: Code): Statement[Nothing] =
    val fillings = numberedVariables("filling", thunkArity(code, Vector.empty))
    Statement(
      StatementTerm.Layered(Thunk(code, Vector.empty, fillings)),
      codeInstance(code, fillings)
    )

  /** The defunctionalized β rule of a thunk of one hole followed by the body
    * equation of the thunk with no hole it leaves (`fill`, then `body`):
    * `apply(thunk(code, [hole], filling0 …), argument)` equals the code's body
    * over the fillings, the argument at the hole's slot, or dropped for an
    * ignored hole. A trace replays the two steps as one, so that no command
    * writes the thunk with no hole, which the front end never spells
    * (`ReplaySpelling`). Throws `IllegalArgumentException` for other than one
    * hole.
    */
  def betaBody(code: Code, holes: Vector[Hole]): Statement[Nothing] =
    if holes.size != 1 then
      throw IllegalArgumentException(
        s"the β rule into a body fills the one hole, not $holes"
      )
    fill(code, holes) match
      case Statement(
            left,
            StatementTerm.Layered(Thunk(_, Vector(), fillings))
          ) =>
        Statement(left, codeInstance(code, fillings))
      case other =>
        throw IllegalStateException(
          s"the β rule of one hole leaves no thunk with no hole: $other"
        )

  /** The defunctionalized η rule of an eta-shaped thunk: the thunk equals its
    * one filling.
    */
  def eta(code: Code, holes: Vector[Hole]): Statement[Nothing] =
    val filling = StatementTerm.Variable("filling0")
    Statement(
      StatementTerm.Layered(Thunk(code, holes, Vector(filling))),
      filling
    )

  /** The equation of a thunk of the code with the holes and its spelling by the
    * front end (`BindingNormalForm.respelled`): `thunk(code, holes, filling0
    * …)` equals the respelled thunk, whose fillings are terms over the
    * variables. Throws `IllegalArgumentException` for a thunk that is its own
    * spelling, and as `BindingNormalForm.respelled` does for one with no hole.
    */
  def respell(code: Code, holes: Vector[Hole]): Statement[Nothing] =
    val arity = thunkArity(code, holes)
    val fillings = numberedVariables("filling", arity)
    val (spelledCode, spelledHoles, spelledFillings) = BindingNormalForm
      .respelled(code, holes, arity)
      .getOrElse(
        throw IllegalArgumentException(
          s"the thunk of $code and $holes is its own spelling"
        )
      )
    Statement(
      StatementTerm.Layered(Thunk(code, holes, fillings)),
      StatementTerm.Layered(
        Thunk(
          spelledCode,
          spelledHoles,
          spelledFillings.map(filling =>
            BindingNormalForm.fillingMapped(filling, fillings)(
              StatementTerm.Layered(_)
            )
          )
        )
      )
    )

  /** The statement of a lemma of two closed sides, as the baseline's encoding
    * reads them (`com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding`): the
    * binders both sides open with are the variables `metavariable0`,
    * `metavariable1`, ..., outermost first; a side with binders left over is
    * the thunk of the object lambda they make; every filling of a side, a
    * closed term, is an instruction; a lemma of no metavariable equates its two
    * sides. The article states a lemma from the strategy's encoding, and the
    * writer of a trace checks that the two agree
    * (`com.yang_bo.gezi.proofs.RewriteTrace.trace`).
    */
  def lemma[C <: NativeSpecializer & Singleton](
      left: Configured[C],
      right: Configured[C]
  )(using C): Statement[Configured[C]] =
    val arity = binders(left) min binders(right)
    Statement(side(left, arity), side(right, arity))

  private def binders[C <: NativeSpecializer & Singleton](side: Configured[C])(
      using C
  ): Int = side.layer match
    case Thunk(_, holes, _) => holes.size
    case _                  => 0

  private def side[C <: NativeSpecializer & Singleton](
      side: Configured[C],
      arity: Int
  )(using C): StatementTerm[Configured[C]] =
    (arity, side.layer) match
      case (0, _)                            => StatementTerm.Stored(side)
      case (_, Thunk(code, holes, fillings)) =>
        val (metavariableHoles, lambdaHoles) = holes.splitAt(arity)
        val holeValues: Vector[Option[StatementTerm[Configured[C]]]] =
          numberedVariables("metavariable", metavariableHoles.size).map(
            Some(_)
          ) ++ lambdaHoles.map(_ => None)
        val environment = Defunctionalization.slotValues(
          holes,
          holeValues,
          fillings.map(filling => Some(StatementTerm.Stored(filling)))
        )
        if lambdaHoles.isEmpty then
          codeInstance(
            code,
            environment.map(
              _.getOrElse(
                throw IllegalStateException(
                  "a lambda hole with no binder left over"
                )
              )
            )
          )
        else
          StatementTerm.Layered(Thunk(code, lambdaHoles, environment.flatten))
      case (_, other) =>
        throw IllegalArgumentException(
          s"a side that is no thunk has no $arity metavariables: $other"
        )

  /** The body of a thunk with no hole, its slot i read as the element i of the
    * fillings. Throws `IllegalArgumentException` for a slot with none. A
    * trampoline: a code is as deep as a program.
    */
  def codeInstance[Term](
      code: Code,
      fillings: Vector[StatementTerm[Term]]
  ): StatementTerm[Term] = codeInstanced(code, fillings).result

  private def codeInstanced[Term](
      code: Code,
      fillings: Vector[StatementTerm[Term]]
  ): TailRec[StatementTerm[Term]] =
    def binary(first: Code, second: Code)(
        layer: (StatementTerm[Term], StatementTerm[Term]) => Layer[
          StatementTerm[Term]
        ]
    ): TailRec[StatementTerm[Term]] =
      for
        firstMade <- tailcall(codeInstanced(first, fillings))
        secondMade <- tailcall(codeInstanced(second, fillings))
      yield StatementTerm.Layered(layer(firstMade, secondMade))
    code.layer match
      case Slot(index) =>
        done(
          fillings
            .lift(index)
            .getOrElse(
              throw IllegalArgumentException(
                s"the code reads slot $index of ${fillings.size}"
              )
            )
        )
      case Apply(function, argument)  => binary(function, argument)(Apply(_, _))
      case Parallel(left, right)      => binary(left, right)(Parallel(_, _))
      case Choice(left, right)        => binary(left, right)(Choice(_, _))
      case Thunk(inner, holes, codes) =>
        traversed(codes)(child => tailcall(codeInstanced(child, fillings))).map(
          made => StatementTerm.Layered(Thunk(inner, holes, made))
        )

  /** The variables of a side, each time they occur, in order. */
  def variables[Term](term: StatementTerm[Term]): Vector[String] = term match
    case StatementTerm.Variable(name) => Vector(name)
    case StatementTerm.Stored(_)      => Vector.empty
    case StatementTerm.Layered(layer) => layer.children.flatMap(variables)

  /** `occurrences` of every variable of the term, in one walk: each variable's
    * positions in preorder. A loop over the positions pending: a side is as
    * deep as a program's code.
    */
  def occurrencesByName[Term](
      term: StatementTerm[Term]
  ): Map[String, Vector[Vector[PositionSegment]]] =
    @tailrec
    def walked(
        pending: List[(StatementTerm[Term], Vector[PositionSegment])],
        found: Map[String, Vector[Vector[PositionSegment]]]
    ): Map[String, Vector[Vector[PositionSegment]]] =
      pending match
        case Nil                                          => found
        case (StatementTerm.Variable(name), path) :: rest =>
          walked(
            rest,
            found.updated(name, found.getOrElse(name, Vector.empty) :+ path)
          )
        case (StatementTerm.Stored(_), _) :: rest         => walked(rest, found)
        case (StatementTerm.Layered(layer), path) :: rest =>
          walked(
            layer.children
              .zip(Positions.roles(layer))
              .map((child, role) => (child, path :+ role))
              .toList ++ rest,
            found
          )
    walked(List((term, Vector.empty)), Map.empty)

  /** The positions of the variable in a side. */
  def occurrences[Term](
      term: StatementTerm[Term],
      name: String
  ): Vector[Vector[PositionSegment]] = term match
    case StatementTerm.Variable(found) =>
      if found == name then Vector(Vector.empty) else Vector.empty
    case StatementTerm.Stored(_)      => Vector.empty
    case StatementTerm.Layered(layer) =>
      layer.children
        .zip(Positions.roles(layer))
        .flatMap((child, role) => occurrences(child, name).map(role +: _))

  /** The closed instruction of a side with its variables bound. Throws
    * `IllegalArgumentException` for a variable with no binding. A trampoline: a
    * term is as deep as a program.
    */
  def instance[C <: NativeSpecializer & Singleton](
      term: StatementTerm[Configured[C]],
      bound: Map[String, Configured[C]]
  )(using C): Configured[C] =
    instanced(term, bound).result

  private def instanced[C <: NativeSpecializer & Singleton](
      term: StatementTerm[Configured[C]],
      bound: Map[String, Configured[C]]
  )(using C): TailRec[Configured[C]] = term match
    case StatementTerm.Stored(stored) => done(stored)
    case StatementTerm.Variable(name) =>
      done(
        bound.getOrElse(
          name,
          throw IllegalArgumentException(s"the instance binds no $name")
        )
      )
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(instanced(child, bound))).map(
        children => rebuilt(layer, children)
      )

  /** The bindings of the side's variables that make it the term: each variable
    * bound to the subterm at its occurrences, every instruction the term's
    * subterm there, every layer of the side a layer of the same shape in the
    * term. Throws `IllegalArgumentException` when the term is no instance of
    * the side. A trampoline.
    */
  def bindings[C <: NativeSpecializer & Singleton](
      side: StatementTerm[Configured[C]],
      term: Configured[C]
  )(using C, StorageAccess): Map[String, Configured[C]] =
    matchedBindings(side, term).getOrElse(
      throw IllegalArgumentException(s"$term is no instance of $side")
    )

  /** `bindings`, or nothing when the term is no instance of the side. */
  def matchedBindings[C <: NativeSpecializer & Singleton](
      side: StatementTerm[Configured[C]],
      term: Configured[C]
  )(using C, StorageAccess): Option[Map[String, Configured[C]]] =
    matched(side, term, Map.empty).result

  private def matched[C <: NativeSpecializer & Singleton](
      side: StatementTerm[Configured[C]],
      term: Configured[C],
      bound: Map[String, Configured[C]]
  )(using C, StorageAccess): TailRec[Option[Map[String, Configured[C]]]] =
    side match
      case StatementTerm.Variable(name) =>
        done(bound.get(name) match
          case Some(earlier) if !Configured.same(earlier, term) => None
          case _ => Some(bound.updated(name, term)))
      case StatementTerm.Stored(stored) =>
        done(Option.when(Configured.same(stored, term))(bound))
      case StatementTerm.Layered(_) if term.opaque => done(None)
      case StatementTerm.Layered(layer)            =>
        val termLayer = Positions.layerOf(term)
        if !sameShape(layer, termLayer) then done(None)
        else
          TailRecFolds
            .folded[(StatementTerm[Configured[C]], Configured[C]), Option[
              Map[String, Configured[C]]
            ]](
              layer.children.zip(termLayer.children).toVector,
              Some(bound)
            ) {
              case (Some(current), (child, termChild)) =>
                matched(child, termChild, current)
              case (None, _) => done(None)
            }

  private def sameShape[Term, C <: NativeSpecializer & Singleton](
      side: Layer[StatementTerm[Term]],
      term: Positions.TraceLayer[Configured[C]]
  ): Boolean = (side, term) match
    case (Apply(_, _), Apply(_, _))       => true
    case (Choice(_, _), Choice(_, _))     => true
    case (Parallel(_, _), Parallel(_, _)) => true
    // A storage's view is the parallel the storage stands for.
    case (Parallel(_, _), StorageView(_, _)) => true
    case (
          Thunk(code, holes, fillings),
          Thunk(termCode, termHoles, termFillings)
        ) =>
      code == termCode && holes == termHoles && fillings.size == termFillings.size
    case _ => false

  /** The term of the side's layer of the same shape over the children, as many
    * as it has, built through the trace's configuration (`Positions.built`): a
    * parallel converted into its storage when it is the unique spelling of one.
    * Throws `IllegalArgumentException` for a thunk of no hole, which is no
    * term.
    */
  private def rebuilt[Term, C <: NativeSpecializer & Singleton](
      layer: Layer[StatementTerm[Term]],
      children: Vector[Configured[C]]
  )(using C): Configured[C] =
    layer match
      case Thunk(code, Vector(), _) =>
        throw IllegalArgumentException(
          s"a thunk of the code $code with no hole is a side of a statement, no term"
        )
      case _ => Positions.built(layer, children)

  /** The results of the step on each item, in order, as a trampoline. */
  private[rewritetrace] def traversed[Item, Result](items: Vector[Item])(
      step: Item => TailRec[Result]
  ): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else
        tailcall(step(items(index))).flatMap(result =>
          from(index + 1, results :+ result)
        )
    from(0, Vector.empty)
