package gezi.rewritetrace

import scala.annotation.tailrec

import gezi.frontend.Defunctionalization
import gezi.ir.BindingNormalForm
import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** A side of an equation: a term over instructions with named variables. */
enum StatementTerm:
  case Variable(name: String)
  case Stored(instruction: Instruction)
  case Layered(layer: Layer[StatementTerm])

/** An equation `left = right` whose variables are universally quantified. */
final case class Statement(left: StatementTerm, right: StatementTerm):

  /** The variables, each once, in the order they first occur, left side
    * first: the order a command's bindings index (`TraceCommand.Rewrite`).
    */
  def variables: Vector[String] = (Statements.variables(left) ++ Statements.variables(right)).distinct

  /** The side a step in the direction replaces, and the side it puts there. */
  def oriented(direction: RewriteDirection): (StatementTerm, StatementTerm) = direction match
    case RewriteDirection.Forward  => (left, right)
    case RewriteDirection.Backward => (right, left)

  /** The provenance of the variables, in the order of `variables`, from the
    * left side to the right side. Each side is walked once for all its
    * variables (`Statements.occurrencesByName`): the β rule of a thunk of n
    * fillings has n variables, and walking the sides once for each made a
    * step of a program's top-level thunk cost n² (2,468 fillings on `contest-entries-solo`'s
    * repeated_library_hotspots calls_1000 point).
    */
  def provenance: Vector[Provenance] =
    val onLeft = Statements.occurrencesByName(left)
    val onRight = Statements.occurrencesByName(right)
    variables.map(name => Provenance(name, onLeft.getOrElse(name, Vector.empty), onRight.getOrElse(name, Vector.empty)))

/** The equations a step instantiates, stated as the article states them
  * (`gezi.proofs.ArticleStore.axiomStatement`, which reads them from
  * here): the numbered equations of the formal definition, the
  * defunctionalized β rule, body equation and η rule of a thunk, and a lemma
  * stated from its two closed sides; and the instance of a side, the
  * bindings a side has in a term, and the positions of a variable.
  */
object Statements:

  /** The numbered equations (1) to (6) and (8) to (10), the IR's choice and
    * parallel standing for + and ∥, over the variables M, N, P, A and B, the
    * names the design record gives them. Throws `IllegalArgumentException`
    * for another number.
    */
  def setEquation(number: Int): Statement =
    val first = StatementTerm.Variable("M")
    val second = StatementTerm.Variable("N")
    val third = StatementTerm.Variable("P")
    val firstArgument = StatementTerm.Variable("A")
    val secondArgument = StatementTerm.Variable("B")
    def choice(left: StatementTerm, right: StatementTerm) = StatementTerm.Layered(Choice(left, right))
    def parallel(left: StatementTerm, right: StatementTerm) = StatementTerm.Layered(Parallel(left, right))
    def apply(function: StatementTerm, argument: StatementTerm) = StatementTerm.Layered(Apply(function, argument))
    number match
      case 1 => Statement(choice(first, second), choice(second, first))
      case 2 => Statement(choice(choice(first, second), third), choice(first, choice(second, third)))
      case 3 => Statement(parallel(first, second), parallel(second, first))
      case 4 => Statement(parallel(parallel(first, second), third), parallel(first, parallel(second, third)))
      case 5 => Statement(parallel(first, choice(first, second)), first)
      case 6 => Statement(choice(first, parallel(first, second)), first)
      case 8 => Statement(apply(choice(first, second), third), choice(apply(first, third), apply(second, third)))
      case 9 => Statement(apply(parallel(first, second), third), parallel(apply(first, third), apply(second, third)))
      case 10 =>
        Statement(
          choice(apply(first, firstArgument), apply(first, choice(firstArgument, secondArgument))),
          apply(first, choice(firstArgument, secondArgument))
        )
      case _ => throw IllegalArgumentException(s"no numbered equation ($number)")

  /** The highest slot of the enclosing thunk that the code reads, -1 when
    * none. A nested thunk's code numbers its own slots; its fillings read
    * the enclosing thunk's. Every slot below the highest is read somewhere,
    * since the front end numbers slots by first occurrence.
    */
  def highestSlot(code: Code): Int = code.layer match
    case Slot(index)               => index
    case Apply(function, argument) => highestSlot(function) max highestSlot(argument)
    case Parallel(left, right)     => highestSlot(left) max highestSlot(right)
    case Choice(left, right)       => highestSlot(left) max highestSlot(right)
    case Thunk(_, _, fillings)     => fillings.map(highestSlot).maxOption.getOrElse(-1)

  /** The number of fillings of a thunk of the code with the holes: the
    * code's slots that are no hole. Throws `IllegalArgumentException` when it
    * would be negative.
    */
  def thunkArity(code: Code, holes: Vector[Hole]): Int =
    val arity = highestSlot(code) + 1 - holes.count {
      case Hole.Bound(_) => true
      case Hole.Ignored  => false
    }
    if arity < 0 then throw IllegalArgumentException(s"the code $code reads fewer slots than the holes $holes bind")
    arity

  /** A thunk of the code with the holes has a defunctionalized η rule
    * equation: its body is `apply(slot(F), slot(H))`, its one hole is H, and
    * F is another slot.
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
  def numberedVariables(stem: String, count: Int): Vector[StatementTerm] =
    Vector.tabulate(count)(index => StatementTerm.Variable(s"$stem$index"))

  /** The defunctionalized β rule of a thunk of the code with the holes,
    * the first hole taking the argument: `apply(thunk(code, holes,
    * filling0 …), argument)` equals the thunk of the other holes whose
    * fillings take the argument at the first hole's slot, or drop it for a
    * hole that is ignored. Throws `IllegalArgumentException` for no hole.
    */
  def fill(code: Code, holes: Vector[Hole]): Statement =
    val fillings = numberedVariables("filling", thunkArity(code, holes))
    val argument = StatementTerm.Variable("argument")
    val left = StatementTerm.Layered(Apply(StatementTerm.Layered(Thunk(code, holes, fillings)), argument))
    val right = holes match
      case Hole.Ignored +: rest => StatementTerm.Layered(Thunk(code, rest, fillings))
      case Hole.Bound(slot) +: rest =>
        val position = Defunctionalization.fillingPosition(rest, slot)
        StatementTerm.Layered(Thunk(code, rest, fillings.patch(position, Vector(argument), 0)))
      case _ => throw IllegalArgumentException(s"the equation of a fill has a hole, not $holes")
    Statement(left, right)

  /** The equation of a thunk with no hole and its code's body, the slots
    * read as the fillings.
    */
  def body(code: Code): Statement =
    val fillings = numberedVariables("filling", thunkArity(code, Vector.empty))
    Statement(StatementTerm.Layered(Thunk(code, Vector.empty, fillings)), codeInstance(code, fillings))

  /** The defunctionalized β rule of a thunk of one hole followed by the body
    * equation of the thunk with no hole it leaves (`fill`, then `body`):
    * `apply(thunk(code, [hole], filling0 …), argument)` equals the code's
    * body over the fillings, the argument at the hole's slot, or dropped
    * for an ignored hole. A trace replays the two steps as one, so that no
    * command writes the thunk with no hole, which the front end never
    * spells (`ReplaySpelling`). Throws `IllegalArgumentException` for other
    * than one hole.
    */
  def betaBody(code: Code, holes: Vector[Hole]): Statement =
    if holes.size != 1 then throw IllegalArgumentException(s"the β rule into a body fills the one hole, not $holes")
    fill(code, holes) match
      case Statement(left, StatementTerm.Layered(Thunk(_, Vector(), fillings))) => Statement(left, codeInstance(code, fillings))
      case other => throw IllegalStateException(s"the β rule of one hole leaves no thunk with no hole: $other")

  /** The defunctionalized η rule of an eta-shaped thunk: the thunk equals its
    * one filling.
    */
  def eta(code: Code, holes: Vector[Hole]): Statement =
    val filling = StatementTerm.Variable("filling0")
    Statement(StatementTerm.Layered(Thunk(code, holes, Vector(filling))), filling)

  /** The equation of a thunk of the code with the holes and its spelling by
    * the front end (`BindingNormalForm.respelled`): `thunk(code,
    * holes, filling0 …)` equals the respelled thunk, whose fillings are terms
    * over the variables. Throws `IllegalArgumentException` for a thunk that
    * is its own spelling, and as `BindingNormalForm.respelled` does for one
    * with no hole.
    */
  def respell(code: Code, holes: Vector[Hole]): Statement =
    val arity = thunkArity(code, holes)
    val fillings = numberedVariables("filling", arity)
    val (spelledCode, spelledHoles, spelledFillings) = BindingNormalForm
      .respelled(code, holes, arity)
      .getOrElse(throw IllegalArgumentException(s"the thunk of $code and $holes is its own spelling"))
    val variables = BindingNormalForm.placeholders(arity).zip(fillings).toMap
    Statement(
      StatementTerm.Layered(Thunk(code, holes, fillings)),
      StatementTerm.Layered(
        Thunk(spelledCode, spelledHoles, spelledFillings.map(filling => overPlaceholders(filling, variables).result))
      )
    )

  /** A term over placeholders as a statement term, each placeholder its
    * variable. A trampoline: a filling is as deep as a code.
    */
  private def overPlaceholders(term: Instruction, variables: Map[Instruction, StatementTerm]): TailRec[StatementTerm] =
    variables.get(term) match
      case Some(variable)      => done(variable)
      case None if term.opaque => done(StatementTerm.Stored(term))
      case None =>
        val layer = term.layered
        traversed(layer.children)(child => tailcall(overPlaceholders(child, variables))).map(children =>
          StatementTerm.Layered(layer.over(children))
        )

  /** The statement of a lemma of two closed sides, as the baseline's
    * encoding reads them (`gezi.lemmaencoding.baseline.BaselineLemmaEncoding`):
    * the binders both sides open with are the variables `metavariable0`,
    * `metavariable1`, ..., outermost first; a side with binders left over is
    * the thunk of the object lambda they make; every filling of a side, a
    * closed term, is an instruction; a lemma of no metavariable equates its two
    * sides. The article states a lemma from the strategy's encoding, and
    * the writer of a trace checks that the two agree
    * (`gezi.proofs.RewriteTrace.trace`).
    */
  def lemma(left: Instruction, right: Instruction): Statement =
    val arity = binders(left) min binders(right)
    Statement(side(left, arity), side(right, arity))

  private def binders(side: Instruction): Int = side match
    case Instruction.Thunk(_, holes, _) => holes.size
    case _                              => 0

  private def side(side: Instruction, arity: Int): StatementTerm = side match
    case _ if arity == 0 => StatementTerm.Stored(side)
    case Instruction.Thunk(code, holes, fillings) =>
      val (metavariableHoles, lambdaHoles) = holes.splitAt(arity)
      val holeValues: Vector[Option[StatementTerm]] =
        numberedVariables("metavariable", metavariableHoles.size).map(Some(_)) ++ lambdaHoles.map(_ => None)
      val environment = Defunctionalization.slotValues(holes, holeValues, fillings.map(filling => Some(StatementTerm.Stored(filling))))
      if lambdaHoles.isEmpty then
        codeInstance(
          code,
          environment.map(_.getOrElse(throw IllegalStateException("a lambda hole with no binder left over")))
        )
      else StatementTerm.Layered(Thunk(code, lambdaHoles, environment.flatten))
    case other => throw IllegalArgumentException(s"a side that is no thunk has no $arity metavariables: $other")

  /** The body of a thunk with no hole, its slot i read as the element i of
    * the fillings. Throws `IllegalArgumentException` for a slot with none. A
    * trampoline: a code is as deep as a program.
    */
  def codeInstance(code: Code, fillings: Vector[StatementTerm]): StatementTerm = codeInstanced(code, fillings).result

  private def codeInstanced(code: Code, fillings: Vector[StatementTerm]): TailRec[StatementTerm] =
    def binary(first: Code, second: Code)(layer: (StatementTerm, StatementTerm) => Layer[StatementTerm]): TailRec[StatementTerm] =
      for
        firstMade <- tailcall(codeInstanced(first, fillings))
        secondMade <- tailcall(codeInstanced(second, fillings))
      yield StatementTerm.Layered(layer(firstMade, secondMade))
    code.layer match
      case Slot(index) =>
        done(fillings.lift(index).getOrElse(throw IllegalArgumentException(s"the code reads slot $index of ${fillings.size}")))
      case Apply(function, argument) => binary(function, argument)(Apply(_, _))
      case Parallel(left, right)     => binary(left, right)(Parallel(_, _))
      case Choice(left, right)       => binary(left, right)(Choice(_, _))
      case Thunk(inner, holes, codes) =>
        traversed(codes)(child => tailcall(codeInstanced(child, fillings))).map(made =>
          StatementTerm.Layered(Thunk(inner, holes, made))
        )

  /** The variables of a side, each time they occur, in order. */
  def variables(term: StatementTerm): Vector[String] = term match
    case StatementTerm.Variable(name) => Vector(name)
    case StatementTerm.Stored(_)      => Vector.empty
    case StatementTerm.Layered(layer) => layer.children.flatMap(variables)

  /** `occurrences` of every variable of the term, in one walk: each
    * variable's positions in preorder. A loop over the positions pending: a
    * side is as deep as a program's code.
    */
  def occurrencesByName(term: StatementTerm): Map[String, Vector[Vector[PositionSegment]]] =
    @tailrec
    def walked(
        pending: List[(StatementTerm, Vector[PositionSegment])],
        found: Map[String, Vector[Vector[PositionSegment]]]
    ): Map[String, Vector[Vector[PositionSegment]]] =
      pending match
        case Nil => found
        case (StatementTerm.Variable(name), path) :: rest =>
          walked(rest, found.updated(name, found.getOrElse(name, Vector.empty) :+ path))
        case (StatementTerm.Stored(_), _) :: rest => walked(rest, found)
        case (StatementTerm.Layered(layer), path) :: rest =>
          walked(layer.children.zip(Positions.roles(layer)).map((child, role) => (child, path :+ role)).toList ++ rest, found)
    walked(List((term, Vector.empty)), Map.empty)

  /** The positions of the variable in a side. */
  def occurrences(term: StatementTerm, name: String): Vector[Vector[PositionSegment]] = term match
    case StatementTerm.Variable(found) => if found == name then Vector(Vector.empty) else Vector.empty
    case StatementTerm.Stored(_)       => Vector.empty
    case StatementTerm.Layered(layer) =>
      layer.children.zip(Positions.roles(layer)).flatMap((child, role) => occurrences(child, name).map(role +: _))

  /** The closed instruction of a side with its variables bound. Throws
    * `IllegalArgumentException` for a variable with no binding. A
    * trampoline: a term is as deep as a program.
    */
  def instance(term: StatementTerm, bound: Map[String, Instruction]): Instruction = instanced(term, bound).result

  private def instanced(term: StatementTerm, bound: Map[String, Instruction]): TailRec[Instruction] = term match
    case StatementTerm.Stored(instruction) => done(instruction)
    case StatementTerm.Variable(name) =>
      done(bound.getOrElse(name, throw IllegalArgumentException(s"the instance binds no $name")))
    case StatementTerm.Layered(layer) =>
      traversed(layer.children)(child => tailcall(instanced(child, bound))).map(children => Instruction(rebuilt(layer, children)))

  /** The bindings of the side's variables that make it the term: each
    * variable bound to the subterm at its occurrences, every instruction the
    * term's subterm there, every layer of the side a layer of the same shape
    * in the term. Throws `IllegalArgumentException` when the term is no
    * instance of the side. A trampoline.
    */
  def bindings(side: StatementTerm, term: Instruction): Map[String, Instruction] =
    matchedBindings(side, term).getOrElse(throw IllegalArgumentException(s"$term is no instance of $side"))

  /** `bindings`, or nothing when the term is no instance of the side. */
  def matchedBindings(side: StatementTerm, term: Instruction): Option[Map[String, Instruction]] =
    matched(side, term, Map.empty).result

  private def matched(
      side: StatementTerm,
      term: Instruction,
      bound: Map[String, Instruction]
  ): TailRec[Option[Map[String, Instruction]]] = side match
    case StatementTerm.Variable(name) =>
      done(bound.get(name) match
        case Some(earlier) if earlier != term => None
        case _                                   => Some(bound.updated(name, term))
      )
    case StatementTerm.Stored(instruction) => done(Option.when(instruction == term)(bound))
    case StatementTerm.Layered(layer) =>
      val termLayer = term.layered
      if !sameShape(layer, termLayer) then done(None)
      else
        TailRecFolds.folded[(StatementTerm, Instruction), Option[Map[String, Instruction]]](
          layer.children.zip(termLayer.children).toVector,
          Some(bound)
        ) {
          case (Some(current), (child, termChild)) => matched(child, termChild, current)
          case (None, _)                           => done(None)
        }

  private def sameShape(side: Layer[StatementTerm], term: Layer[Instruction]): Boolean = (side, term) match
    case (Apply(_, _), Apply(_, _))       => true
    case (Choice(_, _), Choice(_, _))     => true
    case (Parallel(_, _), Parallel(_, _)) => true
    case (Thunk(code, holes, fillings), Thunk(termCode, termHoles, termFillings)) =>
      code == termCode && holes == termHoles && fillings.size == termFillings.size
    case _ => false

  /** The layer of the same shape over the children, as many as it has. */
  private def rebuilt(layer: Layer[StatementTerm], children: Vector[Instruction]): Layer[Instruction] =
    (layer, children) match
      case (Thunk(code, holes, _), _)          => Thunk(code, holes, children)
      case (Apply(_, _), Vector(function, argument)) => Apply(function, argument)
      case (Choice(_, _), Vector(left, right))   => Choice(left, right)
      case (Parallel(_, _), Vector(left, right)) => Parallel(left, right)
      case _ => throw IllegalArgumentException(s"the layer $layer has no layer over ${children.size} children")

  /** The results of the step on each item, in order, as a trampoline. */
  private[rewritetrace] def traversed[Item, Result](items: Vector[Item])(step: Item => TailRec[Result]): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else tailcall(step(items(index))).flatMap(result => from(index + 1, results :+ result))
    from(0, Vector.empty)
