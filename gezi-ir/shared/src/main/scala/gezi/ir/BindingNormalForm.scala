package gezi.ir

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The normal form of a lemma's thunk pattern under its bindings, the one
  * function that both the higher-order saturator (`HigherOrderMatching`,
  * project `saturation`) and the trace's conversions (`Conversions`, project
  * `rewrite-trace`) compute, so that a conversion the saturator writes is one
  * the trace's replay computes, and no β conversion of the saturator is
  * left without a proof in the trace. Two implementations of it that were
  * meant to agree spelled one normal form with two codes, and the trace had no
  * command for the saturator's unions (2026-11-16): two implementations that
  * must agree are a defect waiting to recur.
  *
  * What it is: the instance of the pattern under the bindings, with every
  * application of a higher-order metavariable's value reduced by β,
  * hereditarily (a lambda given as an argument to an inlined lambda is
  * inlined in turn), spelled as the front end spells a closed term
  * (`gezi.frontend.Defunctionalization`): a chain of lambdas is one thunk
  * whose holes are its binders, outermost first, a binder the body does not
  * read an ignored hole; the body's slots are numbered by first occurrence
  * in preorder; each maximal subterm that reads no binder around it is one
  * slot, equal subterms one slot, filled by that subterm; an inner lambda is
  * an inner thunk whose fillings are slots of the body, in its own slot
  * order; and a chain's body that is a thunk with holes goes on as the chain.
  *
  * It is a normal form relative to the bindings, not the β-normal form of the
  * whole term: only the higher-order metavariables' values, and lambdas
  * passed to them, are reduced; any other value is a leaf as it is, even a
  * thunk applied to something, and a redex of the pattern's own code that no
  * inlined value makes is kept. Do not "complete" it into full β: the
  * conversions it defines are the instances' equations, and nothing else.
  *
  * A higher-order metavariable's value is entered whatever it is: a thunk
  * with holes is inlined; any other value stays a leaf. A value is an
  * instruction, an opaque one standing for a subterm the caller does not
  * expand (the saturator's graph nodes that are no thunk with holes).
  *
  * Every recursion over a term, a code or a value is a trampoline
  * (`scala.util.control.TailCalls`), so that no function here recurses on
  * the JVM stack once per level of nesting: a term the front end reads back
  * from a printed program nests as deep as the program, and the e-graph
  * respells each thunk it adds (`gezi.egraph.Respelling`); recursing on the
  * stack, a programfamilies `list` item of size 512 overflowed a 1 MB thread
  * stack 2,461 frames deep (`BindingNormalFormDepthLawTest`). A trampoline is bound (`map`,
  * `flatMap`) only where it is a `tailcall` or a `done`, never on the
  * result of another bind: `TailCalls` binds a bound trampoline by composing
  * the continuations into one closure, which a recursion that binds each
  * level's result in turn nests one closure per level, so that running it
  * recurses on the stack once per level and costs the square of the depth.
  */
object BindingNormalForm:

  /** The normal form of the thunk pattern under the bindings, the higher-order
    * metavariables' indices given. Throws `IllegalArgumentException` for a
    * metavariable with no binding, and `IllegalStateException` when the
    * pattern's thunk reads a binder around it (a pattern of a lemma's side is
    * closed).
    */
  def of(thunk: Pattern.Thunk, bindings: Map[Int, Instruction], higherOrder: Set[Int]): Instruction =
    tailcall(traversed(thunk.fillings)(patternValue(_, bindings, higherOrder)))
      .flatMap(fillings => closedInstruction(Value.Lambda.of(thunk.code, thunk.holes, fillingEnvironment(thunk.holes, fillings), inlined = false)))
      .result
      .getOrElse(throw IllegalStateException(s"the pattern's thunk reads a binder around it under $bindings"))

  /** The opaque leaves that stand for a thunk's fillings while it is
    * respelled (`respelled`), by position; no library names them and no
    * pattern mentions them.
    */
  def placeholders(count: Int): Vector[Instruction] =
    Vector.tabulate(count)(position => Instruction.opaque(s"respelling placeholder of filling $position"))

  /** A filling of a spelling `respelled` gives, folded bottom-up through a
    * state: the placeholder of position p is `standing(p)`, and every other
    * subterm is `made` of the state and its layer over its children's
    * results, the children folded in the order of `children`. The e-graph
    * makes a respelled thunk's fillings with it (`gezi.egraph.Respelling`),
    * a lemma's side is respelled with it
    * (`gezi.orientation.OrientationCompilation`), and an article's
    * pattern (`gezi.proofs.ProofMatching`).
    *
    * Every leaf of such a filling is a placeholder: `respelled` spells a
    * thunk whose fillings are the placeholders, its code has no leaf but its
    * slots (`CodeLayer` has no opaque case), and the spelling is made of the
    * code's layers and the fillings' values. Throws `IllegalStateException`
    * for another opaque leaf.
    */
  def placeholdersFolded[State, Result](filling: Instruction, standing: Vector[Result], state: State)(
      made: (State, Layer[Result]) => (State, Result)
  ): (State, Result) =
    val positions = placeholders(standing.size).zipWithIndex.toMap
    def folded(term: Instruction, current: State): TailRec[(State, Result)] =
      positions.get(term) match
        case Some(position) => done((current, standing(position)))
        case None if term.opaque =>
          throw IllegalStateException(s"a respelled filling holds the leaf $term, no placeholder")
        case None =>
          val layer = term.layered
          val children = layer.children
          def from(index: Int, before: State, results: Vector[Result]): TailRec[(State, Vector[Result])] =
            if index >= children.size then done((before, results))
            else tailcall(folded(children(index), before)).flatMap((next, result) => from(index + 1, next, results :+ result))
          tailcall(from(0, current, Vector.empty)).map((after, results) => made(after, layer.over(results)))
    folded(filling, state).result

  /** `placeholdersFolded` with no state. */
  def placeholdersMapped[Result](filling: Instruction, standing: Vector[Result])(made: Layer[Result] => Result): Result =
    placeholdersFolded(filling, standing, ())((_, layer) => ((), made(layer)))._2

  /** The front end's spelling of a thunk of the code and holes whose
    * `fillingCount` fillings are opaque placeholders, a function of these
    * alone: nothing
    * when the thunk is its own spelling, else the code, the holes and the
    * fillings it is spelled with, the fillings closed terms over
    * `placeholders`, each placeholder standing for the filling of its
    * position. It is not the front end's spelling of the thunk with its
    * actual fillings (`spelled`) where a placeholder hides what the front
    * end reads: a filling that is a lambda at the body of the chain, which
    * the front end continues the chain through, and equal fillings, which
    * it makes one slot. The e-graph makes its thunk nodes in this spelling
    * (`gezi.egraph.Respelling`), a trace replays in it
    * (`gezi.rewritetrace.ReplaySpelling`), and its Respell equation
    * states it (`Statements.respell`). Throws
    * `IllegalArgumentException` for no hole and `IllegalStateException` when
    * the spelling is no thunk.
    */
  def respelled(code: Code, holes: Vector[Hole], fillingCount: Int): Option[(Code, Vector[Hole], Vector[Instruction])] =
    require(holes.nonEmpty, s"a thunk respelled has holes: $code")
    val standing = placeholders(fillingCount)
    spelled(Instruction.Thunk(code, holes, standing)).layered match
      case Thunk(spelledCode, spelledHoles, spelledFillings) =>
        Option.unless(spelledCode == code && spelledHoles == holes && spelledFillings == standing)(
          (spelledCode, spelledHoles, spelledFillings)
        )
      case other => throw IllegalStateException(s"the spelling of a thunk with holes is no thunk: $other")

  /** The closed instruction spelled as the front end spells a closed term,
    * with nothing reduced: the spelling half of `of`, which the front end's
    * `Defunctionalization.thunkInstruction` is to call. Throws
    * `IllegalArgumentException` for an instruction that is not closed.
    */
  def spelled(instruction: Instruction): Instruction =
    tailcall(instructionValue(instruction))
      .flatMap(closedInstruction)
      .result
      .getOrElse(throw IllegalArgumentException(s"the instruction is not closed: $instruction"))

  /** The results of the step on each item, in order, as a trampoline: each
    * step is bound in the continuation of the one before it, so that no
    * chain of continuations is built before it runs, which a fold of binds
    * from the left would build and then call one inside another.
    */
  private def traversed[Item, Result](items: Vector[Item])(step: Item => TailRec[Result]): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else tailcall(step(items(index))).flatMap(result => from(index + 1, results :+ result))
    from(0, Vector.empty)

  /** The instruction as a value with nothing inlined: a thunk a lambda over
    * its fillings, one layer over values, an opaque instruction a leaf.
    */
  private def instructionValue(instruction: Instruction): TailRec[Value] = instruction match
    case Instruction.Apply(function, argument) =>
      tailcall(instructionValue(function)).flatMap(functionValue =>
        tailcall(instructionValue(argument)).map(Value.Apply(functionValue, _))
      )
    case Instruction.Parallel(left, right) =>
      tailcall(instructionValue(left)).flatMap(leftValue => tailcall(instructionValue(right)).map(Value.Parallel(leftValue, _)))
    case Instruction.Choice(left, right) =>
      tailcall(instructionValue(left)).flatMap(leftValue => tailcall(instructionValue(right)).map(Value.Choice(leftValue, _)))
    case Instruction.Thunk(code, holes, fillings) =>
      tailcall(traversed(fillings)(instructionValue)).map(values =>
        Value.Lambda.of(code, holes, fillingEnvironment(holes, values), inlined = false)
      )
    case other => done(Value.Leaf(other))

  /** A term as the normal form reads it: a binder of a lambda entered, a
    * closed leaf, one layer over values, or a lambda whose holes are not yet
    * entered (a code, its holes, and its slots read so far). A lambda that is
    * `inlined` is a higher-order metavariable's value (or a lambda given to
    * one), reduced by β where it is applied.
    */
  private sealed trait Value:

    /** The binders of lambdas around the value that it reads, computed when
      * the value is made from its parts' own, which were made before it, so
      * that asking at every node of an emission costs the value's size once,
      * not once per level, and computing it recurses no deeper than one
      * level.
      */
    val binders: Set[Int]

  private object Value:

    final case class Bound(binder: Int) extends Value:
      val binders: Set[Int] = Set(binder)

    final case class Leaf(instruction: Instruction) extends Value:
      val binders: Set[Int] = Set.empty

    final case class Apply(function: Value, argument: Value) extends Value:
      val binders: Set[Int] = function.binders ++ argument.binders

    final case class Parallel(left: Value, right: Value) extends Value:
      val binders: Set[Int] = left.binders ++ right.binders

    final case class Choice(left: Value, right: Value) extends Value:
      val binders: Set[Int] = left.binders ++ right.binders

    /** A lambda, its binders those of its environment's values, which `of`
      * computes and which entering a hole (`applied`) extends by the value
      * it enters.
      */
    final case class Lambda(code: Code, holes: Vector[Hole], environment: Map[Int, Value], inlined: Boolean, binders: Set[Int])
        extends Value

    object Lambda:
      /** The lambda with the binders of its environment's values. */
      def of(code: Code, holes: Vector[Hole], environment: Map[Int, Value], inlined: Boolean): Lambda =
        Lambda(code, holes, environment, inlined, environment.values.foldLeft(Set.empty[Int])(_ ++ _.binders))

  /** The pattern under the bindings: a higher-order metavariable's value
    * inlined wherever it occurs, any other value a leaf, a reference its
    * instruction, a thunk a lambda over its fillings.
    */
  private def patternValue(pattern: Pattern, bindings: Map[Int, Instruction], higherOrder: Set[Int]): TailRec[Value] =
    pattern match
      case Pattern.Metavariable(index)               => done(bound(index, bindings, higherOrder))
      case Pattern.Closure(index)                    => done(bound(index, bindings, higherOrder))
      case Pattern.InstructionReference(instruction) => done(Value.Leaf(instruction))
      case Pattern.Apply(function, argument) =>
        tailcall(patternValue(function, bindings, higherOrder)).flatMap(functionValue =>
          tailcall(patternValue(argument, bindings, higherOrder)).map(Value.Apply(functionValue, _))
        )
      case Pattern.Parallel(left, right) =>
        tailcall(patternValue(left, bindings, higherOrder)).flatMap(leftValue =>
          tailcall(patternValue(right, bindings, higherOrder)).map(Value.Parallel(leftValue, _))
        )
      case Pattern.Choice(left, right) =>
        tailcall(patternValue(left, bindings, higherOrder)).flatMap(leftValue =>
          tailcall(patternValue(right, bindings, higherOrder)).map(Value.Choice(leftValue, _))
        )
      case Pattern.Thunk(code, holes, fillings) =>
        tailcall(traversed(fillings)(patternValue(_, bindings, higherOrder))).map(values =>
          Value.Lambda.of(code, holes, fillingEnvironment(holes, values), inlined = false)
        )

  private def bound(index: Int, bindings: Map[Int, Instruction], higherOrder: Set[Int]): Value =
    val value = bindings.getOrElse(index, throw IllegalArgumentException(s"the metavariable $index has no binding"))
    if higherOrder.contains(index) then inlinedValue(value) else Value.Leaf(value)

  /** A value given to be reduced where applied: a thunk with holes as an
    * inlined lambda, anything else a leaf.
    */
  private def inlinedValue(instruction: Instruction): Value = instruction match
    case Instruction.Thunk(code, holes, fillings) if holes.nonEmpty =>
      Value.Lambda.of(code, holes, fillingEnvironment(holes, fillings.map(Value.Leaf(_))), inlined = true)
    case other => Value.Leaf(other)

  /** For each slot of a thunk that is no hole, its filling. */
  private def fillingEnvironment[Filling](holes: Vector[Hole], fillings: Vector[Filling]): Map[Int, Filling] =
    val boundSlots = holes.collect { case Hole.Bound(slot) => slot }.toSet
    val slots = (0 until boundSlots.size + fillings.size).filterNot(boundSlots.contains)
    require(slots.size == fillings.size, s"the fillings $fillings do not fill the slots of $holes")
    slots.zip(fillings).toMap

  /** The code read under the environment of its slots. */
  private def read(code: Code, environment: Map[Int, Value]): TailRec[Value] = code.layer match
    case Slot(index) =>
      done(environment.getOrElse(index, throw IllegalStateException(s"the slot $index is not in $environment")))
    case Apply(function, argument) =>
      tailcall(read(function, environment)).flatMap(functionValue =>
        tailcall(read(argument, environment)).map(Value.Apply(functionValue, _))
      )
    case Parallel(left, right) =>
      tailcall(read(left, environment)).flatMap(leftValue => tailcall(read(right, environment)).map(Value.Parallel(leftValue, _)))
    case Choice(left, right) =>
      tailcall(read(left, environment)).flatMap(leftValue => tailcall(read(right, environment)).map(Value.Choice(leftValue, _)))
    case Thunk(inner, holes, fillings) =>
      tailcall(traversed(fillings)(read(_, environment))).map(values =>
        Value.Lambda.of(inner, holes, fillingEnvironment(holes, values), inlined = false)
      )

  /** The lambda with its first hole entered by the value: the lambda of the
    * holes left, or its body when none is. A `tailcall` or a `done`, which a
    * caller binds as it is.
    */
  private def applied(lambda: Value.Lambda, value: Value): TailRec[Value] =
    val (environment, binders) = lambda.holes.headOption match
      case Some(Hole.Bound(slot)) if lambda.environment.contains(slot) =>
        val replaced = lambda.environment.updated(slot, value)
        (replaced, Value.Lambda.of(lambda.code, lambda.holes, replaced, lambda.inlined).binders)
      case Some(Hole.Bound(slot)) => (lambda.environment.updated(slot, value), lambda.binders ++ value.binders)
      case Some(Hole.Ignored)     => (lambda.environment, lambda.binders)
      case None                   => throw IllegalStateException(s"a lambda with no hole is applied: $lambda")
    if lambda.holes.size == 1 then tailcall(read(lambda.code, environment))
    else done(lambda.copy(holes = lambda.holes.tail, environment = environment, binders = binders))

  /** The value with every application of an inlined lambda at its head
    * reduced by β, a lambda given as an argument to it inlined in turn.
    *
    * FIXME (carried from `HigherOrderMatching.headReduced`, 2026-11-04): https://github.com/Atry/private-overlay/issues/1965
    * nothing bounds the reduction; a higher-order value that applies a lambda
    * to itself, as `λy. y y` given `λx. x x`, does not end. No lemma of the
    * standard library has such a right side. Candidate fix: a bound on the β
    * steps of one normal form, the instance dropped when it is reached.
    */
  private def headReduced(value: Value): TailRec[Value] = value match
    case Value.Apply(_, _) =>
      val (head, arguments) = spine(value, Nil)
      head match
        case lambda: Value.Lambda if lambda.inlined =>
          tailcall(argumentsEntered(lambda, arguments)).flatMap(headReduced)
        case _ => done(value)
    case other => done(other)

  /** The function applied to the arguments in order: each enters the next
    * hole while the function is a lambda, a lambda argument inlined; the
    * arguments left, from the first the function is no lambda for, applied
    * to what it gives.
    */
  private def argumentsEntered(function: Value, arguments: List[Value]): TailRec[Value] = (function, arguments) match
    case (entered: Value.Lambda, argument :: rest) =>
      val passed = argument match
        case argumentLambda: Value.Lambda => argumentLambda.copy(inlined = true)
        case other                        => other
      tailcall(applied(entered, passed)).flatMap(argumentsEntered(_, rest))
    case _ => done(arguments.foldLeft(function)(Value.Apply(_, _)))

  /** The head of an application spine and its arguments in order, the
    * arguments of the applications around the value given after them.
    */
  @scala.annotation.tailrec
  private def spine(value: Value, arguments: List[Value]): (Value, List[Value]) = value match
    case Value.Apply(function, argument) => spine(function, argument :: arguments)
    case other                           => (other, arguments)

  /** A chain's body that is a leaf whose layer is a thunk with holes, as the
    * lambda it is, so that the chain goes on into it, as the front end folds
    * such a body into the chain. Any other value as it is.
    */
  private def enteredLeaf(value: Value): Value = value match
    case Value.Leaf(Instruction.Thunk(code, holes, fillings)) if holes.nonEmpty =>
      Value.Lambda.of(code, holes, fillingEnvironment(holes, fillings.map(Value.Leaf(_))), inlined = false)
    case other => other

  /** What a slot of a body being emitted reads: a binder of the chains
    * around it, or a closed subterm.
    */
  private enum Source:
    case Bound(binder: Int)
    case Closed(instruction: Instruction)

  /** The slots of a body being emitted, numbered by first occurrence in
    * preorder.
    */
  private final case class Slots(sources: Vector[Source], numbers: Map[Source, Int]):
    def slotOf(source: Source): (Int, Slots) =
      numbers.get(source) match
        case Some(slot) => (slot, this)
        case None       => (sources.size, Slots(sources :+ source, numbers.updated(source, sources.size)))

  private object Slots:
    val empty: Slots = Slots(Vector.empty, Map.empty)

  /** An emitted chain: its code, its holes, and what its other slots read in
    * slot order, the binders around it and the closed subterms.
    */
  private final case class Emitted(code: Code, holes: Vector[Hole], fillings: Vector[Source]):
    def free: Vector[Int] = fillings.collect { case Source.Bound(binder) => binder }

  /** The chain of the binders given, then of every lambda at the head of the
    * body, emitted over the body, and the next binder after it.
    */
  private def chainEmitted(binders: Vector[Int], body: Value, nextBinder: Int): TailRec[(Emitted, Int)] =
    tailcall(headReduced(body)).flatMap(reduced =>
      enteredLeaf(reduced) match
        case lambda: Value.Lambda =>
          applied(lambda, Value.Bound(nextBinder)).flatMap(entered =>
            chainEmitted(binders :+ nextBinder, entered, nextBinder + 1)
          )
        case entered =>
          tailcall(bodyEmitted(entered, Slots.empty, nextBinder)).map((code, slots, after) =>
            val chain = binders.toSet
            val holes = binders.map(binder => slots.numbers.get(Source.Bound(binder)).fold(Hole.Ignored)(Hole.Bound(_)))
            val fillings = slots.sources.filter {
              case Source.Bound(binder) => !chain.contains(binder)
              case Source.Closed(_)     => true
            }
            (Emitted(code, holes, fillings), after)
          )
    )

  /** The code of a subterm of a body, and the slots and the next binder after
    * it: a binder its slot; a maximal closed subterm its slot; a lambda an
    * inner chain whose fillings are slots of the body.
    */
  private def bodyEmitted(value: Value, slots: Slots, nextBinder: Int): TailRec[(Code, Slots, Int)] =
    tailcall(headReduced(value)).flatMap(reducedBodyEmitted(_, slots, nextBinder))

  /** `bodyEmitted` of a value whose head is reduced: the function of an
    * application in it has the same head, so it is emitted with no
    * reduction again, and an application spine costs its length once, not
    * once per prefix.
    */
  private def reducedBodyEmitted(reduced: Value, slots: Slots, nextBinder: Int): TailRec[(Code, Slots, Int)] =
    reduced match
      case Value.Bound(binder) =>
        val (slot, after) = slots.slotOf(Source.Bound(binder))
        done((Code.Slot(slot), after, nextBinder))
      case closed if closed.binders.isEmpty =>
        tailcall(reducedClosedInstruction(closed)).map(found =>
          val instruction = found.getOrElse(
            throw IllegalStateException(s"a value that reads no binder is not closed: $closed")
          )
          val (slot, after) = slots.slotOf(Source.Closed(instruction))
          (Code.Slot(slot), after, nextBinder)
        )
      case Value.Apply(function, argument) =>
        tailcall(reducedBodyEmitted(function, slots, nextBinder)).flatMap((functionCode, afterFunction, nextAfterFunction) =>
          tailcall(bodyEmitted(argument, afterFunction, nextAfterFunction)).map((argumentCode, afterArgument, nextAfterArgument) =>
            (Code.Apply(functionCode, argumentCode), afterArgument, nextAfterArgument)
          )
        )
      case Value.Parallel(left, right) =>
        tailcall(bodyEmitted(left, slots, nextBinder)).flatMap((leftCode, afterLeft, nextAfterLeft) =>
          tailcall(bodyEmitted(right, afterLeft, nextAfterLeft)).map((rightCode, afterRight, nextAfterRight) =>
            (Code.Parallel(leftCode, rightCode), afterRight, nextAfterRight)
          )
        )
      case Value.Choice(left, right) =>
        tailcall(bodyEmitted(left, slots, nextBinder)).flatMap((leftCode, afterLeft, nextAfterLeft) =>
          tailcall(bodyEmitted(right, afterLeft, nextAfterLeft)).map((rightCode, afterRight, nextAfterRight) =>
            (Code.Choice(leftCode, rightCode), afterRight, nextAfterRight)
          )
        )
      case lambda: Value.Lambda =>
        applied(lambda, Value.Bound(nextBinder)).flatMap(entered =>
          tailcall(chainEmitted(Vector(nextBinder), entered, nextBinder + 1)).map((inner, afterInner) =>
            val (fillings, after) = inner.fillings.foldLeft((Vector.empty[Code], slots)) { case ((codes, current), source) =>
              val (slot, next) = current.slotOf(source)
              (codes :+ Code.Slot(slot), next)
            }
            (Code.Thunk(inner.code, inner.holes, fillings), after, afterInner)
          )
        )
      case Value.Leaf(instruction) =>
        val (slot, after) = slots.slotOf(Source.Closed(instruction))
        done((Code.Slot(slot), after, nextBinder))

  /** The instruction of a value that reads no binder, nothing for one that
    * does. The binders a closed lambda's chain enters are numbered from 0:
    * the value reads no other.
    */
  private def closedInstruction(value: Value): TailRec[Option[Instruction]] =
    if value.binders.nonEmpty then done(None) else tailcall(headReduced(value)).flatMap(reducedClosedInstruction)

  /** `closedInstruction` of a value whose head is reduced, the function of an
    * application in it read with no reduction again (`reducedBodyEmitted`).
    */
  private def reducedClosedInstruction(reduced: Value): TailRec[Option[Instruction]] =
    if reduced.binders.nonEmpty then done(None)
    else
      reduced match
        case Value.Leaf(instruction) => done(Some(instruction))
        case Value.Apply(function, argument) =>
          both(tailcall(reducedClosedInstruction(function)), closedInstruction(argument))(Instruction.Apply(_, _))
        case Value.Parallel(left, right) =>
          both(tailcall(closedInstruction(left)), closedInstruction(right))(Instruction.Parallel(_, _))
        case Value.Choice(left, right) =>
          both(tailcall(closedInstruction(left)), closedInstruction(right))(Instruction.Choice(_, _))
        case lambda: Value.Lambda =>
          tailcall(chainEmitted(Vector.empty, lambda, 0)).map((emitted, _) =>
            Option.when(emitted.free.isEmpty)(
              Instruction.Thunk(
                emitted.code,
                emitted.holes,
                emitted.fillings.collect { case Source.Closed(instruction) => instruction }
              )
            )
          )
        case Value.Bound(_) => done(None)

  /** The two instructions combined, nothing when either is nothing; the
    * second not computed when the first is nothing.
    */
  private def both(first: TailRec[Option[Instruction]], second: => TailRec[Option[Instruction]])(
      combined: (Instruction, Instruction) => Instruction
  ): TailRec[Option[Instruction]] =
    first.flatMap {
      case None                   => done(None)
      case Some(firstInstruction) => tailcall(second).map(_.map(combined(firstInstruction, _)))
    }
