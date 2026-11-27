package gezi.ir

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The normal form of a lemma's thunk pattern under its bindings, the one
  * function that both the higher-order saturator (`HigherOrderMatching`,
  * project `saturation`) and the trace's conversions (`Conversions`, project
  * `rewrite-trace`) compute, so that a conversion the saturator writes is one
  * the trace's replay computes, and no β conversion of the saturator is left
  * without a proof in the trace. Two implementations of it that were meant to
  * agree spelled one normal form with two codes, and the trace had no command
  * for the saturator's unions (2026-11-16): two implementations that must agree
  * are a defect waiting to recur.
  *
  * What it is: the instance of the pattern under the bindings, with every
  * application of a higher-order metavariable's value reduced by β,
  * hereditarily (a lambda given as an argument to an inlined lambda is inlined
  * in turn), spelled as the front end spells a closed term
  * (`gezi.frontend.Defunctionalization`): a chain of lambdas is one thunk whose
  * holes are its binders, outermost first, a binder the body does not read an
  * ignored hole; the body's slots are numbered by first occurrence in preorder;
  * each maximal subterm that reads no binder around it is one slot, equal
  * subterms one slot, filled by that subterm; an inner lambda is an inner thunk
  * whose fillings are slots of the body, in its own slot order; and a chain's
  * body that is a thunk with holes goes on as the chain.
  *
  * It is a normal form relative to the bindings, not the β-normal form of the
  * whole term: only the higher-order metavariables' values, and lambdas passed
  * to them, are reduced; any other value is a leaf as it is, even a thunk
  * applied to something, and a redex of the pattern's own code that no inlined
  * value makes is kept. Do not "complete" it into full β: the conversions it
  * defines are the instances' equations, and nothing else.
  *
  * A higher-order metavariable's value is entered whatever it is: a thunk with
  * holes is inlined; any other value stays a leaf. A value is a term of the
  * configuration, an opaque one standing for a subterm the caller does not
  * expand (the saturator's graph nodes that are no thunk with holes).
  *
  * Every recursion over a term, a code or a value is a trampoline
  * (`scala.util.control.TailCalls`), so that no function here recurses on the
  * JVM stack once per level of nesting: a term the front end reads back from a
  * printed program nests as deep as the program, and the e-graph respells each
  * thunk it adds (`gezi.egraph.Respelling`); recursing on the stack, a
  * programfamilies `list` item of size 512 overflowed a 1 MB thread stack 2,461
  * frames deep (`BindingNormalFormDepthLawTest`). A trampoline is bound (`map`,
  * `flatMap`) only where it is a `tailcall` or a `done`, never on the result of
  * another bind: `TailCalls` binds a bound trampoline by composing the
  * continuations into one closure, which a recursion that binds each level's
  * result in turn nests one closure per level, so that running it recurses on
  * the stack once per level and costs the square of the depth.
  */
object BindingNormalForm:

  /** The normal form of the thunk pattern under the bindings, the higher-order
    * metavariables' indices given, built through the specializer in scope.
    * Throws `IllegalArgumentException` for a metavariable with no binding, and
    * `IllegalStateException` when the pattern's thunk reads a binder around it
    * (a pattern of a lemma's side is closed).
    */
  def of[C <: NativeSpecializer & Singleton](
      thunk: Pattern.Thunk[C],
      bindings: Map[Int, Configured[C]],
      higherOrder: Set[Int]
  )(using specializer: C): Configured[C] =
    Normalization(specializer).of(thunk, bindings, higherOrder)

  /** A filling of a spelling `respelled` gives, a code over the placeholder
    * slots, folded bottom-up through a state: the slot of position p is
    * `standing(p)`, and every other layer is `made` of the state and its layer
    * over its children's results, the children folded in the order of
    * `children`. The e-graph makes a respelled thunk's fillings with it
    * (`gezi.egraph.Respelling`), a lemma's side is respelled with it
    * (`gezi.orientation.OrientationCompilation`), and an article's pattern
    * (`gezi.proofs.ProofMatching`). A filling holds no leaf but its slots, so a
    * layer `made` gets is never a noinline leaf: its leaf type is `Nothing`. A
    * caller that puts terms in the slots builds the filling's instance through
    * its specializer (`NativeSpecializer.instance`), not by this fold.
    */
  def fillingFolded[State, Result](
      filling: Code,
      standing: Vector[Result],
      state: State
  )(
      made: (State, LayerWith[Result, Nothing]) => (State, Result)
  )(using NotTerm[Result]): (State, Result) =
    def folded(code: Code, current: State): TailRec[(State, Result)] =
      code.layer match
        case Slot(position) =>
          done(
            (
              current,
              standing
                .lift(position)
                .getOrElse(
                  throw IllegalArgumentException(
                    s"the filling's slot $position stands for none of ${standing.size} results"
                  )
                )
            )
          )
        case layer =>
          val children = codeChildren(layer)
          def from(
              index: Int,
              before: State,
              results: Vector[Result]
          ): TailRec[(State, Vector[Result])] =
            if index >= children.size then done((before, results))
            else
              tailcall(folded(children(index), before)).flatMap(
                (next, result) => from(index + 1, next, results :+ result)
              )
          tailcall(from(0, current, Vector.empty)).map((after, results) =>
            made(after, codeLayerOver(layer, results))
          )
    folded(filling, state).result

  /** `fillingFolded` with no state. */
  def fillingMapped[Result](filling: Code, standing: Vector[Result])(
      made: LayerWith[Result, Nothing] => Result
  )(using
      NotTerm[Result]
  ): Result =
    fillingFolded(filling, standing, ())((_, layer) => ((), made(layer)))._2

  /** The front end's spelling of a thunk of the code and holes whose
    * `fillingCount` fillings are opaque placeholders, a function of these alone
    * and of no configuration: nothing when the thunk is its own spelling, else
    * the code, the holes and the fillings it is spelled with, each filling a
    * code over the placeholders' slots, slot p standing for the filling of
    * position p. It is not the front end's spelling of the thunk with its
    * actual fillings (`spelled`) where a placeholder hides what the front end
    * reads: a filling that is a lambda at the body of the chain, which the
    * front end continues the chain through, and equal fillings, which it makes
    * one slot. The e-graph makes its thunk nodes in this spelling
    * (`gezi.egraph.Respelling`), a trace replays in it
    * (`gezi.rewritetrace.ReplaySpelling`), and its Respell equation states it
    * (`Statements.respell`). Throws `IllegalArgumentException` for no hole and
    * `IllegalStateException` when the spelling is no thunk.
    */
  def respelled(
      code: Code,
      holes: Vector[Hole],
      fillingCount: Int
  ): Option[(Code, Vector[Hole], Vector[Code])] =
    val present = NonEmptyHoles
      .of(holes)
      .getOrElse(
        throw IllegalArgumentException(s"a thunk respelled has holes: $code")
      )
    // The spelling is computed over opaque placeholders of no facts, private to this function: a code's leaves are its
    // slots, so every node of the spelling is built from placeholders and the code's own layers, and it comes back as
    // codes over the placeholders' slots, a term of no configuration. Under any configuration the spelling of the
    // thunk with its actual fillings is the instance of these codes (`NativeSpecializer.instance`), since
    // specialization is one-to-one within a configuration and so keeps which subterms are equal.
    val standing = Vector.tabulate(fillingCount)(position =>
      NoFacts.opaque(s"respelling placeholder of filling $position")
    )
    val positions = standing.zipWithIndex.toMap
    given NoFacts.type = NoFacts
    spelled(NoFacts.thunk(code, present, standing)).layer match
      case Thunk(spelledCode, spelledHoles, spelledFillings) =>
        Option.unless(
          spelledCode == code && spelledHoles == holes && spelledFillings == standing
        )(
          (
            spelledCode,
            spelledHoles,
            spelledFillings.map(placeholderCode(_, positions))
          )
        )
      case other =>
        throw IllegalStateException(
          s"the spelling of a thunk with holes is no thunk: $other"
        )

  /** The closed term spelled as the front end spells a closed term, with
    * nothing reduced, built through the specializer in scope: the spelling half
    * of `of`, which the front end's `Defunctionalization.thunkInstruction` is
    * to call. Throws `IllegalArgumentException` for a term that is not closed.
    */
  def spelled[C <: NativeSpecializer & Singleton](term: Configured[C])(using
      specializer: C
  ): Configured[C] =
    Normalization(specializer).spelled(term)

  /** The children of a code's layer that is no slot, in the order of a layer's
    * `children`.
    */
  private def codeChildren(layer: CodeLayer[Code]): Vector[Code] = layer match
    case Apply(function, argument) => Vector(function, argument)
    case Parallel(left, right)     => Vector(left, right)
    case Choice(left, right)       => Vector(left, right)
    case Thunk(_, _, fillings)     => fillings
    case Slot(_)                   => Vector.empty

  /** A code's layer that is no slot over the children's results. */
  private def codeLayerOver[Result](
      layer: CodeLayer[Code],
      results: Vector[Result]
  )(using
      NotTerm[Result]
  ): LayerWith[Result, Nothing] = layer match
    case Apply(_, _) =>
      val Vector(function, argument) = results: @unchecked
      Apply(function, argument)
    case Parallel(_, _) =>
      val Vector(left, right) = results: @unchecked
      Parallel(left, right)
    case Choice(_, _) =>
      val Vector(left, right) = results: @unchecked
      Choice(left, right)
    case Thunk(code, holes, _) => Thunk(code, holes, results)
    case Slot(index)           =>
      throw IllegalStateException(s"a slot $index has no layer over results")

  /** The spelled filling over the placeholders as a code, each placeholder its
    * position's slot; a trampoline, as a filling nests as deep as the code.
    */
  private def placeholderCode(
      filling: Configured[NoFacts.type],
      positions: Map[Configured[NoFacts.type], Int]
  ): Code =
    def converted(term: Configured[NoFacts.type]): TailRec[Code] =
      positions.get(term) match
        case Some(position) => done(Code.Slot(position))
        case None           =>
          term.layer match
            case Apply(function, argument) =>
              tailcall(converted(function)).flatMap(functionCode =>
                tailcall(converted(argument)).map(Code.Apply(functionCode, _))
              )
            case Parallel(left, right) =>
              tailcall(converted(left)).flatMap(leftCode =>
                tailcall(converted(right)).map(Code.Parallel(leftCode, _))
              )
            case Choice(left, right) =>
              tailcall(converted(left)).flatMap(leftCode =>
                tailcall(converted(right)).map(Code.Choice(leftCode, _))
              )
            case Thunk(inner, holes, fillings) =>
              tailcall(traversed(fillings)(converted))
                .map(Code.Thunk(inner, holes, _))
            case other =>
              throw IllegalStateException(
                s"a respelled filling holds the leaf $other, no placeholder"
              )
    converted(filling).result

  /** The results of the step on each item, in order, as a trampoline: each step
    * is bound in the continuation of the one before it, so that no chain of
    * continuations is built before it runs, which a fold of binds from the left
    * would build and then call one inside another.
    */
  private[ir] def traversed[Item, Result](items: Vector[Item])(
      step: Item => TailRec[Result]
  ): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else
        tailcall(step(items(index))).flatMap(result =>
          from(index + 1, results :+ result)
        )
    from(0, Vector.empty)

  /** The normal form's computation in the configuration of one specializer,
    * whose terms are its leaves and which builds the closed terms it emits.
    */
  private final class Normalization[C <: NativeSpecializer & Singleton](
      specializer: C
  ):

    private given C = specializer

    def of(
        thunk: Pattern.Thunk[C],
        bindings: Map[Int, Configured[C]],
        higherOrder: Set[Int]
    ): Configured[C] =
      tailcall(
        traversed(thunk.fillings)(patternValue(_, bindings, higherOrder))
      )
        .flatMap(fillings =>
          closedInstruction(
            Value.Lambda.of(
              thunk.code,
              thunk.holes,
              fillingEnvironment(thunk.holes, fillings),
              inlined = false
            )
          )
        )
        .result
        .getOrElse(
          throw IllegalStateException(
            s"the pattern's thunk reads a binder around it under $bindings"
          )
        )

    def spelled(term: Configured[C]): Configured[C] =
      tailcall(instructionValue(term))
        .flatMap(closedInstruction(_))
        .result
        .getOrElse(
          throw IllegalArgumentException(s"the term is not closed: $term")
        )

    /** The term as a value with nothing inlined: a thunk a lambda over its
      * fillings, one layer over values, an opaque term and a native storage a
      * leaf, its view not read.
      */
    private def instructionValue(term: Configured[C]): TailRec[Value] =
      term.layer match
        case Apply(function, argument) =>
          tailcall(instructionValue(function)).flatMap(functionValue =>
            tailcall(instructionValue(argument)).map(
              Value.Apply(functionValue, _)
            )
          )
        case Parallel(left, right) =>
          tailcall(instructionValue(left)).flatMap(leftValue =>
            tailcall(instructionValue(right)).map(Value.Parallel(leftValue, _))
          )
        case Choice(left, right) =>
          tailcall(instructionValue(left)).flatMap(leftValue =>
            tailcall(instructionValue(right)).map(Value.Choice(leftValue, _))
          )
        case Thunk(code, holes, fillings) =>
          tailcall(traversed(fillings)(instructionValue)).map(values =>
            Value.Lambda.of(
              code,
              holes,
              fillingEnvironment(holes, values),
              inlined = false
            )
          )
        case _ => done(Value.Leaf(term))

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

      final case class Leaf(term: Configured[C]) extends Value:
        val binders: Set[Int] = Set.empty

      final case class Apply(function: Value, argument: Value) extends Value:
        val binders: Set[Int] = function.binders ++ argument.binders

      final case class Parallel(left: Value, right: Value) extends Value:
        val binders: Set[Int] = left.binders ++ right.binders

      final case class Choice(left: Value, right: Value) extends Value:
        val binders: Set[Int] = left.binders ++ right.binders

      /** A lambda, its binders those of its environment's values, which `of`
        * computes and which entering a hole (`applied`) extends by the value it
        * enters.
        */
      final case class Lambda(
          code: Code,
          holes: Vector[Hole],
          environment: Map[Int, Value],
          inlined: Boolean,
          binders: Set[Int]
      ) extends Value

      object Lambda:
        /** The lambda with the binders of its environment's values. */
        def of(
            code: Code,
            holes: Vector[Hole],
            environment: Map[Int, Value],
            inlined: Boolean
        ): Lambda =
          Lambda(
            code,
            holes,
            environment,
            inlined,
            environment.values.foldLeft(Set.empty[Int])(_ ++ _.binders)
          )

    /** The pattern under the bindings: a higher-order metavariable's value
      * inlined wherever it occurs, any other value a leaf, a reference its
      * term, a thunk a lambda over its fillings.
      */
    private def patternValue(
        pattern: Pattern[C],
        bindings: Map[Int, Configured[C]],
        higherOrder: Set[Int]
    ): TailRec[Value] =
      pattern match
        case Pattern.Metavariable(index) =>
          done(bound(index, bindings, higherOrder))
        case Pattern.Closure(index) => done(bound(index, bindings, higherOrder))
        case Pattern.InstructionReference(term) => done(Value.Leaf(term))
        case Pattern.Apply(function, argument)  =>
          tailcall(patternValue(function, bindings, higherOrder)).flatMap(
            functionValue =>
              tailcall(patternValue(argument, bindings, higherOrder)).map(
                Value.Apply(functionValue, _)
              )
          )
        case Pattern.Parallel(left, right) =>
          tailcall(patternValue(left, bindings, higherOrder)).flatMap(
            leftValue =>
              tailcall(patternValue(right, bindings, higherOrder)).map(
                Value.Parallel(leftValue, _)
              )
          )
        case Pattern.Choice(left, right) =>
          tailcall(patternValue(left, bindings, higherOrder)).flatMap(
            leftValue =>
              tailcall(patternValue(right, bindings, higherOrder)).map(
                Value.Choice(leftValue, _)
              )
          )
        case Pattern.Thunk(code, holes, fillings) =>
          tailcall(traversed(fillings)(patternValue(_, bindings, higherOrder)))
            .map(values =>
              Value.Lambda.of(
                code,
                holes,
                fillingEnvironment(holes, values),
                inlined = false
              )
            )

    private def bound(
        index: Int,
        bindings: Map[Int, Configured[C]],
        higherOrder: Set[Int]
    ): Value =
      val value = bindings.getOrElse(
        index,
        throw IllegalArgumentException(
          s"the metavariable $index has no binding"
        )
      )
      if higherOrder.contains(index) then inlinedValue(value)
      else Value.Leaf(value)

    /** A value given to be reduced where applied: a thunk with holes as an
      * inlined lambda, anything else a leaf.
      */
    private def inlinedValue(term: Configured[C]): Value = term.layer match
      case Thunk(code, holes, fillings) if holes.nonEmpty =>
        Value.Lambda.of(
          code,
          holes,
          fillingEnvironment(holes, fillings.map(Value.Leaf(_))),
          inlined = true
        )
      case _ => Value.Leaf(term)

    /** For each slot of a thunk that is no hole, its filling. */
    private def fillingEnvironment[Filling](
        holes: Vector[Hole],
        fillings: Vector[Filling]
    ): Map[Int, Filling] =
      val boundSlots = holes.collect { case Hole.Bound(slot) => slot }.toSet
      val slots =
        (0 until boundSlots.size + fillings.size).filterNot(boundSlots.contains)
      require(
        slots.size == fillings.size,
        s"the fillings $fillings do not fill the slots of $holes"
      )
      slots.zip(fillings).toMap

    /** The code read under the environment of its slots. */
    private def read(code: Code, environment: Map[Int, Value]): TailRec[Value] =
      code.layer match
        case Slot(index) =>
          done(
            environment.getOrElse(
              index,
              throw IllegalStateException(
                s"the slot $index is not in $environment"
              )
            )
          )
        case Apply(function, argument) =>
          tailcall(read(function, environment)).flatMap(functionValue =>
            tailcall(read(argument, environment)).map(
              Value.Apply(functionValue, _)
            )
          )
        case Parallel(left, right) =>
          tailcall(read(left, environment)).flatMap(leftValue =>
            tailcall(read(right, environment)).map(Value.Parallel(leftValue, _))
          )
        case Choice(left, right) =>
          tailcall(read(left, environment)).flatMap(leftValue =>
            tailcall(read(right, environment)).map(Value.Choice(leftValue, _))
          )
        case Thunk(inner, holes, fillings) =>
          tailcall(traversed(fillings)(read(_, environment))).map(values =>
            Value.Lambda.of(
              inner,
              holes,
              fillingEnvironment(holes, values),
              inlined = false
            )
          )

    /** The lambda with its first hole entered by the value: the lambda of the
      * holes left, or its body when none is. A `tailcall` or a `done`, which a
      * caller binds as it is.
      */
    private def applied(lambda: Value.Lambda, value: Value): TailRec[Value] =
      val (environment, binders) = lambda.holes.headOption match
        case Some(Hole.Bound(slot)) if lambda.environment.contains(slot) =>
          val replaced = lambda.environment.updated(slot, value)
          (
            replaced,
            Value.Lambda
              .of(lambda.code, lambda.holes, replaced, lambda.inlined)
              .binders
          )
        case Some(Hole.Bound(slot)) =>
          (
            lambda.environment.updated(slot, value),
            lambda.binders ++ value.binders
          )
        case Some(Hole.Ignored) => (lambda.environment, lambda.binders)
        case None               =>
          throw IllegalStateException(
            s"a lambda with no hole is applied: $lambda"
          )
      if lambda.holes.size == 1 then tailcall(read(lambda.code, environment))
      else
        done(
          lambda.copy(
            holes = lambda.holes.tail,
            environment = environment,
            binders = binders
          )
        )

    /** The value with every application of an inlined lambda at its head
      * reduced by β, a lambda given as an argument to it inlined in turn.
      *
      * FIXME (carried from `HigherOrderMatching.headReduced`, 2026-11-04):
      * https://github.com/Atry/private-overlay/issues/1965 nothing bounds the
      * reduction; a higher-order value that applies a lambda to itself, as
      * `λy. y y` given `λx. x x`, does not end. No lemma of the standard
      * library has such a right side. Candidate fix: a bound on the β steps of
      * one normal form, the instance dropped when it is reached.
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
      * arguments left, from the first the function is no lambda for, applied to
      * what it gives.
      */
    private def argumentsEntered(
        function: Value,
        arguments: List[Value]
    ): TailRec[Value] = (function, arguments) match
      case (entered: Value.Lambda, argument :: rest) =>
        val passed = argument match
          case argumentLambda: Value.Lambda =>
            argumentLambda.copy(inlined = true)
          case other => other
        tailcall(applied(entered, passed)).flatMap(argumentsEntered(_, rest))
      case _ => done(arguments.foldLeft(function)(Value.Apply(_, _)))

    /** The head of an application spine and its arguments in order, the
      * arguments of the applications around the value given after them.
      */
    @scala.annotation.tailrec
    private def spine(
        value: Value,
        arguments: List[Value]
    ): (Value, List[Value]) = value match
      case Value.Apply(function, argument) =>
        spine(function, argument :: arguments)
      case other => (other, arguments)

    /** A chain's body that is a leaf whose layer is a thunk with holes, as the
      * lambda it is, so that the chain goes on into it, as the front end folds
      * such a body into the chain. Any other value as it is.
      */
    private def enteredLeaf(value: Value): Value = value match
      case Value.Leaf(term) =>
        term.layer match
          case Thunk(code, holes, fillings) if holes.nonEmpty =>
            Value.Lambda.of(
              code,
              holes,
              fillingEnvironment(holes, fillings.map(Value.Leaf(_))),
              inlined = false
            )
          case _ => value
      case other => other

    /** What a slot of a body being emitted reads: a binder of the chains around
      * it, or a closed subterm.
      */
    private enum Source:
      case Bound(binder: Int)
      case Closed(term: Configured[C])

    /** The slots of a body being emitted, numbered by first occurrence in
      * preorder.
      */
    private final case class Slots(
        sources: Vector[Source],
        numbers: Map[Source, Int]
    ):
      def slotOf(source: Source): (Int, Slots) =
        numbers.get(source) match
          case Some(slot) => (slot, this)
          case None       =>
            (
              sources.size,
              Slots(sources :+ source, numbers.updated(source, sources.size))
            )

    private object Slots:
      val empty: Slots = Slots(Vector.empty, Map.empty)

    /** An emitted chain: its code, its holes, and what its other slots read in
      * slot order, the binders around it and the closed subterms.
      */
    private final case class Emitted(
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Source]
    ):
      def free: Vector[Int] = fillings.collect { case Source.Bound(binder) =>
        binder
      }

    /** The chain of the binders given, then of every lambda at the head of the
      * body, emitted over the body, and the next binder after it.
      */
    private def chainEmitted(
        binders: Vector[Int],
        body: Value,
        nextBinder: Int
    ): TailRec[(Emitted, Int)] =
      tailcall(headReduced(body)).flatMap(reduced =>
        enteredLeaf(reduced) match
          case lambda: Value.Lambda =>
            applied(lambda, Value.Bound(nextBinder)).flatMap(entered =>
              chainEmitted(binders :+ nextBinder, entered, nextBinder + 1)
            )
          case entered =>
            tailcall(bodyEmitted(entered, Slots.empty, nextBinder)).map(
              (code, slots, after) =>
                val chain = binders.toSet
                val holes = binders.map(binder =>
                  slots.numbers
                    .get(Source.Bound(binder))
                    .fold(Hole.Ignored)(Hole.Bound(_))
                )
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
    private def bodyEmitted(
        value: Value,
        slots: Slots,
        nextBinder: Int
    ): TailRec[(Code, Slots, Int)] =
      tailcall(headReduced(value)).flatMap(
        reducedBodyEmitted(_, slots, nextBinder)
      )

    /** `bodyEmitted` of a value whose head is reduced: the function of an
      * application in it has the same head, so it is emitted with no reduction
      * again, and an application spine costs its length once, not once per
      * prefix.
      */
    private def reducedBodyEmitted(
        reduced: Value,
        slots: Slots,
        nextBinder: Int
    ): TailRec[(Code, Slots, Int)] =
      reduced match
        case Value.Bound(binder) =>
          val (slot, after) = slots.slotOf(Source.Bound(binder))
          done((Code.Slot(slot), after, nextBinder))
        case closed if closed.binders.isEmpty =>
          tailcall(reducedClosedInstruction(closed)).map(found =>
            val term = found.getOrElse(
              throw IllegalStateException(
                s"a value that reads no binder is not closed: $closed"
              )
            )
            val (slot, after) = slots.slotOf(Source.Closed(term))
            (Code.Slot(slot), after, nextBinder)
          )
        case Value.Apply(function, argument) =>
          tailcall(reducedBodyEmitted(function, slots, nextBinder)).flatMap(
            (functionCode, afterFunction, nextAfterFunction) =>
              tailcall(bodyEmitted(argument, afterFunction, nextAfterFunction))
                .map((argumentCode, afterArgument, nextAfterArgument) =>
                  (
                    Code.Apply(functionCode, argumentCode),
                    afterArgument,
                    nextAfterArgument
                  )
                )
          )
        case Value.Parallel(left, right) =>
          tailcall(bodyEmitted(left, slots, nextBinder)).flatMap(
            (leftCode, afterLeft, nextAfterLeft) =>
              tailcall(bodyEmitted(right, afterLeft, nextAfterLeft)).map(
                (rightCode, afterRight, nextAfterRight) =>
                  (
                    Code.Parallel(leftCode, rightCode),
                    afterRight,
                    nextAfterRight
                  )
              )
          )
        case Value.Choice(left, right) =>
          tailcall(bodyEmitted(left, slots, nextBinder)).flatMap(
            (leftCode, afterLeft, nextAfterLeft) =>
              tailcall(bodyEmitted(right, afterLeft, nextAfterLeft)).map(
                (rightCode, afterRight, nextAfterRight) =>
                  (Code.Choice(leftCode, rightCode), afterRight, nextAfterRight)
              )
          )
        case lambda: Value.Lambda =>
          applied(lambda, Value.Bound(nextBinder)).flatMap(entered =>
            tailcall(chainEmitted(Vector(nextBinder), entered, nextBinder + 1))
              .map((inner, afterInner) =>
                val (fillings, after) =
                  inner.fillings.foldLeft((Vector.empty[Code], slots)) {
                    case ((codes, current), source) =>
                      val (slot, next) = current.slotOf(source)
                      (codes :+ Code.Slot(slot), next)
                  }
                (
                  Code.Thunk(inner.code, inner.holes, fillings),
                  after,
                  afterInner
                )
              )
          )
        case Value.Leaf(term) =>
          val (slot, after) = slots.slotOf(Source.Closed(term))
          done((Code.Slot(slot), after, nextBinder))

    /** The term of a value that reads no binder, nothing for one that does. The
      * binders a closed lambda's chain enters are numbered from 0: the value
      * reads no other.
      */
    private def closedInstruction(
        value: Value
    ): TailRec[Option[Configured[C]]] =
      if value.binders.nonEmpty then done(None)
      else tailcall(headReduced(value)).flatMap(reducedClosedInstruction(_))

    /** `closedInstruction` of a value whose head is reduced, the function of an
      * application in it read with no reduction again (`reducedBodyEmitted`).
      */
    private def reducedClosedInstruction(
        reduced: Value
    ): TailRec[Option[Configured[C]]] =
      if reduced.binders.nonEmpty then done(None)
      else
        reduced match
          case Value.Leaf(term)                => done(Some(term))
          case Value.Apply(function, argument) =>
            both(
              tailcall(reducedClosedInstruction(function)),
              closedInstruction(argument)
            )(specializer.application(_, _))
          case Value.Parallel(left, right) =>
            both(tailcall(closedInstruction(left)), closedInstruction(right))(
              specializer.parallel(_, _)
            )
          case Value.Choice(left, right) =>
            both(tailcall(closedInstruction(left)), closedInstruction(right))(
              specializer.choice(_, _)
            )
          case lambda: Value.Lambda =>
            tailcall(chainEmitted(Vector.empty, lambda, 0)).map((emitted, _) =>
              Option.when(emitted.free.isEmpty)(
                specializer.thunk(
                  emitted.code,
                  NonEmptyHoles
                    .of(emitted.holes)
                    .getOrElse(
                      throw IllegalStateException(
                        s"a closed lambda's chain entered no binder: ${emitted.code}"
                      )
                    ),
                  emitted.fillings.collect { case Source.Closed(term) => term }
                )
              )
            )
          case Value.Bound(_) => done(None)

    /** The two terms combined, nothing when either is nothing; the second not
      * computed when the first is nothing.
      */
    private def both(
        first: TailRec[Option[Configured[C]]],
        second: => TailRec[Option[Configured[C]]]
    )(
        combined: (Configured[C], Configured[C]) => Configured[C]
    ): TailRec[Option[Configured[C]]] =
      first.flatMap {
        case None            => done(None)
        case Some(firstTerm) =>
          tailcall(second).map(_.map(combined(firstTerm, _)))
      }
