package gezi.standardlibrary

import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.ChoiceSpine
import gezi.ir.Configured
import gezi.ir.Hole
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.Spine

/** Replaying a definitional lemma by beta and eta steps on the IR, the port of
  * `gezi/tests/lemma_replay.pl`, whose module comment states the method. A
  * lemma whose proof is `λ_c. _c "munit" Suite`, a suite that replays it
  * (`StandardLibraryLemmasTest`), is a consequence of the definitions alone:
  * both sides reach one beta eta normal form once the library names are
  * expanded. This is the one place a lemma is checked by rewriting, since only
  * the steps that are no lemma can be verified by small step rewriting; the
  * compiler and the engine never read a proof.
  *
  *   - The head of the left side, the instruction at its spine head under its
  *     binders, is unfolded to its first instantiation (delta steps, then steps
  *     of the defunctionalized β rule one hole at a time), and every subterm of
  *     the result that is a name's term is written as that name's instruction.
  *   - Every instruction whose term is a thunk is replaced by that term,
  *     recursively; every other instruction stays opaque.
  *   - Both sides are normalised by evaluation and read back to canonical thunk
  *     layers, with eta steps, the slots numbered by first occurrence as the
  *     front end numbers them; each beta and eta step costs one of the budget.
  *
  * The rule reads the IR's layers and no name (the IR knows no fixpoint and no
  * knot). The names are the terms of the library files the caller reads from
  * the tree (`TreeTerms`): the index keeps no library file.
  */
final case class LemmaReplay(
    library: StandardLibrary,
    names: Set[Configured[NoFacts.type]]
):

  private given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  /** The layers of an instruction as extractors, and the instructions built
    * through the specializer of no facts.
    */
  private object Layered:
    object Apply:
      def unapply(
          instruction: NoFactsTerm
      ): Option[(NoFactsTerm, NoFactsTerm)] = instruction.layer match
        case gezi.ir.Apply(function, argument) => Some((function, argument))
        case _                                 => None
    object Choice:
      def unapply(
          instruction: NoFactsTerm
      ): Option[(NoFactsTerm, NoFactsTerm)] = instruction.layer match
        case gezi.ir.Choice(left, right) => Some((left, right))
        case _                           => None
    object Parallel:
      def unapply(
          instruction: NoFactsTerm
      ): Option[(NoFactsTerm, NoFactsTerm)] = instruction.layer match
        case gezi.ir.Parallel(left, right) => Some((left, right))
        case _                             => None
    object Thunk:
      def unapply(
          instruction: NoFactsTerm
      ): Option[(Code, Vector[Hole], Vector[NoFactsTerm])] =
        instruction.layer match
          case gezi.ir.Thunk(code, holes, fillings) =>
            Some((code, holes, fillings))
          case _ => None

  /** The thunk of the code with its holes and fillings, or, all its holes
    * filled, the instance of its code, a thunk of no hole being no term of the
    * IR.
    */
  private def thunkOf(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[NoFactsTerm]
  ): NoFactsTerm =
    NoFacts.thunkOrInstance(code, holes, fillings)

  /** The beta and eta steps one side may take; past it the replay throws. The
    * most the two sides of a replayed lemma of prelude or guard_laws take
    * together is 23 steps, at natural_equal_successor_successor (measured
    * 2026-10-04 on the Prolog replay); the replayed lemmas of generic_types
    * take at most 397, and those of generic_fold at most 156.
    */
  val budget: Int = 10000

  /** The normal forms of the two sides of the lemma, the left's head unfolded
    * first, and the beta and eta steps the two took together.
    */
  def sidesNormalised(name: String): (NoFactsTerm, NoFactsTerm, Int) =
    val sides = library.index
      .sides(library.index.lemmaIdentifier(name))
      .getOrElse(throw IllegalArgumentException(s"$name has no sides"))
    // When both sides open with a binder, a side is read by its layer at its
    // root, though its instruction be a name; otherwise a side is read as a
    // name when it is one. An unfolded head is folded, so a name's term
    // there is the name.
    val literal = opensWithBinder(sides.left) && opensWithBinder(sides.right)
    val (unfolded, unfoldingSteps) = headUnfolded(sides.left, 0, literal)
    val unfoldedLiteral = Configured.same(unfolded, sides.left) && literal
    val (leftNormal, leftSteps) =
      canonicalNormal(unfolded, unfoldingSteps, unfoldedLiteral)
    val (rightNormal, rightSteps) = canonicalNormal(sides.right, 0, literal)
    (leftNormal, rightNormal, leftSteps + rightSteps)

  /** The normal form both sides of the lemma reach, if they reach one. */
  def replayed(name: String): Option[NoFactsTerm] =
    val (left, right, _) = sidesNormalised(name)
    Option.when(Configured.same(left, right))(left)

  /** The side is a thunk with at least one hole. */
  private def opensWithBinder(side: NoFactsTerm): Boolean = side match
    case Layered.Thunk(_, holes, _) => holes.nonEmpty
    case _                          => false

  // ---- steps ----

  private def counted(steps: Int): Int =
    if steps < budget then steps + 1
    else throw IllegalStateException(s"lemma_replay_budget_exceeded($budget)")

  // ---- the head ----

  /** The instruction at the spine head under the leading binders replaced by
    * its first instantiation, folded, when it has one; any other instruction
    * unchanged. Only the head's own term is unfolded. `literal` when the
    * instruction is read by its layer though it be a name.
    */
  private def headUnfolded(
      instruction: NoFactsTerm,
      steps: Int,
      literal: Boolean
  ): (NoFactsTerm, Int) =
    instruction match
      case name if !literal && names.contains(name) =>
        headInstantiated(name, Vector.empty, steps, literal = false) match
          case Some((instantiated, after)) => (instantiated, after)
          case None                        => (instruction, steps)
      case Layered.Apply(function, argument) =>
        val (unfolded, after) = headUnfolded(function, steps, literal = false)
        (NoFacts.application(unfolded, argument), after)
      case Layered.Thunk(code, holes, fillings) =>
        Spine.of(code)._1 match
          case Code.Slot(slot) if !holes.contains(Hole.Bound(slot)) =>
            val position = Defunctionalization.fillingPosition(holes, slot)
            val (unfolded, after) =
              headUnfolded(fillings(position), steps, literal = false)
            (thunkOf(code, holes, fillings.updated(position, unfolded)), after)
          case _ => (instruction, steps)
      case _ => (instruction, steps)

  /** The head and the arguments of the spine, a name a head. */
  private def spine(
      instruction: NoFactsTerm
  ): (NoFactsTerm, Vector[NoFactsTerm]) =
    instruction match
      case Layered.Apply(function, argument) if !names.contains(instruction) =>
        val (head, arguments) = spine(function)
        (head, arguments :+ argument)
      case other => (other, Vector.empty)

  /** The spine of the head applied to the arguments, its head replaced by its
    * term while it is a name (delta steps; `literal` when the head is a name's
    * term, read by its layer), and the thunk then at the head applied to the
    * arguments one hole at a time until its body is instantiated; nothing when
    * the head comes to no thunk, or to a thunk with more holes than there are
    * arguments.
    */
  private def headInstantiated(
      head: NoFactsTerm,
      arguments: Vector[NoFactsTerm],
      steps: Int,
      literal: Boolean
  ): Option[(NoFactsTerm, Int)] = head match
    case name if !literal && names.contains(name) =>
      name match
        case Layered.Apply(function, argument) =>
          val (innerHead, inner) = spine(function)
          headInstantiated(
            innerHead,
            (inner :+ argument) ++ arguments,
            steps,
            literal = false
          )
        case _ => headInstantiated(name, arguments, steps, literal = true)
    case Layered.Thunk(code, holes, fillings)
        if holes.nonEmpty && holes.size <= arguments.size =>
      val (taken, remaining) = arguments.splitAt(holes.size)
      val initial = slotValues(holes, fillings.map(Some(_)))
      val (slots, after) = holes.zip(taken).foldLeft((initial, steps)) {
        case ((current, count), (hole, argument)) =>
          (filled(current, hole, argument), counted(count))
      }
      val body = codeInstantiated(
        code,
        slots.map(_.getOrElse(throw IllegalStateException("a hole left")))
      )
      Some((remaining.foldLeft(body)(NoFacts.application(_, _)), after))
    case _ => None

  private def filled[Value](
      slots: Vector[Option[Value]],
      hole: Hole,
      value: Value
  ): Vector[Option[Value]] =
    hole match
      case Hole.Ignored     => slots
      case Hole.Bound(slot) => slots.updated(slot, Some(value))

  /** The values by slot, nothing at each hole's slot and the fillings in order
    * at the others.
    */
  private def slotValues[Value](
      holes: Vector[Hole],
      fillings: Vector[Option[Value]]
  ): Vector[Option[Value]] =
    Defunctionalization.slotValues(holes, holes.map(_ => None), fillings)

  /** A thunk body with each slot replaced by the instruction of that slot. */
  private def codeInstantiated(
      code: Code,
      slots: Vector[NoFactsTerm]
  ): NoFactsTerm = code match
    case Code.Slot(index)               => slots(index)
    case Code.Apply(function, argument) =>
      NoFacts.application(
        codeInstantiated(function, slots),
        codeInstantiated(argument, slots)
      )
    case Code.Parallel(left, right) =>
      NoFacts.parallel(
        codeInstantiated(left, slots),
        codeInstantiated(right, slots)
      )
    case Code.Choice(left, right) =>
      NoFacts.choice(
        codeInstantiated(left, slots),
        codeInstantiated(right, slots)
      )
    case Code.Thunk(inner, holes, references) =>
      thunkOf(inner, holes, references.map(codeInstantiated(_, slots)))

  /** The names whose term is no thunk, which the evaluation keeps opaque; every
    * other instruction, a name whose term is a thunk included, is read by its
    * layer.
    */
  private lazy val opaqueNames: Set[NoFactsTerm] = names.filter {
    case Layered.Thunk(_, _, _) => false
    case _                      => true
  }

  // ---- normalisation by evaluation ----

  /** The head of a neutral value: an opaque instruction, a variable, or a stuck
    * choice or parallel.
    */
  private enum Head:
    case Opaque(instruction: NoFactsTerm)
    case Variable(level: Int)
    case Stuck(value: Value)

  /** A value: a thunk with its remaining holes and its slots, nothing at the
    * unfilled ones; a neutral value; a choice, of two members; a parallel.
    */
  private enum Value:
    case ThunkValue(
        code: Code,
        holes: Vector[Hole],
        slots: Vector[Option[Value]]
    )
    case Neutral(head: Head, arguments: Vector[Value])
    case ChoiceValue(values: Vector[Value])
    case ParallelValue(left: Value, right: Value)

  /** An instruction read back under binders, open: a variable of binder L (from
    * 0, outermost first) is a level until the chain that binds it is numbered.
    */
  private enum Open:
    case Level(level: Int)
    case Reference(instruction: NoFactsTerm)
    case Apply(function: Open, argument: Open)
    case Choice(members: Vector[Open])
    case Parallel(left: Open, right: Open)
    case Thunk(code: Code, holes: Vector[Hole], fillings: Vector[Open])

  /** The beta eta normal form of a closed instruction: evaluated, then read
    * back; `literal` when its root is read by its layer though it be a name.
    */
  private def canonicalNormal(
      instruction: NoFactsTerm,
      steps: Int,
      literal: Boolean
  ): (NoFactsTerm, Int) =
    val (value, afterEvaluation) = evaluated(instruction, steps, literal)
    val (open, afterReadBack) = readBack(value, 0, afterEvaluation)
    (closed(open), afterReadBack)

  private def evaluated(
      instruction: NoFactsTerm,
      afterSteps: Int
  ): (Value, Int) =
    evaluated(instruction, afterSteps, literal = false)

  private def evaluated(
      instruction: NoFactsTerm,
      afterSteps: Int,
      literal: Boolean
  ): (Value, Int) = instruction match
    case name if name.opaque || (!literal && opaqueNames.contains(name)) =>
      (Value.Neutral(Head.Opaque(name), Vector.empty), afterSteps)
    case Layered.Apply(function, argument) =>
      val (functionValue, afterFunction) = evaluated(function, afterSteps)
      val (argumentValue, afterArgument) = evaluated(argument, afterFunction)
      applied(functionValue, argumentValue, afterArgument)
    case Layered.Thunk(code, holes, fillings) =>
      val (values, after) = allEvaluated(fillings, afterSteps)(evaluated)
      (
        Value.ThunkValue(code, holes, slotValues(holes, values.map(Some(_)))),
        after
      )
    case Layered.Choice(left, right) =>
      val (values, after) =
        allEvaluated(Vector(left, right), afterSteps)(evaluated)
      (Value.ChoiceValue(values), after)
    case Layered.Parallel(left, right) =>
      val (leftValue, afterLeft) = evaluated(left, afterSteps)
      val (rightValue, afterRight) = evaluated(right, afterLeft)
      (Value.ParallelValue(leftValue, rightValue), afterRight)

  private def codeEvaluated(
      code: Code,
      slots: Vector[Option[Value]],
      steps: Int
  ): (Value, Int) =
    code match
      case Code.Slot(index) =>
        (
          slots(index).getOrElse(
            throw IllegalStateException(s"slot $index is a hole")
          ),
          steps
        )
      case Code.Apply(function, argument) =>
        val (functionValue, afterFunction) =
          codeEvaluated(function, slots, steps)
        val (argumentValue, afterArgument) =
          codeEvaluated(argument, slots, afterFunction)
        applied(functionValue, argumentValue, afterArgument)
      case Code.Thunk(inner, holes, references) =>
        val (values, after) =
          allEvaluated(references, steps)(codeEvaluated(_, slots, _))
        (
          Value.ThunkValue(
            inner,
            holes,
            slotValues(holes, values.map(Some(_)))
          ),
          after
        )
      case Code.Choice(left, right) =>
        val (values, after) =
          allEvaluated(Vector(left, right), steps)(codeEvaluated(_, slots, _))
        (Value.ChoiceValue(values), after)
      case Code.Parallel(left, right) =>
        val (leftValue, afterLeft) = codeEvaluated(left, slots, steps)
        val (rightValue, afterRight) = codeEvaluated(right, slots, afterLeft)
        (Value.ParallelValue(leftValue, rightValue), afterRight)

  private def allEvaluated[Item](items: Vector[Item], steps: Int)(
      evaluate: (Item, Int) => (Value, Int)
  ): (Vector[Value], Int) =
    items.foldLeft((Vector.empty[Value], steps)) {
      case ((values, current), item) =>
        val (value, after) = evaluate(item, current)
        (values :+ value, after)
    }

  /** A thunk value fills its first hole, and evaluates its body when that was
    * the last; a neutral value grows; a choice or parallel value is stuck.
    */
  private def applied(
      function: Value,
      argument: Value,
      steps: Int
  ): (Value, Int) = function match
    case Value.ThunkValue(code, hole +: holes, slots) =>
      val after = counted(steps)
      val filledSlots = filled(slots, hole, argument)
      if holes.isEmpty then codeEvaluated(code, filledSlots, after)
      else (Value.ThunkValue(code, holes, filledSlots), after)
    case Value.ThunkValue(_, _, _) =>
      throw IllegalStateException("a thunk value with no hole")
    case Value.Neutral(head, arguments) =>
      (Value.Neutral(head, arguments :+ argument), steps)
    case stuck => (Value.Neutral(Head.Stuck(stuck), Vector(argument)), steps)

  // ---- readback ----

  private def readBack(value: Value, depth: Int, steps: Int): (Open, Int) =
    value match
      case Value.Neutral(head, arguments) =>
        val (headOpen, afterHead) = head match
          case Head.Opaque(instruction) => (Open.Reference(instruction), steps)
          case Head.Variable(level)     => (Open.Level(level), steps)
          case Head.Stuck(stuck)        => readBack(stuck, depth, steps)
        arguments.foldLeft((headOpen, afterHead)) {
          case ((function, current), argument) =>
            val (argumentOpen, after) = readBack(argument, depth, current)
            (Open.Apply(function, argumentOpen), after)
        }
      case Value.ChoiceValue(values) =>
        val (opens, after) = values.foldLeft((Vector.empty[Open], steps)) {
          case ((done, current), member) =>
            val (open, next) = readBack(member, depth, current)
            (done :+ open, next)
        }
        (Open.Choice(opens), after)
      case Value.ParallelValue(left, right) =>
        val (leftOpen, afterLeft) = readBack(left, depth, steps)
        val (rightOpen, afterRight) = readBack(right, depth, afterLeft)
        (Open.Parallel(leftOpen, rightOpen), afterRight)
      case thunk @ Value.ThunkValue(_, _, _) =>
        val (count, body, afterOpening) = chainOpened(thunk, depth, 0, steps)
        val (bodyOpen, afterBody) = readBack(body, depth + count, afterOpening)
        val (contracted, remaining, afterContraction) =
          etaContracted(bodyOpen, depth, count, afterBody)
        if remaining == 0 then (contracted, afterContraction)
        else (chainNumbered(contracted, depth, remaining), afterContraction)

  /** The thunk value applied to the variables of the levels from
    * `depth + count`, hole by hole, and again while its body is a thunk value;
    * the binders in all, and the value of the innermost body.
    */
  @scala.annotation.tailrec
  private def chainOpened(
      value: Value,
      depth: Int,
      count: Int,
      steps: Int
  ): (Int, Value, Int) =
    value match
      case Value.ThunkValue(_, _ +: _, _) =>
        val (next, after) = applied(
          value,
          Value.Neutral(Head.Variable(depth + count), Vector.empty),
          steps
        )
        chainOpened(next, depth, count + 1, after)
      case other => (count, other, steps)

  /** The innermost binders dropped while the body is `F x` with x the innermost
    * binder not occurring in F, each an eta step.
    */
  @scala.annotation.tailrec
  private def etaContracted(
      body: Open,
      depth: Int,
      count: Int,
      steps: Int
  ): (Open, Int, Int) =
    body match
      case Open.Apply(function, Open.Level(level))
          if count > 0 && level == depth + count - 1 && !levelIn(
            function,
            level
          ) =>
        etaContracted(function, depth, count - 1, counted(steps))
      case _ => (body, count, steps)

  private def levelIn(open: Open, level: Int): Boolean = open match
    case Open.Level(found)              => found == level
    case Open.Reference(_)              => false
    case Open.Apply(function, argument) =>
      levelIn(function, level) || levelIn(argument, level)
    case Open.Choice(members)       => members.exists(levelIn(_, level))
    case Open.Parallel(left, right) =>
      levelIn(left, level) || levelIn(right, level)
    case Open.Thunk(_, _, fillings) => fillings.exists(levelIn(_, level))

  private def hasLevel(open: Open): Boolean = open match
    case Open.Level(_)                  => true
    case Open.Reference(_)              => false
    case Open.Apply(function, argument) =>
      hasLevel(function) || hasLevel(argument)
    case Open.Choice(members)       => members.exists(hasLevel)
    case Open.Parallel(left, right) => hasLevel(left) || hasLevel(right)
    case Open.Thunk(_, _, fillings) => fillings.exists(hasLevel)

  /** What a slot of a chain being numbered stands for: a binder of the chain, a
    * variable of an outer chain, or a closed subterm.
    */
  private enum Source:
    case Bound(level: Int)
    case Free(level: Int)
    case Closed(term: Open)

  /** The thunk layer of the chain of `count` binders at the levels from `depth`
    * over the body, the slots numbered by first occurrence in preorder, as
    * `Defunctionalization.thunkInstruction` numbers a chain.
    */
  private def chainNumbered(body: Open, depth: Int, count: Int): Open =
    val (code, slots) = bodyNumbered(body, depth, count, Vector.empty)
    val holes = (depth until depth + count).toVector.map(level =>
      slots.indexOf(Source.Bound(level)) match
        case -1   => Hole.Ignored
        case slot => Hole.Bound(slot)
    )
    val fillings = slots.collect {
      case Source.Closed(term) => term
      case Source.Free(level)  => Open.Level(level)
    }
    Open.Thunk(code, holes, fillings)

  private def bodyNumbered(
      open: Open,
      depth: Int,
      count: Int,
      slots: Vector[Source]
  ): (Code, Vector[Source]) = open match
    case Open.Level(level)    => slotOf(levelSource(level, depth, count), slots)
    case _ if !hasLevel(open) => slotOf(Source.Closed(open), slots)
    case Open.Apply(function, argument) =>
      val (functionCode, afterFunction) =
        bodyNumbered(function, depth, count, slots)
      val (argumentCode, afterArgument) =
        bodyNumbered(argument, depth, count, afterFunction)
      (Code.Apply(functionCode, argumentCode), afterArgument)
    case Open.Choice(members) =>
      val (codes, after) = members.foldLeft((Vector.empty[Code], slots)) {
        case ((done, current), member) =>
          val (code, next) = bodyNumbered(member, depth, count, current)
          (done :+ code, next)
      }
      // A choice of no member has no level, so it is a closed slot above.
      (Code.Choice.nested(codes), after)
    case Open.Parallel(left, right) =>
      val (leftCode, afterLeft) = bodyNumbered(left, depth, count, slots)
      val (rightCode, afterRight) = bodyNumbered(right, depth, count, afterLeft)
      (Code.Parallel(leftCode, rightCode), afterRight)
    case Open.Thunk(code, holes, fillings) =>
      val (references, after) = fillings.foldLeft((Vector.empty[Code], slots)) {
        case ((done, current), filling) =>
          val source = filling match
            case Open.Level(level) => levelSource(level, depth, count)
            case closedFilling     => Source.Closed(closedFilling)
          val (reference, next) = slotOf(source, current)
          (done :+ reference, next)
      }
      (Code.Thunk(code, holes, references), after)
    case Open.Reference(_) => slotOf(Source.Closed(open), slots)

  private def levelSource(level: Int, depth: Int, count: Int): Source =
    if level >= depth && level < depth + count then Source.Bound(level)
    else if level < depth then Source.Free(level)
    else
      throw IllegalStateException(
        s"level_below_its_binder($level, $depth, $count)"
      )

  private def slotOf(
      source: Source,
      slots: Vector[Source]
  ): (Code, Vector[Source]) =
    slots.indexOf(source) match
      case -1    => (Code.Slot(slots.size), slots :+ source)
      case index => (Code.Slot(index), slots)

  /** The instruction of a choice of no member: top (`Literals.top`), the term
    * of no answer, the choice being binary.
    */
  private lazy val noAnswer: NoFactsTerm =
    Defunctionalization.thunkInstruction[NoFacts.type](
      gezi.frontend.Literals.top
    )

  /** The instruction of an open term with no level. */
  private def closed(open: Open): NoFactsTerm = open match
    case Open.Level(level) =>
      throw IllegalStateException(s"open_normal_form: level $level is free")
    case Open.Reference(instruction)    => instruction
    case Open.Apply(function, argument) =>
      NoFacts.application(closed(function), closed(argument))
    case Open.Choice(members) =>
      if members.isEmpty then noAnswer
      else
        ChoiceSpine
          .nested[NoFactsTerm](members.map(closed), NoFacts.choice(_, _))
    case Open.Parallel(left, right) =>
      NoFacts.parallel(closed(left), closed(right))
    case Open.Thunk(code, holes, fillings) =>
      thunkOf(code, holes, fillings.map(closed))
