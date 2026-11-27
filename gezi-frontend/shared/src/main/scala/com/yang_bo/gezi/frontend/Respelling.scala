package com.yang_bo.gezi.frontend

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NonEmptyHoles
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The instruction the front end gives for the term of a closed instruction,
  * computed on the IR: `thunkInstruction` of the instruction's term, each
  * instruction of the names and each opaque instruction read as a constant,
  * with no de Bruijn tree in between (`CONTRIBUTING.md`, "Types live only in
  * the term": after the front end no module is a de Bruijn tree). A closed
  * instruction is respelled once and its respelling reused wherever it occurs,
  * so the work is linear in the instruction as a graph, not in its term written
  * out as a tree, which shares nothing. The tree path this replaced, a readback
  * to the de Bruijn term and its conversion, made the readback of an in-tree
  * entry's round some 720,000 nodes after literals became variable arguments (a
  * byte about 34 nodes of the tree), and ran it out of a 256 MB heap (a scratch
  * probe, 2026-11-12); the respelling agreed with it on 300 generated inputs
  * before it was deleted (`RespellingSnapshotTest`).
  *
  * A thunk's body is walked as its open spine: each slot of its code reads the
  * variable of a binder, numbered by its level, the count of binders above it
  * from the closed thunk, or the respelling of a filling; a part of the code
  * that reads no variable is one closed instruction, built from the respellings
  * of its parts. The spine is then converted as `Defunctionalization` converts
  * a body: its maximal closed parts and its variables take slots in order of
  * first occurrence in preorder, equal closed parts one slot; a chain of nested
  * abstractions is one thunk; a chain whose body is a thunk with holes is
  * folded into that thunk. Two closed parts are one slot when their respellings
  * are one instruction, which holds when their terms are equal.
  *
  * The codes are the front end's: an inner thunk of a code reads, as its
  * fillings, slots of the enclosing body (`Defunctionalization`, the
  * conversion's inner chains); the evaluator keeps a thunk's code as it is
  * (`com.yang_bo.gezi.weakhead.Values.instruction`).
  */
object Respelling:

  /** The respelling of the closed instruction, each instruction of the names
    * and each opaque instruction kept as it is. Throws as `respelledCounted`
    * does.
    */
  def respelled[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      names: Set[Configured[C]]
  )(using
      specializer: C
  ): Configured[C] =
    respelledCounted(instruction, names).value

  /** `respelled` with the count of its operations: one for each instruction
    * looked up (a repeated one found in the respellings made so far counts
    * one), one for each node of an open spine built, and one for each node a
    * spine's conversion visits. Throws `LambdaError` with `SlotOutOfRange` for
    * a code that reads a slot its thunk does not have, with
    * `FillingsNotMatched` when a thunk's fillings are not its non-hole slots,
    * and `IllegalArgumentException` for an inner thunk whose filling is no slot
    * of the enclosing body, a code the front end does not make.
    */
  def respelledCounted[C <: NativeSpecializer & Singleton](
      instruction: Configured[C],
      names: Set[Configured[C]]
  )(using
      specializer: C
  ): Counted[Configured[C]] =
    Respeller[C](specializer).respelledCounted(instruction, names)

  /** The respelling of the terms of one configuration, built through its
    * specializer. A storage is a leaf the respelling keeps as it is, as it
    * keeps an opaque term.
    */
  private final class Respeller[C <: NativeSpecializer & Singleton](
      specializer: C
  ):

    def respelledCounted(
        instruction: Configured[C],
        names: Set[Configured[C]]
    ): Counted[Configured[C]] =
      val (result, state) = respelledIn(instruction, names, State.empty).result
      Counted(result, state.operations)

    /** The respellings made so far, by instruction, and the operations counted.
      */
    private final case class State(
        respellings: Map[Configured[C], Configured[C]],
        operations: Long
    ):
      def counted(more: Long): State = copy(operations = operations + more)

    private object State:
      val empty: State = State(Map.empty, 0)

    /** A node of a thunk body's open spine: a binder's variable by its level, a
      * closed part by its respelling, or a node over open parts, each with the
      * levels of the variables free under it.
      */
    private enum Spine:
      def free: Set[Int]
      case Variable(level: Int, free: Set[Int])
      case Closed(instruction: Configured[C], free: Set[Int])
      case Apply(function: Spine, argument: Spine, free: Set[Int])
      case Choice(left: Spine, right: Spine, free: Set[Int])
      case Parallel(left: Spine, right: Spine, free: Set[Int])

      /** A chain of `count` abstractions binding the levels from `firstLevel`,
        * its body no abstraction, under which a variable of a level below
        * `firstLevel` is free.
        */
      case Lambda(firstLevel: Int, count: Int, body: Spine, free: Set[Int])

    private def variable(level: Int): Spine = Spine.Variable(level, Set(level))

    private def closed(instruction: Configured[C]): Spine =
      Spine.Closed(instruction, Set.empty)

    private def respelledIn(
        instruction: Configured[C],
        names: Set[Configured[C]],
        entered: State
    ): TailRec[(Configured[C], State)] =
      val state = entered.counted(1)
      state.respellings.get(instruction) match
        case Some(found) => done((found, state))
        case None if instruction.heldAsLeaf || names.contains(instruction) =>
          done((instruction, state))
        case None =>
          val made: TailRec[(Configured[C], State)] = instruction.layer match
            case com.yang_bo.gezi.ir.Apply(function, argument) =>
              for
                (functionRespelled, afterFunction) <- tailcall(
                  respelledIn(function, names, state)
                )
                (argumentRespelled, afterArgument) <- tailcall(
                  respelledIn(argument, names, afterFunction)
                )
              yield (
                specializer.application(functionRespelled, argumentRespelled),
                afterArgument
              )
            case com.yang_bo.gezi.ir.Choice(left, right) =>
              for
                (leftRespelled, afterLeft) <- tailcall(
                  respelledIn(left, names, state)
                )
                (rightRespelled, afterRight) <- tailcall(
                  respelledIn(right, names, afterLeft)
                )
              yield (
                specializer.choice(leftRespelled, rightRespelled),
                afterRight
              )
            case com.yang_bo.gezi.ir.Parallel(left, right) =>
              for
                (leftRespelled, afterLeft) <- tailcall(
                  respelledIn(left, names, state)
                )
                (rightRespelled, afterRight) <- tailcall(
                  respelledIn(right, names, afterLeft)
                )
              yield (
                specializer.parallel(leftRespelled, rightRespelled),
                afterRight
              )
            case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) =>
              for
                (fillingsRespelled, afterFillings) <- Trampoline.threaded(
                  fillings,
                  state
                )((filling, current) =>
                  tailcall(respelledIn(filling, names, current))
                )
                slots = Defunctionalization.slotValues(
                  holes,
                  holes.indices.toVector.map(variable),
                  fillingsRespelled.map(closed)
                )
                (body, afterBody) <- tailcall(
                  spineOf(code, slots, holes.size, names, afterFillings)
                )
                (chain, afterChain) <- tailcall(
                  abstracted(0, holes.size, body, names, afterBody)
                )
              yield chain match
                case Spine.Closed(respelling, _) => (respelling, afterChain)
                case other                       =>
                  throw IllegalStateException(
                    s"a closed thunk's chain reads the levels ${other.free} outside it"
                  )
            case other =>
              throw IllegalStateException(
                s"$other is neither a leaf nor a layer of the IR"
              )
          made.map((respelling, after) =>
            (
              respelling,
              after.copy(respellings =
                after.respellings.updated(instruction, respelling)
              )
            )
          )

    /** The open spine of a code at `depth` binders, each slot reading what
      * `slots` holds at its index.
      */
    private def spineOf(
        code: Code,
        slots: Vector[Spine],
        depth: Int,
        names: Set[Configured[C]],
        entered: State
    ): TailRec[(Spine, State)] =
      val state = entered.counted(1)
      code match
        case Code.Slot(index) =>
          if index >= 0 && index < slots.size then done((slots(index), state))
          else
            throw LambdaError(
              LambdaErrorReason.SlotOutOfRange(index, slots.size)
            )
        case Code.Apply(function, argument) =>
          for
            (functionSpine, afterFunction) <- tailcall(
              spineOf(function, slots, depth, names, state)
            )
            (argumentSpine, afterArgument) <- tailcall(
              spineOf(argument, slots, depth, names, afterFunction)
            )
          yield (functionSpine, argumentSpine) match
            case (
                  Spine.Closed(functionClosed, _),
                  Spine.Closed(argumentClosed, _)
                ) =>
              (
                closed(specializer.application(functionClosed, argumentClosed)),
                afterArgument
              )
            case _ =>
              (
                Spine.Apply(
                  functionSpine,
                  argumentSpine,
                  functionSpine.free ++ argumentSpine.free
                ),
                afterArgument
              )
        case Code.Choice(left, right) =>
          for
            (leftSpine, afterLeft) <- tailcall(
              spineOf(left, slots, depth, names, state)
            )
            (rightSpine, afterRight) <- tailcall(
              spineOf(right, slots, depth, names, afterLeft)
            )
          yield (leftSpine, rightSpine) match
            case (Spine.Closed(leftClosed, _), Spine.Closed(rightClosed, _)) =>
              (closed(specializer.choice(leftClosed, rightClosed)), afterRight)
            case _ =>
              (
                Spine.Choice(
                  leftSpine,
                  rightSpine,
                  leftSpine.free ++ rightSpine.free
                ),
                afterRight
              )
        case Code.Parallel(left, right) =>
          for
            (leftSpine, afterLeft) <- tailcall(
              spineOf(left, slots, depth, names, state)
            )
            (rightSpine, afterRight) <- tailcall(
              spineOf(right, slots, depth, names, afterLeft)
            )
          yield (leftSpine, rightSpine) match
            case (Spine.Closed(leftClosed, _), Spine.Closed(rightClosed, _)) =>
              (
                closed(specializer.parallel(leftClosed, rightClosed)),
                afterRight
              )
            case _ =>
              (
                Spine.Parallel(
                  leftSpine,
                  rightSpine,
                  leftSpine.free ++ rightSpine.free
                ),
                afterRight
              )
        case Code.Thunk(inner, holes, fillings) =>
          val innerFillings = fillings.map {
            case Code.Slot(index) =>
              if index >= 0 && index < slots.size then slots(index)
              else
                throw LambdaError(
                  LambdaErrorReason.SlotOutOfRange(index, slots.size)
                )
            case other =>
              throw IllegalArgumentException(
                s"an inner thunk's filling is a slot of the enclosing body, not $other"
              )
          }
          val innerSlots =
            Defunctionalization.slotValues(
              holes,
              holes.indices.toVector.map(position =>
                variable(depth + position)
              ),
              innerFillings
            )
          for
            (body, afterBody) <- tailcall(
              spineOf(inner, innerSlots, depth + holes.size, names, state)
            )
            abstraction <- tailcall(
              abstracted(depth, holes.size, body, names, afterBody)
            )
          yield abstraction

    /** The chain of `count` abstractions binding the levels from `firstLevel`
      * over the body, a chain directly under it joined to it: the closed
      * instruction of the chain when nothing outside it is free under it
      * (`chainConfigured[C]`), its open spine otherwise.
      */
    private def abstracted(
        firstLevel: Int,
        count: Int,
        body: Spine,
        names: Set[Configured[C]],
        state: State
    ): TailRec[(Spine, State)] =
      val (chainCount, chainBody) = body match
        case Spine.Lambda(innerFirst, innerCount, innerBody, _) =>
          assert(
            innerFirst == firstLevel + count,
            s"a chain directly under one of levels from $firstLevel binds from $innerFirst"
          )
          (count + innerCount, innerBody)
        case _ => (count, body)
      val free = chainBody.free.filter(level =>
        level < firstLevel || level >= firstLevel + chainCount
      )
      if free.isEmpty then
        chainConfigured(firstLevel, chainCount, chainBody, names, state).map(
          (instruction, after) => (closed(instruction), after)
        )
      else done((Spine.Lambda(firstLevel, chainCount, chainBody, free), state))

    /** The thunk of a closed chain of `count` abstractions binding the levels
      * from `firstLevel` over the body, no abstraction: folded into the body
      * when the body is a thunk with holes, its binders put before the holes as
      * ignored ones (`Defunctionalization.thunkConfigured[C]`'s fold), unless
      * the body is an instruction of the names, which is read as a constant and
      * so is no abstraction of the term to fold into; otherwise the body's code
      * over slots in order of first occurrence and the holes of the binders.
      */
    private def chainConfigured(
        firstLevel: Int,
        count: Int,
        body: Spine,
        names: Set[Configured[C]],
        state: State
    ): TailRec[(Configured[C], State)] =
      body match
        case Spine.Closed(thunk @ HoledThunk(code, holes, fillings), _)
            if !names.contains(thunk) =>
          done(
            (
              thunkOf(
                code,
                Vector.fill(count)(Hole.Ignored) ++ holes,
                fillings
              ),
              state.counted(1)
            )
          )
        case _ =>
          bodyCode(body, Slots.empty, state).map {
            case ((code, slots), after) =>
              (
                thunkOf(code, slots.holes(firstLevel, count), slots.fillings),
                after
              )
          }

    /** A thunk with at least one hole, as a closed body of a chain folds it. */
    private object HoledThunk:
      def unapply(
          term: Configured[C]
      ): Option[(Code, Vector[Hole], Vector[Configured[C]])] = term.layer match
        case com.yang_bo.gezi.ir.Thunk(code, holes, fillings) if holes.nonEmpty =>
          Some((code, holes, fillings))
        case _ => None

    /** The thunk of the code over the holes, or, with no hole, the instance of
      * the code over its fillings: a term has no thunk without holes.
      */
    private def thunkOf(
        code: Code,
        holes: Vector[Hole],
        fillings: Vector[Configured[C]]
    ): Configured[C] =
      NonEmptyHoles.of(holes) match
        case Some(present) => specializer.thunk(code, present, fillings)
        case None          => specializer.instance(code, fillings)

    /** What a slot of a body reads: the variable of a level, or a closed part
      * by its respelling.
      */
    private enum SlotSource:
      case Variable(level: Int)
      case Closed(instruction: Configured[C])

    /** The slots of a body: what each reads, in order of first occurrence, and
      * the slot of each.
      */
    private final case class Slots(
        sources: Vector[SlotSource],
        numbers: Map[SlotSource, Int]
    ):

      /** The slot of the source, appended when new, and the slots after. */
      def slotOf(source: SlotSource): (Int, Slots) =
        numbers.get(source) match
          case Some(index) => (index, this)
          case None        =>
            (
              sources.size,
              Slots(sources :+ source, numbers.updated(source, sources.size))
            )

      /** For the binders of the levels from `firstLevel`, outermost first, the
        * slot each reads, or ignored.
        */
      def holes(firstLevel: Int, count: Int): Vector[Hole] =
        (firstLevel until firstLevel + count).toVector.map(level =>
          numbers.get(SlotSource.Variable(level)) match
            case Some(slot) => Hole.Bound(slot)
            case None       => Hole.Ignored
        )

      /** The closed parts the slots read, in slot order: a closed thunk's
        * fillings.
        */
      def fillings: Vector[Configured[C]] = sources.collect {
        case SlotSource.Closed(instruction) => instruction
      }

    private object Slots:
      val empty: Slots = Slots(Vector.empty, Map.empty)

    /** The code of an open spine in the body of a chain, and the slots after
      * it, in preorder. A variable's slot is keyed by its level, whether the
      * chain binds it or a chain outside does; the chain reads off its holes by
      * its levels afterwards (`Slots.holes`).
      */
    private def bodyCode(
        spine: Spine,
        slots: Slots,
        entered: State
    ): TailRec[((Code, Slots), State)] =
      val state = entered.counted(1)
      spine match
        case Spine.Variable(level, _) =>
          val (slot, after) = slots.slotOf(SlotSource.Variable(level))
          done(((Code.Slot(slot), after), state))
        case Spine.Closed(instruction, _) =>
          val (slot, after) = slots.slotOf(SlotSource.Closed(instruction))
          done(((Code.Slot(slot), after), state))
        case Spine.Apply(function, argument, _) =>
          for
            ((functionCode, afterFunction), functionState) <- tailcall(
              bodyCode(function, slots, state)
            )
            ((argumentCode, afterArgument), argumentState) <-
              tailcall(bodyCode(argument, afterFunction, functionState))
          yield (
            (Code.Apply(functionCode, argumentCode), afterArgument),
            argumentState
          )
        case Spine.Choice(left, right, _) =>
          for
            ((leftCode, afterLeft), leftState) <- tailcall(
              bodyCode(left, slots, state)
            )
            ((rightCode, afterRight), rightState) <- tailcall(
              bodyCode(right, afterLeft, leftState)
            )
          yield ((Code.Choice(leftCode, rightCode), afterRight), rightState)
        case Spine.Parallel(left, right, _) =>
          for
            ((leftCode, afterLeft), leftState) <- tailcall(
              bodyCode(left, slots, state)
            )
            ((rightCode, afterRight), rightState) <- tailcall(
              bodyCode(right, afterLeft, leftState)
            )
          yield ((Code.Parallel(leftCode, rightCode), afterRight), rightState)
        case Spine.Lambda(innerFirst, innerCount, innerBody, _) =>
          tailcall(bodyCode(innerBody, Slots.empty, state)).map {
            case ((innerCode, innerSlots), after) =>
              // The inner chain's slots other than its own binders' read, in its
              // slot order, slots of this body: a closed part, or a variable of a
              // level outside the inner chain.
              val (fillings, enclosing) =
                innerSlots.sources.foldLeft((Vector.empty[Code], slots)) {
                  case ((found, current), SlotSource.Variable(level))
                      if level >= innerFirst && level < innerFirst + innerCount =>
                    (found, current)
                  case ((found, current), source) =>
                    val (slot, next) = current.slotOf(source)
                    (found :+ Code.Slot(slot), next)
                }
              (
                (
                  Code.Thunk(
                    innerCode,
                    innerSlots.holes(innerFirst, innerCount),
                    fillings
                  ),
                  enclosing
                ),
                after
              )
          }
