package com.yang_bo.gezi.narrowblocks

import com.yang_bo.gezi.ir
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.strategies.CodeFold
import com.yang_bo.gezi.strategies.CodeFolding
import com.yang_bo.gezi.strategies.FoldState
import com.yang_bo.gezi.strategies.ModuleReading
import com.yang_bo.gezi.strategies.OrderTerm
import com.yang_bo.gezi.strategies.OrderValue
import com.yang_bo.gezi.strategies.TermOrderError
import com.yang_bo.gezi.strategies.TermOrderErrorReason
import com.yang_bo.gezi.strategies.TermReading

/** What a slot holds as the narrow parse reads it (`NarrowItem`, its binder
  * numbers dropped, which no production's acceptance reads): a closed term of a
  * kind, a binder, the recursion of so many parameters, or nothing the parse
  * can read (an inner thunk's filling that is no slot, whose let the parse
  * refuses).
  */
enum NarrowSlotItem:
  case Known(kind: NarrowKind)
  case Parameter
  case Recursion(parameters: Int)
  case Missing

/** What one of the two parses of a thunk's body (`NarrowBlocks.body`, without
  * and with its first hole the recursion) accepts a code part as: an expression
  * (`expression`), an operand (`operand`), and a branch or a let's body, a
  * thunk of one hole whose fillings are slots and whose code is an expression
  * with its hole a binder (`branch`).
  */
final case class NarrowParse(
    expression: Boolean,
    operand: Boolean,
    branch: Boolean
)

object NarrowParse:
  val refused: NarrowParse = NarrowParse(false, false, false)

/** The head of an application spine as the parse reads it
  * (`NarrowBlocks.application`).
  */
enum NarrowHead:
  case SlotHead(function: NarrowSlotItem, recursion: NarrowSlotItem)
  case FilterHead(
      criterionRead: Boolean,
      function: NarrowParse,
      recursion: NarrowParse
  )
  case LetHead(function: NarrowParse, recursion: NarrowParse)
  case OtherHead

/** An argument of an application spine as the parse reads it: its parses, and,
  * where it is a slot, what it holds and which hole it is.
  */
final case class NarrowArgument(
    function: NarrowParse,
    recursion: NarrowParse,
    slot: Option[(NarrowSlotItem, NarrowSlotItem)],
    hole: Option[(Int, Int)]
)

/** The shape of a code part beyond its parses: a slot, an application spine, or
  * any other part.
  */
enum NarrowShape:
  case SlotShape(
      function: NarrowSlotItem,
      recursion: NarrowSlotItem,
      hole: Option[(Int, Int)]
  )
  case Spine(head: NarrowHead, arguments: Vector[NarrowArgument])
  case FilterShape(
      criterionRead: Boolean,
      function: NarrowParse,
      recursion: NarrowParse
  )
  case ThunkShape
  case OtherShape

/** The reading of a code part at `narrow_blocks`: its two parses, its shape,
  * whether every filling slot it reads holds a `Closed` term, and the depths of
  * the holes it reads (`NarrowBlocks.closedSlots`: a part that reads no hole
  * and only `Closed` fillings is a closed term of the block).
  */
final case class NarrowCodeReading(
    function: NarrowParse,
    recursion: NarrowParse,
    shape: NarrowShape,
    closedFillings: Boolean,
    holeDepths: Set[Int]
) extends ModuleReading

/** The code state of `narrow_blocks` (`NarrowCodeFolding`): its reading, and
  * the residuals of the fillings the part reads (`residual`), so that the thunk
  * counts each filling once however many times its code reads it, as
  * `NarrowBlockOrder` counts a thunk's children. A filling the code reads more
  * than once (`CodeFold.Filling`'s `repeated`) counts nothing where it is read
  * and is counted once when the thunk is closed (`CodeFold.Closing`'s
  * `repeated`): the parts the extraction compares read the same entries of the
  * repeated fillings, so leaving them out of a part's rank changes no
  * comparison.
  */
final case class NarrowCodeState(reading: NarrowCodeReading, residual: BigInt)
    extends FoldState:
  def closed: Boolean = reading.closedFillings && reading.holeDepths.isEmpty

object NarrowCodeState:

  /** The counts of the parts together. */
  def joined(
      reading: NarrowCodeReading,
      parts: Vector[NarrowCodeState]
  ): NarrowCodeState =
    NarrowCodeState(reading, parts.foldLeft(BigInt(0))(_ + _.residual))

/** `narrow_blocks`'s fold of a thunk's code part by part (`CodeFolding`): the
  * parse of `NarrowBlocks.body` read as a summary of each part (what each of
  * the two parses accepts it as, and what a part around it reads of it), so
  * that a thunk's kind (`NarrowBlocks.thunkKind`) is a function of its code's
  * summary and the fillings' kinds enter only through the parts that read them;
  * and the thunk's rank, its code's layers and its fillings' residuals summed
  * once each. The summary holds what `thunkKind` already derives from the
  * code's syntax and the fillings' kinds, and the ranks the module counts: no
  * fact about a node's type, and no record kept beside the term, a memo of a
  * function of the syntax (`CONTRIBUTING.md`, "Tables").
  */
final class NarrowCodeFolding[C <: NativeSpecializer & Singleton]
    extends CodeFolding[C]:

  def folded(layer: CodeFold[C], reading: TermReading[C]): FoldState =
    layer match
      case CodeFold.Filling(term, repeated) =>
        val kind = termKind(term)
        val residual = if repeated then BigInt(0) else counted(term)
        val item = NarrowSlotItem.Known(kind)
        slot(item, item, None, kind == NarrowKind.Closed, Set.empty, residual)
      case CodeFold.InnerFilling(part) =>
        val inner = own(part)
        val (function, recursion) = inner.reading.shape match
          case NarrowShape.SlotShape(function, recursion, _) =>
            (function, recursion)
          case _ => (NarrowSlotItem.Missing, NarrowSlotItem.Missing)
        slot(
          function,
          recursion,
          None,
          inner.reading.closedFillings,
          inner.reading.holeDepths,
          inner.residual
        )
      case CodeFold.HoleSlot(depth, position, count) =>
        val recursion = if depth == 0 && position == 0 then
          NarrowSlotItem.Recursion(count - 1)
        else NarrowSlotItem.Parameter
        slot(
          NarrowSlotItem.Parameter,
          recursion,
          Some((depth, position)),
          true,
          Set(depth),
          0
        )
      case CodeFold.Apply(function, argument) =>
        val (functionState, argumentState) = (own(function), own(argument))
        val spine: NarrowShape.Spine = functionState.reading.shape match
          case NarrowShape.Spine(head, arguments) =>
            NarrowShape.Spine(head, arguments :+ asArgument(argumentState))
          case _ =>
            NarrowShape.Spine(
              asHead(functionState),
              Vector(asArgument(argumentState))
            )
        val closedFillings =
          functionState.reading.closedFillings && argumentState.reading.closedFillings
        val holeDepths =
          functionState.reading.holeDepths ++ argumentState.reading.holeDepths
        val closed = closedFillings && holeDepths.isEmpty
        def parse(recursion: Boolean): NarrowParse =
          val expression = application(spine, recursion)
          NarrowParse(expression, closed || expression, false)
        NarrowCodeState.joined(
          NarrowCodeReading(
            parse(false),
            parse(true),
            spine,
            closedFillings,
            holeDepths
          ),
          Vector(functionState, argumentState)
        )
      case CodeFold.Parallel(left, criterion) =>
        val (leftState, criterionState) = (own(left), own(criterion))
        val criterionRead = criterionState.reading.shape match
          case NarrowShape.SlotShape(
                NarrowSlotItem.Known(NarrowKind.Criterion(true)),
                _,
                _
              ) =>
            true
          case _ => false
        val closedFillings =
          leftState.reading.closedFillings && criterionState.reading.closedFillings
        val holeDepths =
          leftState.reading.holeDepths ++ criterionState.reading.holeDepths
        val closed = closedFillings && holeDepths.isEmpty
        def parse(value: NarrowParse): NarrowParse =
          if criterionRead then NarrowParse(value.operand, value.operand, false)
          else NarrowParse(false, closed, false)
        NarrowCodeState.joined(
          NarrowCodeReading(
            parse(leftState.reading.function),
            parse(leftState.reading.recursion),
            NarrowShape.FilterShape(
              criterionRead,
              leftState.reading.function,
              leftState.reading.recursion
            ),
            closedFillings,
            holeDepths
          ),
          Vector(leftState, criterionState)
        )
      case CodeFold.RangeParallel(left, range) =>
        folded(CodeFold.Parallel(left, range), reading)
      case CodeFold.Choice(members, _) =>
        // The narrow grammar reads the code as written: a choice is no
        // expression, and an operand only as a closed term, every slot it reads
        // holding a `Closed` term (`NarrowBlocks.operand`, `closedSlots`).
        val memberStates = members.map(own)
        val closedFillings = memberStates.forall(_.reading.closedFillings)
        val holeDepths = memberStates.flatMap(_.reading.holeDepths).toSet
        val parse =
          NarrowParse(false, closedFillings && holeDepths.isEmpty, false)
        NarrowCodeState.joined(
          NarrowCodeReading(
            parse,
            parse,
            NarrowShape.OtherShape,
            closedFillings,
            holeDepths
          ),
          memberStates
        )
      case CodeFold.InnerThunk(depth, _, holes, fillings, body, unread) =>
        val bodyState = own(body)
        val unreadStates = unread.map(own)
        val fillingsAreSlots = fillings.forall(_.layer match
          case ir.Slot(_) => true
          case _          => false)
        // The slots a thunk reads are its fillings' (`NarrowBlocks.closedSlots`):
        // its own holes, which its code reads, are not.
        val closedFillings =
          bodyState.reading.closedFillings && unreadStates.forall(
            _.reading.closedFillings
          )
        val holeDepths =
          (bodyState.reading.holeDepths - (depth + 1)) ++ unreadStates.flatMap(
            _.reading.holeDepths
          )
        val closed = closedFillings && holeDepths.isEmpty
        def parse(bodyParse: NarrowParse): NarrowParse =
          NarrowParse(
            false,
            closed,
            holes.size == 1 && fillingsAreSlots && bodyParse.expression
          )
        NarrowCodeState.joined(
          NarrowCodeReading(
            parse(bodyState.reading.function),
            parse(bodyState.reading.recursion),
            NarrowShape.ThunkShape,
            closedFillings,
            holeDepths
          ),
          bodyState +: unreadStates
        )
      case CodeFold.Closing(code, holes, body, unread, repeated) =>
        val bodyState = own(body)
        val kind = closedKind(code, holes, bodyState)
        // A thunk is never a `Value` (`NarrowBlocks.thunkKind`), so whatever
        // its kind the reader reads it whole where it stands outside blocks
        // (`NarrowBlockOrder`).
        NarrowBlockState(
          kind,
          codeSize(code) + bodyState.residual + (unread ++ repeated)
            .map(counted)
            .sum
        )

  def rank(state: FoldState): OrderValue =
    OrderValue.Number(own(state).residual)

  def reading(state: FoldState): ModuleReading = own(state).reading

  /** The code state, read by its class without summoning a `ClassTag` at each
    * part (`TermOrder.ownState`), which the code fold reads at every node.
    */
  private def own(state: FoldState): NarrowCodeState = state match
    case own: NarrowCodeState => own
    case other                =>
      throw TermOrderError(
        TermOrderErrorReason.NotATerm(OrderTerm.Folded(other, false))
      )

  /** What a filling counts: its residual where priced, and one node where it is
    * read only by its reading, as a criterion, as `NarrowBlockOrder` counts an
    * unpriced child of a thunk.
    */
  private def counted(term: OrderTerm[C]): BigInt = term match
    case OrderTerm.Folded(state, _) => blockState(state).residual
    case _                          => 1

  /** A filling's `narrow_blocks` state, read by its class without summoning a
    * `ClassTag` (`TermOrder.ownState`) at each filling the code fold reads.
    */
  private def blockState(state: FoldState): NarrowBlockState = state match
    case own: NarrowBlockState => own
    case other                 =>
      throw TermOrderError(
        TermOrderErrorReason.NotATerm(OrderTerm.Folded(other, false))
      )

  /** A slot's state, holding the items given in the two parses, with the counts
    * given.
    */
  private def slot(
      function: NarrowSlotItem,
      recursion: NarrowSlotItem,
      hole: Option[(Int, Int)],
      closedFillings: Boolean,
      holeDepths: Set[Int],
      residual: BigInt
  ): NarrowCodeState =
    NarrowCodeState(
      NarrowCodeReading(
        slotParse(function),
        slotParse(recursion),
        NarrowShape.SlotShape(function, recursion, hole),
        closedFillings,
        holeDepths
      ),
      residual
    )

  /** A slot as an expression (a `Value`) and as an operand (a binder, a
    * `Value`, a `Closed` term).
    */
  private def slotParse(item: NarrowSlotItem): NarrowParse = item match
    case NarrowSlotItem.Known(NarrowKind.Value) =>
      NarrowParse(true, true, false)
    case NarrowSlotItem.Known(NarrowKind.Closed) =>
      NarrowParse(false, true, false)
    case NarrowSlotItem.Parameter => NarrowParse(false, true, false)
    case _                        => NarrowParse.refused

  /** The kind of a filling's term, as `NarrowBlockOrder` reads a child. */
  private def termKind(term: OrderTerm[C]): NarrowKind = term match
    case OrderTerm.Folded(state, _) => blockState(state).kind
    case OrderTerm.Unpriced(NarrowBlockReading(unpricedKind)) => unpricedKind
    case _ => NarrowKind.Closed

  private def asHead(state: NarrowCodeState): NarrowHead =
    state.reading.shape match
      case NarrowShape.SlotShape(function, recursion, _) =>
        NarrowHead.SlotHead(function, recursion)
      case NarrowShape.FilterShape(criterionRead, function, recursion) =>
        NarrowHead.FilterHead(criterionRead, function, recursion)
      case NarrowShape.ThunkShape =>
        NarrowHead.LetHead(state.reading.function, state.reading.recursion)
      case _ => NarrowHead.OtherHead

  private def asArgument(state: NarrowCodeState): NarrowArgument =
    val (slotItems, hole) = state.reading.shape match
      case NarrowShape.SlotShape(function, recursion, hole) =>
        (Some((function, recursion)), hole)
      case _ => (None, None)
    NarrowArgument(
      state.reading.function,
      state.reading.recursion,
      slotItems,
      hole
    )

  /** Whether the parse (`recursion` or not) reads the spine as an expression,
    * as `NarrowBlocks.application` does.
    */
  private def application(
      spine: NarrowShape.Spine,
      recursion: Boolean
  ): Boolean =
    val arguments = spine.arguments
    val count = arguments.size
    def parseOf(argument: NarrowArgument): NarrowParse =
      if recursion then argument.recursion else argument.function
    def operands(of: Vector[NarrowArgument]): Boolean =
      of.forall(parseOf(_).operand)
    spine.head match
      case NarrowHead.SlotHead(function, recursionItem) =>
        (if recursion then recursionItem else function) match
          case NarrowSlotItem.Known(NarrowKind.Native(_, places, 0))
              if count == places =>
            operands(arguments)
          case NarrowSlotItem.Known(NarrowKind.Native(_, places, supplied))
              if supplied > 0 && count == places - supplied =>
            operands(arguments)
          case NarrowSlotItem.Recursion(parameters) if count == parameters =>
            operands(arguments)
          case NarrowSlotItem.Known(NarrowKind.Thunk(true, _, holes))
              if count == holes =>
            operands(arguments)
          case NarrowSlotItem.Known(NarrowKind.FixpointApplied(parameters, 0))
              if count == parameters =>
            operands(arguments)
          case NarrowSlotItem.Known(
                NarrowKind.FixpointApplied(parameters, supplied)
              ) if supplied > 0 && count == parameters - supplied =>
            operands(arguments)
          case NarrowSlotItem.Known(NarrowKind.Fixpoint) =>
            arguments.headOption.flatMap(_.slot) match
              case Some((functionItem, recursionItemOfBody)) =>
                (if recursion then recursionItemOfBody else functionItem) match
                  case NarrowSlotItem.Known(NarrowKind.Thunk(_, true, holes))
                      if count == holes =>
                    operands(arguments.drop(1))
                  case _ => false
              case None => false
          case _ => false
      case NarrowHead.FilterHead(criterionRead, function, recursionParse)
          if criterionRead && count == 3 =>
        val Vector(zero, even, odd) = arguments: @unchecked
        (if recursion then recursionParse else function).operand &&
        parseOf(zero).operand && parseOf(even).branch && parseOf(odd).branch
      case NarrowHead.LetHead(function, recursionParse) if count == 1 =>
        arguments.forall(
          parseOf(_).operand
        ) && (if recursion then recursionParse else function).branch
      case _ => false

  /** The thunk's kind from its code's summary, as `NarrowBlocks.thunkKind`. */
  private def closedKind(
      code: Code,
      holes: Vector[Hole],
      body: NarrowCodeState
  ): NarrowKind =
    (holes, code.layer) match
      case (Vector(Hole.Bound(first), Hole.Ignored), ir.Slot(slot))
          if slot == first =>
        NarrowKind.Truth(true)
      case (Vector(Hole.Ignored, Hole.Bound(second)), ir.Slot(slot))
          if slot == second =>
        NarrowKind.Truth(false)
      case (Vector(Hole.Bound(bound)), ir.Slot(slot)) if slot == bound =>
        NarrowKind.Identity
      case (Vector(Hole.Bound(_)), ir.Apply(_, _)) if selectsItsHole(body) =>
        NarrowKind.Identity
      case _ =>
        if holes.isEmpty then NarrowKind.Closed
        else
          val function = body.reading.function.expression
          val recursion = body.reading.recursion.expression
          if function || recursion then
            NarrowKind.Thunk(function, recursion, holes.size)
          else NarrowKind.Closed

  /** Whether the code is a boolean filling applied to two codes and the one it
    * selects is the thunk's only hole (`NarrowBlocks.selectedByTruth`).
    */
  private def selectsItsHole(body: NarrowCodeState): Boolean =
    body.reading.shape match
      case NarrowShape.Spine(
            NarrowHead.SlotHead(
              NarrowSlotItem.Known(NarrowKind.Truth(value)),
              _
            ),
            Vector(first, second)
          ) =>
        (if value then first else second).hole.contains((0, 0))
      case _ => false

  private def codeSize(code: Code): BigInt = code.layer match
    case ir.Slot(_)                   => 1
    case ir.Apply(function, argument) =>
      1 + codeSize(function) + codeSize(argument)
    case ir.Parallel(left, right) => 1 + codeSize(left) + codeSize(right)
    case ir.Choice(_, _)          =>
      val Code.ChoiceMembers(members) = code
      1 + members.map(codeSize).sum
    case ir.Thunk(inner, _, fillings) =>
      1 + codeSize(inner) + fillings.map(codeSize).sum
