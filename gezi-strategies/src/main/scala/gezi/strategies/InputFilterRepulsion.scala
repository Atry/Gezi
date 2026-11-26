package gezi.strategies

import gezi.ir.Code
import gezi.ir.Spine
import gezi.ir.Hole

/** The reading of a spine head that an argument added to it needs: an
  * input filter at a position applied to some arguments, capped at the
  * position; a filter function's partial application; or neither.
  */
enum RepulsionHead:
  case InputFilter(position: Int, argumentsGiven: Int)
  case Pending(filter: PendingFilter)
  case Other

/** The fold state of `input_filter_repulsion` (`repulsion(Count, Head,
  * Operands)`): the count in the skeleton state, which is the value and the
  * rank; the spine head's reading; and, for a parallel, its count read as a
  * position of two operands.
  */
final case class RepulsionState(count: BigInt, head: RepulsionHead, operands: Option[BigInt]) extends FoldState

/** The reading of `input_filter_repulsion`: the spine head's reading, and,
  * for a parallel, how much its operands count exceeds its count (its
  * criterion's count, 0 for a parallel the extraction builds, whose
  * criterion is unpriced), which a thunk over it reads.
  */
final case class RepulsionReading(head: RepulsionHead, criterionCount: Option[BigInt]) extends ModuleReading

/** Row 5 of the HM baseline, the repeller of input filters, the port of
  * `gezi/prolog/gezi/baseline/input_filter_repulsion.pl`, whose
  * module documentation this follows. It reads filters as row 1 does
  * (`TermReading`, FILTERS). The value is the number of occurrences, at
  * skeleton positions, of input filters applied to at least their function
  * argument.
  *
  * INPUT FILTER: an instruction whose definition is a thunk with no filling whose
  * code applies the binder at position P (from 1) to parallels, the j-th of
  * which has on its left the binder at position P + j and on its right a
  * binder before P. An OCCURRENCE is an application spine whose head is an
  * input filter and which has at least P arguments, at a skeleton position.
  * SKELETON POSITIONS are the positions outside every criterion: the right
  * operand of a parallel or of a filter function, and the arguments of an
  * input filter before its function, are criteria; everything below a
  * criterion inherits it.
  *
  * FIXME (carried from input_filter_repulsion.pl:31 and :114): https://github.com/Atry/private-overlay/issues/1956
  * row 5's contribution is to be written as a function of the skeleton state
  * it inherits, which is what makes it structural recursion. The skeleton
  * state here is inherited from the root, a function of the position; the reading of row 5 has
  * not been run on the HM lemma set.
  *
  * A parent reads a parallel's operands count beside its count; the
  * reading (`RepulsionReading`) carries their difference, so that within a
  * reading the rank orders the states.
  */
object InputFilterRepulsion extends NormalityModule:

  val name: String = "input_filter_repulsion"

  val meetsExtractionContract: Boolean = true

  def folded(layer: OrderTerm, reading: TermReading): FoldState = state(layer, reading)

  /** The position of the function binder of an input filter, when the
    * instruction is one (`input_filter/2`).
    */
  private def inputFilter(term: OrderTerm, reading: TermReading): Option[Int] = term match
    case OrderTerm.Name(instruction) =>
      reading.nameTerm(instruction) match
        case Some(OrderTerm.Thunk(code, holes, Vector())) =>
          Spine.of(code) match
            case (Code.Slot(functionSlot), parallels) if parallels.nonEmpty =>
              TermReading.binderPosition(holes, functionSlot).filter(position =>
                parallels.zipWithIndex.forall {
                  case (Code.Parallel(Code.Slot(left), Code.Slot(right)), index) =>
                    TermReading.binderPosition(holes, left).contains(position + index + 1) &&
                    TermReading.binderPosition(holes, right).exists(_ < position)
                  case _ => false
                }
              )
            case _ => None
        case _ => None
    case _ => None

  private def state(term: OrderTerm, reading: TermReading): RepulsionState = term match
    case OrderTerm.Folded(folded, _) => TermOrder.ownState[RepulsionState](folded)
    case name @ OrderTerm.Name(_) =>
      reading.filterFunction(name) match
        case Some(filter) => filterFunctionState(filter.code, filter.holes, filter.fillings, reading)
        case None =>
          reading.applicationNamed(name) match
            case Some(definition) => state(definition, reading)
            case None =>
              inputFilter(name, reading) match
                case Some(position) => RepulsionState(0, RepulsionHead.InputFilter(position, 0), None)
                case None           => RepulsionState(0, RepulsionHead.Other, None)
    case leaf if TermReading.leafTerm(leaf) => RepulsionState(0, RepulsionHead.Other, None)
    case OrderTerm.Parallel(value, criterion, _) =>
      val count = state(value, reading).count
      val criterionCount = state(criterion, reading).count
      RepulsionState(count, RepulsionHead.Other, Some(count + criterionCount))
    case OrderTerm.Choice(members) =>
      RepulsionState(members.map(state(_, reading).count).sum, RepulsionHead.Other, None)
    case OrderTerm.Thunk(code, holes, fillings) =>
      if TermReading.slotPair(code) then filterFunctionState(code, holes, fillings, reading)
      else
        val body = state(TermReading.resolved(code, holes, fillings), reading)
        RepulsionState(body.operands.getOrElse(body.count), RepulsionHead.Other, None)
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentCount = state(argument, reading).count
      val (added, head) = applied(functionState.head, argumentCount)
      RepulsionState(functionState.count + added, head, None)
    case other => TermOrder.refused(other)

  /** One more argument of a spine whose head reads as given: an input
    * filter's arguments before its function are criteria, its function
    * argument makes the occurrence; a filter function's criterion hole takes
    * a criterion; any other argument adds its count (`repulsion_applied/4`).
    */
  private def applied(head: RepulsionHead, argumentCount: BigInt): (BigInt, RepulsionHead) = head match
    case RepulsionHead.InputFilter(position, argumentsGiven) =>
      val added =
        if argumentsGiven + 1 < position then BigInt(0)
        else if argumentsGiven + 1 == position then argumentCount + 1
        else argumentCount
      (added, RepulsionHead.InputFilter(position, (argumentsGiven + 1).min(position)))
    case RepulsionHead.Pending(pending) =>
      val (valueSlot, _) = TermReading.slotPairSlots(pending.code)
      val added = if pending.nextHole == Hole.Bound(valueSlot) then argumentCount else BigInt(0)
      (added, pending.advanced.fold(RepulsionHead.Other)(RepulsionHead.Pending(_)))
    case RepulsionHead.Other => (argumentCount, RepulsionHead.Other)

  /** A filter function alone, its code instantiated with its holes leaves:
    * its value at the skeleton, its criterion a criterion
    * (`repulsion_filter_function/4`).
    */
  private def filterFunctionState(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[OrderTerm],
      reading: TermReading
  ): RepulsionState =
    TermReading.instantiated(code, holes, fillings, Vector.empty)._1 match
      case OrderTerm.Parallel(value, _, _) =>
        val head = PendingFilter.alone(code, holes).fold(RepulsionHead.Other)(RepulsionHead.Pending(_))
        RepulsionState(state(value, reading).count, head, None)
      case other => throw IllegalStateException(s"a filter function's code instantiated to $other")

  def rank(state: FoldState): OrderValue = OrderValue.Number(TermOrder.ownState[RepulsionState](state).count)

  override def reading(state: FoldState): ModuleReading =
    val own = TermOrder.ownState[RepulsionState](state)
    RepulsionReading(own.head, own.operands.map(_ - own.count))

  def value(state: FoldState): OrderValue = rank(state)
