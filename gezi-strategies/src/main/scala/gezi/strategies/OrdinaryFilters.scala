package gezi.strategies

import gezi.ir.NativeSpecializer

import gezi.ir.Code
import gezi.ir.Spine
import gezi.ir.Hole

/** The fold state of `ordinary_filters` (`ordinary(Count, Eta, Pending,
  * Operands)`): the count, which is the value and the rank; whether the spine
  * head, read through names of applications, is an eta expansion; a filter
  * function's partial application; and, for a parallel, its count read as a
  * position of two operands.
  */
final case class OrdinaryState(
    count: BigInt,
    eta: Boolean,
    pending: Option[PendingFilter],
    operands: Option[BigInt]
) extends FoldState

/** The reading of `ordinary_filters`: whether the spine head is an eta
  * expansion, the filter function's partial application, and, for a parallel,
  * how much its count exceeds its operands count (its own filter, 0 or 1),
  * which a thunk over it reads. Within a reading the operands count follows the
  * count, so the rank orders the states a parent reads.
  */
final case class OrdinaryReading(
    eta: Boolean,
    pending: Option[PendingFilter],
    ownFilter: Option[BigInt]
) extends ModuleReading

/** Row 4 of the HM baseline, the count of ordinary filters, the port of
  * `gezi/prolog/gezi/baseline/ordinary_filters.pl`, whose module documentation
  * this follows. It reads filters as row 1 does (`TermReading`, FILTERS). The
  * value is the number of filters whose filtered value's spine head, read
  * through names of applications, is no instruction of an eta expansion,
  * criteria included.
  *
  * ETA EXPANSION: an instruction whose definition is a thunk with at least one
  * hole whose code is one filling applied to all the holes in lambda order,
  * `\x1 ... \xn. F x1 ... xn` with F a filling: the typed variant of row 4 read
  * from the definition by the eta reading.
  *
  * FIXME (carried from ordinary_filters.pl:24 and :69; row 4):
  * https://github.com/Atry/private-overlay/issues/1957 the reading takes every
  * eta expansion of a closed term for a typed variant; a define that is the eta
  * expansion of another define for any other reason is read the same way (a
  * probe, not kept, found this reading taking an alias of an elimination
  * combinator for a typed variant). The reading has not been run on the HM
  * lemma set.
  *
  * A parent reads a parallel's operands count beside its count; the reading
  * (`OrdinaryReading`) carries their difference, so that within a reading the
  * rank orders the states.
  */
object OrdinaryFilters extends ConfigurationFreeModule:

  val name: String = "ordinary_filters"

  val meetsExtractionContract: Boolean = true

  def folded[C <: NativeSpecializer & Singleton](
      layer: OrderTerm[C],
      reading: TermReading[C]
  ): FoldState = state(layer, reading)

  /** An instruction whose definition is a thunk with at least one hole whose
    * code applies one of its fillings to all its holes in lambda order
    * (`eta_expansion/1`).
    */
  private def etaExpansion[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C],
      reading: TermReading[C]
  ): Boolean = term match
    case OrderTerm.Name(instruction) =>
      reading.nameTerm(instruction) match
        case Some(OrderTerm.Thunk(code, holes, fillings))
            if holes.nonEmpty && fillings.nonEmpty =>
          Spine.of(code) match
            case (Code.Slot(captured), applied) =>
              !holes.contains(Hole.Bound(captured)) &&
              applied.forall {
                case Code.Slot(_) => true
                case _            => false
              } &&
              applied.collect { case Code.Slot(index) =>
                Hole.Bound(index): Hole
              } == holes
            case _ => false
        case _ => false
    case _ => false

  private val plain = OrdinaryState(0, false, None, None)

  private def state[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C],
      reading: TermReading[C]
  ): OrdinaryState = term match
    case OrderTerm.Folded(folded, _) =>
      TermOrder.ownState[OrdinaryState](folded)
    case name @ OrderTerm.Name(_) =>
      reading.filterFunction(name) match
        case Some(filter) =>
          filterFunctionState(
            filter.code,
            filter.holes,
            filter.fillings,
            reading
          )
        case None =>
          reading.applicationNamed(name) match
            case Some(definition) => state(definition, reading)
            case None             =>
              if etaExpansion(name, reading) then plain.copy(eta = true)
              else plain
    case leaf if TermReading.leafTerm(leaf)      => plain
    case OrderTerm.Parallel(value, criterion, _) =>
      val (count, bodyCount) = filterCounted(value, criterion, reading)
      OrdinaryState(count, false, None, Some(bodyCount))
    case OrderTerm.Choice(members) =>
      plain.copy(count = members.map(state(_, reading).count).sum)
    case OrderTerm.Thunk(code, holes, fillings) =>
      if TermReading.slotPair(code) then
        filterFunctionState(code, holes, fillings, reading)
      else
        val body = state(TermReading.resolved(code, holes, fillings), reading)
        plain.copy(count = body.operands.getOrElse(body.count))
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentState = state(argument, reading)
      functionState.pending match
        case Some(pending) =>
          val added =
            filledHoleCounted(pending.code, pending.nextHole, argumentState)
          OrdinaryState(
            functionState.count + added,
            false,
            pending.advanced,
            None
          )
        case None =>
          OrdinaryState(
            functionState.count + argumentState.count,
            functionState.eta,
            None,
            None
          )
    case other => TermOrder.refused(other)

  /** The count of a filter: one unless its value's spine head is an eta
    * expansion, plus the counts of the value and the criterion; and the counts
    * of the two alone, the parallel read as a position of two operands
    * (`ordinary_filter_counted/4`).
    */
  private def filterCounted[C <: NativeSpecializer & Singleton](
      value: OrderTerm[C],
      criterion: OrderTerm[C],
      reading: TermReading[C]
  ): (BigInt, BigInt) =
    val valueState = state(value, reading)
    val criterionState = state(criterion, reading)
    val bodyCount = valueState.count + criterionState.count
    (own(valueState.eta) + bodyCount, bodyCount)

  private def own(eta: Boolean): BigInt = if eta then 0 else 1

  /** A filter function alone, its code instantiated with its holes leaves
    * (`ordinary_filter_function/4`).
    */
  private def filterFunctionState[C <: NativeSpecializer & Singleton](
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[OrderTerm[C]],
      reading: TermReading[C]
  ): OrdinaryState =
    TermReading.instantiated(code, holes, fillings, Vector.empty)._1 match
      case OrderTerm.Parallel(value, criterion, _) =>
        val (count, _) = filterCounted(value, criterion, reading)
        OrdinaryState(count, false, PendingFilter.alone(code, holes), None)
      case other =>
        throw IllegalStateException(
          s"a filter function's code instantiated to $other"
        )

  /** What an argument filling the hole of a filter function's code adds: at the
    * value, its own filter for the hole's leaf replaced by its eta reading, and
    * its count; at the criterion, its count; an ignored hole drops it
    * (`filled_hole_counted/5`).
    */
  private def filledHoleCounted(
      code: Code,
      hole: Hole,
      argument: OrdinaryState
  ): BigInt =
    val (valueSlot, criterionSlot) = TermReading.slotPairSlots(code)
    val valueAdded = if hole == Hole.Bound(valueSlot) then
      own(argument.eta) - 1 + argument.count
    else BigInt(0)
    val criterionAdded =
      if hole == Hole.Bound(criterionSlot) then argument.count else BigInt(0)
    valueAdded + criterionAdded

  def rank(state: FoldState): OrderValue =
    OrderValue.Number(TermOrder.ownState[OrdinaryState](state).count)

  override def reading(state: FoldState): ModuleReading =
    val own = TermOrder.ownState[OrdinaryState](state)
    OrdinaryReading(own.eta, own.pending, own.operands.map(own.count - _))

  def value(state: FoldState): OrderValue = rank(state)
