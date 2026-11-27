package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.ir.NativeSpecializer

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole

/** A filter function's partial application: its code, its holes and the number
  * of arguments given, fewer than its holes.
  */
final case class PendingFilter(
    code: Code,
    holes: Vector[Hole],
    argumentsGiven: Int
):

  /** The hole the next argument fills. */
  def nextHole: Hole = holes(argumentsGiven)

  /** After one more argument: still pending, or nothing once every hole is
    * filled.
    */
  def advanced: Option[PendingFilter] =
    if argumentsGiven + 1 < holes.size then
      Some(copy(argumentsGiven = argumentsGiven + 1))
    else None

/** The partial applications of filter functions. */
object PendingFilter:

  /** A filter function alone, pending with no argument, or nothing when it has
    * no hole (`choice_pending/3`, and the same reading of rows 4 and 5).
    */
  def alone(code: Code, holes: Vector[Hole]): Option[PendingFilter] =
    if holes.isEmpty then None else Some(PendingFilter(code, holes, 0))

/** The fold state of `choice_attraction` (`choice_state(Depth, Pending)`): the
  * depth of the shallowest choice outside criteria, nothing for no choice,
  * which is the value; and a filter function's partial application.
  */
final case class ChoiceState(depth: Option[Int], pending: Option[PendingFilter])
    extends FoldState

/** The reading of `choice_attraction`: the filter function's partial
  * application, which tells an application over the term whether its argument
  * is a criterion; one per filter function of the graph and arguments given,
  * finitely many.
  */
final case class ChoiceReading(pending: Option[PendingFilter])
    extends ModuleReading

/** Row 2 of the HM baseline, the choice attractor, the port of
  * `gezi/prolog/gezi/baseline/choice_attraction.pl`, whose module documentation
  * this follows. The value is `depth(Depth)`, the IR tree depth of the
  * shallowest choice with at least one member (the root at depth 0; a function,
  * an argument, an operand of a parallel and a member one deeper than their
  * layer, a thunk's resolved body one deeper than the thunk; a criterion, the
  * right operand of a parallel or the argument filling the criterion hole of a
  * filter function, does not count, so that a criterion keeps the instruction
  * its backend fact is written on), or `no_choice`, the worst. An instruction
  * is a leaf. The rank is `[0, Depth]` for `depth(Depth)` and `[1]` for
  * `no_choice`.
  *
  * FIXME (carried from choice_attraction.pl:27 and :157; row 2): the
  * https://github.com/Atry/private-overlay/issues/1950 measure is the depth of
  * the choice from the root, and which depth is left open; the IR tree depth
  * was chosen on 2026-10-08, after a probe (not kept) in which the depth of the
  * role walk of the branch attractor-interface-repeller-check exhausted the
  * budget on the naturals (1355 instances).
  */
object ChoiceAttraction extends ConfigurationFreeModule:

  val name: String = "choice_attraction"

  /** Not strictly monotone at priced positions: an application's depth is the
    * shallower of its function's and its argument's (`shallower`), so a priced
    * child whose choice lies deeper leaves the parent unchanged while the other
    * child is shallower. Measured 2026-11-13 (CostMonotonicityLawTest,
    * strictness): the parent Apply(n, Apply(Choice(n, Parallel(n, n)), n)), n
    * one of the law's instructions, ranks [0 | [2 | []]] over a first child of
    * rank [1 | []] and over one of rank [0 | [2 | []]]. So an extraction
    * refuses it (`TermOrder.extractionModulesChecked`); no entry of the tree
    * names it.
    */
  val meetsExtractionContract: Boolean = false

  def folded[C <: NativeSpecializer & Singleton](
      layer: OrderTerm[C],
      reading: TermReading[C]
  ): FoldState = state(layer, reading)

  private def deeper(depth: Option[Int]): Option[Int] = depth.map(_ + 1)

  private def shallower(first: Option[Int], second: Option[Int]): Option[Int] =
    (first, second) match
      case (None, other)                => other
      case (other, None)                => other
      case (Some(depth), Some(another)) => Some(depth.min(another))

  private def state[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C],
      reading: TermReading[C]
  ): ChoiceState = term match
    case OrderTerm.Folded(folded, _) => TermOrder.ownState[ChoiceState](folded)
    case name @ OrderTerm.Name(_)    =>
      reading.filterFunction(name) match
        case Some(filter) =>
          ChoiceState(None, PendingFilter.alone(filter.code, filter.holes))
        case None =>
          reading.applicationNamed(name) match
            case Some(definition) =>
              ChoiceState(None, state(definition, reading).pending)
            case None => ChoiceState(None, None)
    case leaf if TermReading.leafTerm(leaf) => ChoiceState(None, None)
    case OrderTerm.Choice(Vector())         => ChoiceState(None, None)
    case OrderTerm.Choice(members)          =>
      members.foreach(state(_, reading))
      ChoiceState(Some(0), None)
    case OrderTerm.Parallel(value, criterion, _) =>
      val valueDepth = state(value, reading).depth
      state(criterion, reading)
      ChoiceState(deeper(valueDepth), None)
    case OrderTerm.Thunk(code, holes, fillings) =>
      val bodyDepth =
        state(TermReading.resolved(code, holes, fillings), reading).depth
      val pending = if TermReading.slotPair(code) then
        PendingFilter.alone(code, holes)
      else None
      ChoiceState(deeper(bodyDepth), pending)
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentDepth = state(argument, reading).depth
      val functionDeeper = deeper(functionState.depth)
      functionState.pending match
        case Some(pending) =>
          val (_, criterionSlot) = TermReading.slotPairSlots(pending.code)
          val depth =
            if pending.nextHole == Hole.Bound(criterionSlot) then functionDeeper
            else shallower(functionDeeper, deeper(argumentDepth))
          ChoiceState(depth, pending.advanced)
        case None =>
          ChoiceState(shallower(functionDeeper, deeper(argumentDepth)), None)
    case other => TermOrder.refused(other)

  def rank(state: FoldState): OrderValue =
    TermOrder.ownState[ChoiceState](state).depth match
      case Some(depth) =>
        OrderValue.list(OrderValue.number(0), OrderValue.number(depth))
      case None => OrderValue.list(OrderValue.number(1))

  override def reading(state: FoldState): ModuleReading =
    ChoiceReading(TermOrder.ownState[ChoiceState](state).pending)

  def value(state: FoldState): OrderValue =
    TermOrder.ownState[ChoiceState](state).depth match
      case Some(depth) =>
        OrderValue.Compound("depth", Vector(OrderValue.number(depth)))
      case None => OrderValue.Atom("no_choice")
