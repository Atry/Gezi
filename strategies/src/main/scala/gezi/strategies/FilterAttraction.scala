package gezi.strategies

import gezi.ir.Code
import gezi.ir.Hole

/** The other members of choices: their number and the sum of their Mains
  * (`rest(Count, Sum)`).
  */
final case class Rest(count: BigInt, sum: BigInt):
  def +(other: Rest): Rest = Rest(count + other.count, sum + other.sum)

  /** One more other member, whose Main is given. */
  def memberAdded(main: BigInt): Rest = Rest(count + 1, sum + main)

object Rest:
  val empty: Rest = Rest(0, 0)

/** What a parent reads of the flattened positions of a term's root: the
  * height, Main and Rest of the positions as they are, and Main and Rest of
  * the same positions once a filter covers every one
  * (`measure(Height, Main, Rest, CoveredMain, CoveredRest)`).
  */
final case class Measure(height: Int, main: BigInt, rest: Rest, coveredMain: BigInt, coveredRest: Rest)

/** Where the value slot of a partially applied filter function takes its
  * term from: a term already given, or the argument at an index among the
  * next ones.
  */
enum ValueSource:
  case Given(value: OrderTerm)
  case Pending(index: Int)

/** How a term extends when it is the function of an application. */
enum Absorb:

  /** The term is a spine, or one child of one: its children's tallest
    * height, the sums of their Mains and of their Rests, and whether a
    * filter is read in any of them; an argument adds a child.
    */
  case SpineChildren(tallest: Int, below: BigInt, rest: Rest, read: Boolean)

  /** The term is a filter's value, or the value of a parallel at the head:
    * the absorb, covered.
    */
  case Covered(absorb: Absorb)

  /** A filter function applied to fewer arguments than its holes, some of
    * them left, and the source of its value.
    */
  case FilterFunction(remaining: Int, source: ValueSource)

/** The fold state of `filter_attraction` (`filter_fold(Flag, Measure,
  * Absorbs, Operands)`): whether some filter is read outside criteria; the
  * measure; how the term extends at the head of a spine, one absorb per way;
  * and, for a parallel, the flag and the measure of the position of its two
  * operands.
  */
final case class FilterState(
    read: Boolean,
    measure: Measure,
    absorbs: Vector[Absorb],
    operands: Option[(Boolean, Measure)]
) extends FoldState

/** Row 1 of the HM baseline, the filter attractor at distance 0, the port of
  * `gezi/prolog/gezi/baseline/filter_attraction.pl`, whose
  * module documentation (ROW 1 AT DISTANCE 0, BOUNDED WEIGHTS, THE FOLD
  * STATE, WHAT A PARENT READS) the folds here follow, predicate by
  * predicate. It reads filters as `TermReading` defines them (FILTERS). The
  * value is `positions(Main, Count, Sum)`, Main the sum of 33^min(h, 15) over
  * the heights h of the positions no filter covers, read through the best
  * member of every choice, and `rest(Count, Sum)` the number of the other
  * members of every choice and the sum of their Mains; or `no_filter`, the
  * worst. The rank is `[0, Main, Count, Sum]`, or `[1]` for `no_filter`.
  *
  * FIXME (carried from filter_attraction.pl:18; X4 at extraction; a https://github.com/Atry/private-overlay/issues/1952
  * conflict between constraints, still open): the
  * criterion of a filter is read only by the standard order of ∥, the right
  * operand, and nothing reads whether it is a type. Row 1 therefore counts a
  * filter whose criterion is a fold's image as covering its position just as
  * a filter by a type does. The output is to be an HM-checked typed term,
  * so a fold HM rejects, such as X4 = nat_fold zero true (successor zero),
  * is not to read as typed, while the host holds no type (`CONTRIBUTING.md`,
  * "Types live only in the term"), which excludes a rule that classifies
  * criteria as types. The reading of the Prolog baseline (probe of
  * 2026-10-19 on cb33d570e) is in the Prolog file's FIXME (`git show
  * 13db98f8d:lambda_jit/prolog/lambda_jit/baseline/filter_attraction.pl`).
  *
  * FIXME (carried from filter_attraction.pl:46; an unproven filter at https://github.com/Atry/private-overlay/issues/1952
  * extraction): row 1 recognizes a filter
  * by its code alone, so it reads neither whether the filter is proven,
  * which is whether the filtered term's class holds it (class identity,
  * which no module reads), nor whether its criterion is a type. A
  * filter that no lemma instance proved covers its position as a proven one
  * does. The proof gate on generic_fold's fold_typed_version leaned on this
  * defect (generic_fold.pl, the FIXME on an unproven filter inside the image,
  * which filter_attraction.pl:69 referred to), so that a row 1 that read
  * proofs would have oriented neither fold_image_pending forward; that
  * knowledge module was deleted with the old HM baseline in 61d5e0256,
  * before the port. The readings of the Prolog baseline are in the Prolog file's
  * documentation (the same `git show` as above).
  *
  * FIXME (carried from filter_attraction.pl:126 and :582): the value at https://github.com/Atry/private-overlay/issues/1953
  * attraction distance 1 and more is not implemented: it is open how distances k + 1 are merged into
  * the value and what a shape at distance k + 1 is. The value here is
  * distance 0's.
  *
  * FIXME (2026-11-12; CostMonotonicityLawTest https://github.com/Atry/private-overlay/issues/1954
  * leaves this module out): row 1 is not monotone in its children's ranks,
  * and no finite reading makes it so, so the extraction's best entry of a
  * class, or of a class and a reading, is not exact for a parent at row 1
  * (`gezi.extraction.CostModel`, THE CONTRACT). Three things a parent
  * reads of a child beyond its rank:
  *   1. a covered context reprices the child by a second measure: under a
  *      filter, a parent reads the child's `coveredMain` and `coveredRest`,
  *      not its `main` and `rest`. Of two entries of one class, A with Main
  *      10 and covered Main 100 and B with Main 100 and covered Main 10, A
  *      is the class's best, and a filter over A costs more than the same
  *      filter over B;
  *   2. the absorbs carry unbounded sums (`SpineChildren`'s `below` and
  *      `rest`), which an application over the term adds to;
  *   3. a partially applied filter function carries a term
  *      (`ValueSource.Given`).
  * Candidate repairs: one measure for covered and uncovered positions, with
  * the absorbs folded into the rank; or a Pareto set of entries per class in
  * place of one best. What row 1 prefers is unchanged: it is the HM
  * baseline, and no measured defect points at it yet.
  */
object FilterAttraction extends NormalityModule:

  val name: String = "filter_attraction"

  /** Not monotone within a reading (the FIXME above), so an extraction
    * refuses it (`TermOrder.extractionModulesChecked`).
    */
  val meetsExtractionContract: Boolean = false

  def folded(layer: OrderTerm, reading: TermReading): FoldState = state(layer, reading)

  /** The weight of one uncovered position of the height, 33^min(h, 15)
    * (`height_weight/2`).
    */
  private def heightWeight(height: Int): BigInt = BigInt(33).pow(height.min(15))

  private val leafChild: Absorb.SpineChildren = Absorb.SpineChildren(0, heightWeight(0), Rest.empty, false)

  /** `leaf_fold_state/1`. */
  private val leafState: FilterState =
    FilterState(false, Measure(0, heightWeight(0), Rest.empty, 0, Rest.empty), Vector(leafChild), None)

  /** `filter_fold_state/2`. */
  private def state(term: OrderTerm, reading: TermReading): FilterState = term match
    case OrderTerm.Folded(folded, _) => TermOrder.ownState[FilterState](folded)
    case name @ OrderTerm.Name(_) =>
      reading.filterFunction(name) match
        case Some(filter) => filterFunctionApplied(filter.code, filter.holes, filter.fillings, Vector.empty, reading)
        case None =>
          reading.applicationNamed(name) match
            case Some(definition) => state(definition, reading)
            case None             => leafState
    case leaf if TermReading.leafTerm(leaf) => leafState
    case OrderTerm.Parallel(value, criterion, _) =>
      val valueState = state(value, reading)
      val covered = stateCovered(valueState)
      val criterionState = state(criterion, reading)
      val body = spineChildrenApplied(stateChild(valueState), Vector(criterionState))
      covered.copy(operands = Some((body.read, body.measure)))
    case OrderTerm.Choice(Vector())  => leafState
    case OrderTerm.Choice(members)   => statesJoined(members.map(state(_, reading)))
    case OrderTerm.Thunk(code, holes, fillings) =>
      if TermReading.slotPair(code) then filterFunctionApplied(code, holes, fillings, Vector.empty, reading)
      else
        val bodyState = state(TermReading.resolved(code, holes, fillings), reading)
        val (read, measure) = bodyState.operands.getOrElse((bodyState.read, bodyState.measure))
        FilterState(read, measure, Vector(measureChild(read, measure)), None)
    case OrderTerm.Apply(function, argument) => applied(function, Vector(argument), reading)
    case other                               => TermOrder.refused(other)

  /** The head applied to the arguments, the spine flattened within the layer
    * and read through names of applications (`filter_fold_applied/3`).
    */
  private def applied(head: OrderTerm, arguments: Vector[OrderTerm], reading: TermReading): FilterState =
    head match
      case OrderTerm.Apply(function, argument) => applied(function, argument +: arguments, reading)
      case OrderTerm.Folded(folded, _) =>
        absorbsApplied(TermOrder.ownState[FilterState](folded).absorbs, arguments, reading)
      case name @ OrderTerm.Name(_) =>
        reading.filterFunction(name) match
          case Some(filter) => filterFunctionApplied(filter.code, filter.holes, filter.fillings, arguments, reading)
          case None =>
            reading.applicationNamed(name) match
              case Some(definition) => applied(definition, arguments, reading)
              case None             => spineChildrenApplied(leafChild, arguments.map(state(_, reading)))
      case OrderTerm.Thunk(code, holes, fillings) if TermReading.slotPair(code) =>
        filterFunctionApplied(code, holes, fillings, arguments, reading)
      case OrderTerm.Choice(members) if members.nonEmpty =>
        statesJoined(members.map(applied(_, arguments, reading)))
      case OrderTerm.Parallel(value, _, _) => stateCovered(applied(value, arguments, reading))
      case other => absorbsApplied(state(other, reading).absorbs, arguments, reading)

  /** `absorbs_applied/3`. */
  private def absorbsApplied(absorbs: Vector[Absorb], arguments: Vector[OrderTerm], reading: TermReading): FilterState =
    val argumentStates = arguments.map(state(_, reading))
    statesJoined(absorbs.map(absorbApplied(_, arguments, argumentStates, reading)))

  /** `absorb_applied/4`. */
  private def absorbApplied(
      absorb: Absorb,
      arguments: Vector[OrderTerm],
      argumentStates: Vector[FilterState],
      reading: TermReading
  ): FilterState = absorb match
    case children @ Absorb.SpineChildren(_, _, _, _) => spineChildrenApplied(children, argumentStates)
    case Absorb.Covered(inner) => stateCovered(absorbApplied(inner, arguments, argumentStates, reading))
    case Absorb.FilterFunction(remaining, source) =>
      if arguments.size >= remaining then
        val (taken, extra) = arguments.splitAt(remaining)
        val value = source match
          case ValueSource.Given(term)    => term
          case ValueSource.Pending(index) => taken(index)
        valueCovered(value, extra, reading)
      else
        val advanced = source match
          case source @ ValueSource.Given(_) => source
          case ValueSource.Pending(index) =>
            if index < arguments.size then ValueSource.Given(arguments(index))
            else ValueSource.Pending(index - arguments.size)
        filterFunctionPending(remaining - arguments.size, advanced, reading)

  /** The spine whose children are the absorb's and one more per argument:
    * one uncovered position, whose Main is its height's weight added to the
    * children's Mains and whose Main once covered is the sum of the
    * children's Mains (`spine_children_applied/3`).
    */
  private def spineChildrenApplied(children: Absorb.SpineChildren, argumentStates: Vector[FilterState]): FilterState =
    val joined = argumentStates.map(stateChild).foldLeft(children) { (accumulated, child) =>
      Absorb.SpineChildren(
        accumulated.tallest.max(child.tallest),
        accumulated.below + child.below,
        accumulated.rest + child.rest,
        accumulated.read || child.read
      )
    }
    val height = joined.tallest + 1
    val main = joined.below + heightWeight(height)
    FilterState(joined.read, Measure(height, main, joined.rest, joined.below, joined.rest), Vector(joined), None)

  /** The state as one child of a spine (`fold_state_child/2`). */
  private def stateChild(state: FilterState): Absorb.SpineChildren = measureChild(state.read, state.measure)

  private def measureChild(read: Boolean, measure: Measure): Absorb.SpineChildren =
    Absorb.SpineChildren(measure.height, measure.main, measure.rest, read)

  /** A filter function applied to the arguments: applied to all its holes
    * it is its value, covered, applied to the arguments beyond its holes;
    * applied to fewer it is a filter on its value slot's term or on a hole
    * (`filter_function_applied/5`).
    */
  private def filterFunctionApplied(
      code: Code,
      holes: Vector[Hole],
      fillings: Vector[OrderTerm],
      arguments: Vector[OrderTerm],
      reading: TermReading
  ): FilterState =
    TermReading.instantiated(code, holes, fillings, arguments) match
      case (OrderTerm.Parallel(value, _, _), extra) =>
        if arguments.size >= holes.size then valueCovered(value, extra, reading)
        else
          val (valueSlot, _) = TermReading.slotPairSlots(code)
          val position = holes.indexOf(Hole.Bound(valueSlot))
          val source =
            if position >= arguments.size then ValueSource.Pending(position - arguments.size)
            else ValueSource.Given(value)
          filterFunctionPending(holes.size - arguments.size, source, reading)
      case (other, _) => throw IllegalStateException(s"a filter function's code instantiated to $other")

  /** A filter function with holes left whose value comes from the source
    * (`filter_function_pending/3`).
    */
  private def filterFunctionPending(remaining: Int, source: ValueSource, reading: TermReading): FilterState =
    val valueState = source match
      case ValueSource.Given(value) => state(value, reading)
      case ValueSource.Pending(_)   => leafState
    FilterState(true, stateCovered(valueState).measure, Vector(Absorb.FilterFunction(remaining, source)), None)

  /** The value of a filter function applied to all its holes, applied to the
    * arguments beyond them, covered (`filter_value_covered/3`).
    */
  private def valueCovered(value: OrderTerm, extra: Vector[OrderTerm], reading: TermReading): FilterState =
    stateCovered(if extra.isEmpty then state(value, reading) else applied(value, extra, reading))

  /** Every position covered by a filter (`fold_state_covered/2`). */
  private def stateCovered(state: FilterState): FilterState =
    val measure = state.measure
    FilterState(
      true,
      Measure(measure.height, measure.coveredMain, measure.coveredRest, measure.coveredMain, measure.coveredRest),
      state.absorbs.map(Absorb.Covered(_)),
      None
    )

  /** The states of the members of a choice, or of the ways a term extends at
    * the head of a spine, at least one, joined (`fold_states_joined/2`).
    */
  private def statesJoined(states: Vector[FilterState]): FilterState =
    val first = states.head
    val (read, measure, absorbs) = states.tail.foldLeft((first.read, first.measure, first.absorbs)) {
      case ((accumulatedRead, accumulatedMeasure, accumulatedAbsorbs), next) =>
        (accumulatedRead || next.read, measuresJoined(accumulatedMeasure, next.measure), accumulatedAbsorbs ++ next.absorbs)
    }
    FilterState(read, measure, absorbs.sortBy(absorbKey)(using OrderValue.ordering), None)

  /** `measures_joined/3`. */
  private def measuresJoined(first: Measure, second: Measure): Measure =
    val (main, rest) = membersJoined(first.main, first.rest, second.main, second.rest)
    val (coveredMain, coveredRest) =
      membersJoined(first.coveredMain, first.coveredRest, second.coveredMain, second.coveredRest)
    Measure(first.height.min(second.height), main, rest, coveredMain, coveredRest)

  /** The lesser Main, and the two Rests added with one more other member,
    * the other Main (`members_joined/6`).
    */
  private def membersJoined(firstMain: BigInt, firstRest: Rest, secondMain: BigInt, secondRest: Rest): (BigInt, Rest) =
    val rests = firstRest + secondRest
    if firstMain <= secondMain then (firstMain, rests.memberAdded(secondMain))
    else (secondMain, rests.memberAdded(firstMain))

  /** The key absorbs are sorted by, stably, without the value a filter
    * function's source holds (`absorb_key/2`), in Prolog's standard order.
    */
  private def absorbKey(absorb: Absorb): OrderValue = absorb match
    case Absorb.SpineChildren(tallest, below, rest, read) =>
      OrderValue.Compound(
        "spine_children",
        Vector(
          OrderValue.number(tallest),
          OrderValue.Number(below),
          OrderValue.Compound("rest", Vector(OrderValue.Number(rest.count), OrderValue.Number(rest.sum))),
          OrderValue.Atom(if read then "read" else "unread")
        )
      )
    case Absorb.Covered(inner) => OrderValue.Compound("covered", Vector(absorbKey(inner)))
    case Absorb.FilterFunction(remaining, source) =>
      val kind = source match
        case ValueSource.Given(_)       => OrderValue.Atom("given")
        case ValueSource.Pending(index) => OrderValue.Compound("pending", Vector(OrderValue.number(index)))
      OrderValue.Compound("filter_function", Vector(OrderValue.number(remaining), kind))

  def rank(state: FoldState): OrderValue =
    val own = TermOrder.ownState[FilterState](state)
    if !own.read then OrderValue.list(OrderValue.number(1))
    else
      OrderValue.list(
        OrderValue.number(0),
        OrderValue.Number(own.measure.main),
        OrderValue.Number(own.measure.rest.count),
        OrderValue.Number(own.measure.rest.sum)
      )

  def value(state: FoldState): OrderValue =
    val own = TermOrder.ownState[FilterState](state)
    if !own.read then OrderValue.Atom("no_filter")
    else
      OrderValue.Compound(
        "positions",
        Vector(
          OrderValue.Number(own.measure.main),
          OrderValue.Number(own.measure.rest.count),
          OrderValue.Number(own.measure.rest.sum)
        )
      )
