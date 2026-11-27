package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.ir.NativeSpecializer

import com.yang_bo.gezi.standardlibrary.Property

/** How a closure's body uses the argument standing in one of its holes, at the
  * positions `specialization_attraction` prices: the number of its occurrences;
  * the number of those that are the argument of an application, which the body
  * counts as unfiltered applications while the hole is empty; and the number
  * that are the left operand of a parallel, which it counts as unfiltered left
  * operands while the hole is empty.
  */
final case class HoleUse(
    occurrences: Int,
    unfilteredArguments: Int,
    unfilteredLefts: Int
):

  /** The uses of both, summed. */
  def +(other: HoleUse): HoleUse =
    HoleUse(
      occurrences + other.occurrences,
      unfilteredArguments + other.unfilteredArguments,
      unfilteredLefts + other.unfilteredLefts
    )

  /** The uses as many times over. */
  def *(times: Int): HoleUse = HoleUse(
    occurrences * times,
    unfilteredArguments * times,
    unfilteredLefts * times
  )

object HoleUse:

  /** The use of a hole the term does not read. */
  val unused: HoleUse = HoleUse(0, 0, 0)

/** The root reading of a spelling, the part of the state a parent reads: a
  * filter; the contract of a closure whose body filters, with the uses of its
  * holes still to be filled, in lambda order; a part of an occurrence's tag
  * still missing some arguments; or other.
  */
enum SpecializationRoot:
  case Filter
  case Contract(holes: Vector[HoleUse])
  case Marker(missing: Int)
  case Other

  /** The root reading counts as a filter's for the parent (`filter_reading/1`).
    */
  def filterReading: Boolean = this match
    case Filter | Contract(_) => true
    case _                    => false

/** The fold state of `specialization_attraction` (`specialization(Count,
  * Root)`): the number of unfiltered applications and the root reading; the
  * number of parallels whose left operand's root reading is no filter's
  * (`unfilteredLefts`); the use of each hole free in the term (`holes`, by the
  * leaf that stands for it: a `Bound` hole of a code's body, or the
  * `Metavariable` of negative index a closure puts in each of its own holes);
  * and the hole whose filling's root reading is the term's (`rootHole`): the
  * hole itself, or a tag given its last argument there.
  */
final case class SpecializationState[C <: NativeSpecializer & Singleton](
    count: BigInt,
    root: SpecializationRoot,
    unfilteredLefts: BigInt,
    holes: Map[OrderTerm[C], HoleUse],
    rootHole: Option[OrderTerm[C]]
) extends FoldState

/** The states of the terms with no free hole and no parallel. */
object SpecializationState:
  def apply[C <: NativeSpecializer & Singleton](
      count: BigInt,
      root: SpecializationRoot
  ): SpecializationState[C] =
    SpecializationState(count, root, 0, Map.empty, None)

/** The reading of `specialization_attraction`: the root reading, and the uses
  * of the free holes with the hole the root reads as, empty of every term with
  * no free hole, which every entry of the extraction is.
  */
final case class SpecializationReading[C <: NativeSpecializer & Singleton](
    root: SpecializationRoot,
    holes: Map[OrderTerm[C], HoleUse],
    rootHole: Option[OrderTerm[C]]
) extends ModuleReading

/** The specialization attractor of the native route's compilation, the port of
  * `gezi/prolog/gezi/baseline/specialization_attraction.pl`, whose module
  * documentation (THE VALUE, THE ROOT READING, THE OCCURRENCE TAGS) this
  * follows. The value, which is the rank, is the pair `Count-Unfiltered`: Count
  * the number of applications whose argument is no filter, a choice counted as
  * all its members, which a run evaluates, and read as a filter only when every
  * member is one (a dispatch pattern is priced as what the refinement runs of
  * it, `ModuleCostModel`, THE PRICE OF A CHOICE, and `TermReading.resolved` for
  * a code), a parallel as its left operand, its right operand being a
  * criterion, and a closure as its body; Unfiltered 0 when the root reading is
  * a filter's or a contract's, 1 otherwise. The pair is paired with
  * UnfilteredLefts, the number of parallels whose left operand's root reading
  * is no filter's, summed as Count is: at one count a parallel over a filter,
  * such as a specialization that keeps its range, ranks better than one over
  * the same class spelled without it, which `Compression` would prefer as the
  * smaller (2026-11-12: a class read under an application and under a parallel
  * was spelled two ways, and the parallel's spelling lost the range the native
  * route needs), and so does a term with such a parallel inside, such as the
  * typed member `F (A ∥ D)` of a specialization over a typed A; counted at the
  * root only, it was lost under the application. The range of a
  * specialization's typed member that the dispatch recognizer accepts,
  * `F (A ∥ D) ∥ R` (`OrderTerm.Parallel`'s `specializationRange`), counts no
  * unfiltered left: the refinement turns it into a fallback point on the
  * native's own output, a decode of a value the native built, not a filter over
  * an unchecked value; a hand-written `λx. g x ∥ R` still counts g's output.
  * Counted there, every typed member carried one unfiltered left its untyped
  * spelling did not, which the next typed member's domain over that untyped
  * output gave back: a closure's chain of successors cost as much with every
  * other one untyped, the smaller spelling, which runs no native
  * (aClosuresNaturalsRunCostsASuccessorDoNotGrow, 2026-11-13, 2 native calls of
  * 8). Summed over parts whose root readings are in their readings, the mark
  * being syntax, it is monotone within a reading and no part of it. An
  * application of a closure whose root reading is `contract` counts as that
  * body with the argument in its hole: the closure's count is its body's with
  * its holes empty, each empty hole a leaf that reads as no filter; the
  * application fills the first hole still empty (`HoleUse`), adding the
  * argument's count once per occurrence and, when the argument reads as a
  * filter, taking back the unfiltered applications and left operands the empty
  * hole was counted in; the result reads as a contract while holes remain and
  * as a filter after the last, the body's root. A closure whose body is itself
  * a contract with holes still empty, such as a curried function's typed member
  * `λx. C (F (x ∥ D))`, is a contract of its own holes and then the body's: its
  * arguments past its own fill the body's (2026-11-13, the same fold's step,
  * whose typed cons is that closure). A contract of two holes such as
  * `λf y. f (y ∥ T) ∥ T` read as a filter after its first argument, so its
  * second, filtered in the body, was counted as an unfiltered argument: a
  * fold's step typed by it cost as much with its cons untyped, `Compression`
  * took that smaller spelling, and the step's range check failed on a list cons
  * had not built (strictRunsTheProgramsHindleyMilnerTypes, 2026-11-13). The
  * parts of an occurrence's tag, the defines with the front end's property
  * `occurrence(Role)` applied to fewer arguments than their role gives them,
  * count as their arguments do and add nothing; the application that gives a
  * tag its last argument reads as that argument, so that a tagged closure
  * `C t c` reads as the closure c, a contract when c is one (the extraction
  * keeps an entry of each reading, and the tag's application read as other
  * whatever c was, so the tag of a fold's step took the step's untyped
  * spelling, the smaller under `Compression`, and the native route lost the
  * step's typed successor; probe of 2026-11-12 on
  * `aFoldUnderATypedConstructor`).
  *
  * A native storage the e-graph keeps as a leaf (`NativeStorage.leafInEGraph`,
  * a storage of constant size, which reaches the production as a name) counts
  * no unfiltered application and no unfiltered left, and reads as a filter: it
  * is the term it stands for, `C (f1 ∥ F1) … ∥ T`, which the code that reads
  * it, the JIT and the natives, reads as its own head, its `∥ T` dropped by the
  * unique spelling's pattern theorem
  * (`docs/design/gezi-set-equations-proofs.md`, section 23), whose premise the
  * facts check per representation (`com.yang_bo.gezi.jit.UniqueSpellingPremise`), so no
  * filter is left to check at run time, as a specialization range counts none.
  * It is a rule of its own, not read off the storage's view, whose constructor
  * counts nothing only where the extractor takes it for a production name. A
  * storage the e-graph reads through its one-layer view (a list's cell, a
  * declared family's value) is priced by the view's layers as any written term
  * is, its fields by their own classes.
  */
object SpecializationAttraction extends ConfigurationFreeModule:

  val name: String = "specialization_attraction"

  val meetsExtractionContract: Boolean = true

  def folded[C <: NativeSpecializer & Singleton](
      layer: OrderTerm[C],
      reading: TermReading[C]
  ): FoldState = state(layer, reading)

  /** The arguments a define of the role takes to make an occurrence or a tag
    * (`role_arguments/2`).
    */
  private def roleArguments(role: Property): Int = role match
    case Property.NameMarker    => 2
    case Property.ClosureMarker => 2
    case Property.TagNext       => 1
    case Property.TagOrigin     => 0
    case other                  =>
      throw IllegalStateException(
        s"$other is no front end entry of the occurrences (TermReading.occurrenceRoles)"
      )

  /** The state of the term, a function of its parts' states, so that a part
    * read through its state (`OrderTerm.Folded`) counts as the part itself.
    *
    * FIXME (2026-11-13): a hole is counted as an unfiltered argument only
    * https://github.com/Atry/private-overlay/issues/1959 where the argument
    * reads as the hole (`rootHole`); inside a choice that is an argument,
    * `f (y + z)`, the choice reads as no filter while its holes are empty and
    * may read as one when they are filled, which no use records, so the
    * application of the closure to filters still counts that application. No
    * measured case meets one.
    */
  private def state[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C],
      reading: TermReading[C]
  ): SpecializationState[C] = term match
    case OrderTerm.Folded(folded, _) =>
      TermOrder.ownState[SpecializationState[C]](folded)
    // A native storage leaf: a filter with none left to check (the object's Scaladoc).
    case OrderTerm.Name(instruction)
        if com.yang_bo.gezi.ir.NativeStorage.stored(instruction.representation) =>
      SpecializationState(0, SpecializationRoot.Filter, 0, Map.empty, None)
    case OrderTerm.Name(instruction) =>
      val missing = reading.occurrenceRoles.get(instruction).map(roleArguments)
      SpecializationState(
        0,
        missing
          .filter(_ > 0)
          .fold(SpecializationRoot.Other)(SpecializationRoot.Marker(_))
      )
    case hole if standsForAHole(hole) =>
      SpecializationState(
        0,
        SpecializationRoot.Other,
        0,
        Map(hole -> HoleUse(1, 0, 0)),
        Some(hole)
      )
    case leaf if TermReading.leafTerm(leaf) =>
      SpecializationState(0, SpecializationRoot.Other)
    case OrderTerm.Apply(function, argument) =>
      val functionState = state(function, reading)
      val argumentState = state(argument, reading)
      val both = functionState.count + argumentState.count
      val lefts = functionState.unfilteredLefts + argumentState.unfilteredLefts
      functionState.root match
        case SpecializationRoot.Marker(missing) =>
          SpecializationState(
            both,
            if missing > 1 then SpecializationRoot.Marker(missing - 1)
            else argumentState.root,
            lefts,
            added(functionState.holes, argumentState.holes),
            if missing > 1 then None else argumentState.rootHole
          )
        case SpecializationRoot.Contract(use +: rest) =>
          val filled = argumentState.root.filterReading
          SpecializationState(
            functionState.count + argumentState.count * use.occurrences - (if filled
                                                                           then
                                                                             use.unfilteredArguments
                                                                           else
                                                                             0),
            if rest.isEmpty then SpecializationRoot.Filter
            else SpecializationRoot.Contract(rest),
            functionState.unfilteredLefts + argumentState.unfilteredLefts * use.occurrences -
              (if filled then use.unfilteredLefts else 0),
            added(
              added(
                functionState.holes,
                scaled(argumentState.holes, use.occurrences)
              ),
              direct(
                argumentState.rootHole,
                HoleUse(0, use.unfilteredArguments, use.unfilteredLefts)
              )
            ),
            None
          )
        case _ =>
          val unfiltered = if argumentState.root.filterReading then 0 else 1
          SpecializationState(
            both + unfiltered,
            SpecializationRoot.Other,
            lefts,
            added(
              added(functionState.holes, argumentState.holes),
              direct(argumentState.rootHole, HoleUse(0, unfiltered, 0))
            ),
            None
          )
    case OrderTerm.Parallel(left, _, specializationRange) =>
      val leftState = state(left, reading)
      val unfiltered =
        if specializationRange || leftState.root.filterReading then 0 else 1
      SpecializationState(
        leftState.count,
        SpecializationRoot.Filter,
        leftState.unfilteredLefts + unfiltered,
        added(
          leftState.holes,
          direct(leftState.rootHole, HoleUse(0, 0, unfiltered))
        ),
        None
      )
    case OrderTerm.Choice(Vector()) =>
      SpecializationState(0, SpecializationRoot.Other)
    case OrderTerm.Choice(members) =>
      val states = members.map(state(_, reading))
      val root = if states.forall(_.root.filterReading) then
        SpecializationRoot.Filter
      else SpecializationRoot.Other
      SpecializationState(
        states.map(_.count).sum,
        root,
        states.map(_.unfilteredLefts).sum,
        states.map(_.holes).foldLeft(Map.empty)(added),
        None
      )
    case OrderTerm.Thunk(code, holes, fillings) =>
      val first = fillings.map(freeMarkers).foldLeft(0)(_ max _) + 1
      val markers = holes.indices.toVector.map(position =>
        OrderTerm.Metavariable[C](-(first + position))
      )
      val (body, _) = TermReading.instantiated(code, holes, fillings, markers)
      val bodyState = state(body, reading)
      val own =
        markers.map(marker => bodyState.holes.getOrElse(marker, HoleUse.unused))
      val root = bodyState.root match
        case SpecializationRoot.Contract(remaining) =>
          SpecializationRoot.Contract(own ++ remaining)
        case filter if filter.filterReading && own.nonEmpty =>
          SpecializationRoot.Contract(own)
        case filter if filter.filterReading => SpecializationRoot.Filter
        case _                              => SpecializationRoot.Other
      SpecializationState(
        bodyState.count,
        root,
        bodyState.unfilteredLefts,
        bodyState.holes -- markers,
        None
      )
    case other => TermOrder.refused(other)

  /** A leaf that stands for a hole: a hole of a code's body, or the
    * metavariable a closure puts in one of its own holes, of negative index,
    * which no lemma side has.
    */
  private def standsForAHole[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): Boolean = term match
    case OrderTerm.Bound(_)            => true
    case OrderTerm.Metavariable(index) => index < 0
    case _                             => false

  /** The greatest magnitude of a closure's metavariable free in the term, 0
    * when none is, so that a closure's own metavariables are not those of an
    * enclosing closure that its fillings hold.
    */
  private def freeMarkers[C <: NativeSpecializer & Singleton](
      term: OrderTerm[C]
  ): Int = term match
    case OrderTerm.Metavariable(index) if index < 0 => -index
    case OrderTerm.Folded(folded, _)                =>
      TermOrder
        .ownState[SpecializationState[C]](folded)
        .holes
        .keys
        .map(freeMarkers)
        .foldLeft(0)(_ max _)
    case OrderTerm.Apply(function, argument) =>
      freeMarkers(function) max freeMarkers(argument)
    case OrderTerm.Parallel(left, right, _) =>
      freeMarkers(left) max freeMarkers(right)
    case OrderTerm.Choice(members) =>
      members.map(freeMarkers).foldLeft(0)(_ max _)
    case OrderTerm.Thunk(_, _, fillings) =>
      fillings.map(freeMarkers).foldLeft(0)(_ max _)
    case _ => 0

  /** The uses of both, summed hole by hole. */
  private def added[C <: NativeSpecializer & Singleton](
      left: Map[OrderTerm[C], HoleUse],
      right: Map[OrderTerm[C], HoleUse]
  ): Map[OrderTerm[C], HoleUse] =
    right.foldLeft(left) { case (sum, (hole, use)) =>
      sum.updated(hole, sum.getOrElse(hole, HoleUse.unused) + use)
    }

  /** The uses as many times over. */
  private def scaled[C <: NativeSpecializer & Singleton](
      uses: Map[OrderTerm[C], HoleUse],
      times: Int
  ): Map[OrderTerm[C], HoleUse] =
    uses.map((hole, use) => hole -> use * times)

  /** The unfiltered applications and left operands the hole is counted in where
    * a term reads as that hole.
    */
  private def direct[C <: NativeSpecializer & Singleton](
      rootHole: Option[OrderTerm[C]],
      use: HoleUse
  ): Map[OrderTerm[C], HoleUse] =
    rootHole.filter(_ => use != HoleUse.unused).map(hole => hole -> use).toMap

  def rank(state: FoldState): OrderValue = value(state)

  /** The root reading: a parent's count and root read it (Apply's Marker,
    * Contract and filter cases), and at one count no order of the root readings
    * serves both an application's function and its argument (a filter saves the
    * argument's count, a tag the function's). And the free holes' uses with the
    * hole the root reads as, which a closure over the term reads; of every
    * entry of the extraction, none.
    */
  override def reading(state: FoldState): ModuleReading =
    val own = TermOrder.ownState[SpecializationState[?]](state)
    SpecializationReading(own.root, own.holes, own.rootHole)

  def value(state: FoldState): OrderValue =
    val own = TermOrder.ownState[SpecializationState[?]](state)
    OrderValue.pair(
      OrderValue.pair(
        OrderValue.Number(own.count),
        OrderValue.number(if own.root.filterReading then 0 else 1)
      ),
      OrderValue.Number(own.unfilteredLefts)
    )

  /** The state of a code, part by part, as `state` reads a thunk: an
    * application or a parallel over its parts read through their states, a slot
    * the state of what it holds, and a hole the metavariable a closure puts in
    * it (`standsForAHole`), one for each depth and position, so that an inner
    * thunk's holes are not its enclosing thunk's; a thunk, inner or closed, its
    * code's state with its own holes' uses taken out into its root reading, as
    * `state`'s `OrderTerm.Thunk`. A filling its code does not read counts
    * nothing, as it does in `TermReading.instantiated`.
    */
  override def codeFolding[C <: NativeSpecializer & Singleton]
      : Option[CodeFolding[C]] = Some(
    new CodeFolding[C]:
      def folded(layer: CodeFold[C], reading: TermReading[C]): FoldState =
        layer match
          case CodeFold.Filling(term, _)             => state(term, reading)
          case CodeFold.InnerFilling(part)           => part
          case CodeFold.HoleSlot(depth, position, _) =>
            state(marker(depth, position), reading)
          case CodeFold.Apply(function, argument) =>
            state(
              OrderTerm.Apply(
                OrderTerm.Folded[C](function, false),
                OrderTerm.Folded[C](argument, false)
              ),
              reading
            )
          case CodeFold.Parallel(left, criterion) =>
            state(
              OrderTerm.Parallel(
                OrderTerm.Folded[C](left, false),
                OrderTerm.Folded[C](criterion, false),
                specializationRange = false
              ),
              reading
            )
          case CodeFold.RangeParallel(left, range) =>
            state(
              OrderTerm.Parallel(
                OrderTerm.Folded[C](left, false),
                OrderTerm.Folded[C](range, false),
                specializationRange = true
              ),
              reading
            )
          case CodeFold.Choice(_, Some(dispatched)) => dispatched
          case CodeFold.Choice(members, None)       =>
            state(
              OrderTerm.Choice(members.map(OrderTerm.Folded(_, false))),
              reading
            )
          case CodeFold.InnerThunk(depth, _, holes, _, body, _) =>
            closed(depth + 1, holes.size, body)
          case CodeFold.Closing(_, holes, body, _, _) =>
            closed(0, holes.size, body)
      def rank(state: FoldState): OrderValue =
        SpecializationAttraction.rank(state)
      def reading(state: FoldState): ModuleReading =
        SpecializationAttraction.reading(state)
  )

  /** The metavariable standing in the hole at the position of the thunk `depth`
    * thunks in: a negative index none of an enclosing thunk's has, by Cantor's
    * pairing of the two.
    */
  private def marker[C <: NativeSpecializer & Singleton](
      depth: Int,
      position: Int
  ): OrderTerm[C] =
    OrderTerm.Metavariable[C](
      -(1 + (depth + position) * (depth + position + 1) / 2 + position)
    )

  /** The state of a thunk whose code's state is given, its holes `depth` thunks
    * in: as `state`'s `OrderTerm.Thunk`.
    */
  private def closed[C <: NativeSpecializer & Singleton](
      depth: Int,
      holeCount: Int,
      body: FoldState
  ): SpecializationState[C] =
    val bodyState = TermOrder.ownState[SpecializationState[C]](body)
    val markers = Vector.tabulate(holeCount)(marker[C](depth, _))
    val own =
      markers.map(marker => bodyState.holes.getOrElse(marker, HoleUse.unused))
    val root = bodyState.root match
      case SpecializationRoot.Contract(remaining) =>
        SpecializationRoot.Contract(own ++ remaining)
      case filter if filter.filterReading && own.nonEmpty =>
        SpecializationRoot.Contract(own)
      case filter if filter.filterReading => SpecializationRoot.Filter
      case _                              => SpecializationRoot.Other
    SpecializationState(
      bodyState.count,
      root,
      bodyState.unfilteredLefts,
      bodyState.holes -- markers,
      None
    )
