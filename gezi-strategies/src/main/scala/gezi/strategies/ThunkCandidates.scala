package gezi.strategies

import gezi.ir.NativeSpecializer

import gezi.extraction.ContentOrder
import gezi.extraction.CostModel
import gezi.extraction.Entry
import gezi.extraction.Shape
import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** The candidate entries of a thunk's production under `ModuleCostModel`
  * (`CostModel.candidates`), found without listing every combination of its
  * fillings' entries: a closure `λy. s1 (s2 (… (s32 y)))` whose 32 fillings
  * keep two readings each has 2^32 combinations, which ran the native route
  * out of heap (aClosuresNaturalsRunCostsASuccessorDoNotGrow, 2026-11-13).
  *
  * THE DECOMPOSITION. The modules fold a code's body part by part, each
  * part's state a function of its parts' states, so that a part read through
  * its state (`OrderTerm.Folded`) counts as the part itself, and within one
  * reading a part's better state makes no enclosing state worse (the
  * contract of `gezi.extraction.CostModel` at a code's own
  * applications and parallels). So the body's best of each reading is found
  * bottom up: at a slot whose filling occurs once, the filling's entries; at
  * an application, every pair of its function's and its argument's
  * alternatives, the best of each reading kept; at a parallel, its left
  * operand's alternatives over its criterion, which no module prices, of
  * each filling read only there the first entry of each reading by size and
  * content, since a module reads an unpriced child's reading. A
  * filling is read jointly, one combination of their entries at a time,
  * where a part reads more of it than its state: the fillings of slots that
  * occur more than once, those under a code's choice or inner thunk (whose
  * dispatch patterns read whether a filling is λf. f,
  * `TermReading.identityContract`), and, of a thunk of two holes, the
  * function of its body's application (`DispatchPattern.identityContractLayer`).
  * A filling the code does not read is the first of its entries by size and
  * content. Each candidate is priced by `ModuleCostModel.cost` over its
  * whole combination, so that a candidate's cost is the production's; the
  * alternatives only choose which combinations are priced.
  *
  * Among alternatives of one cost and one reading the smaller by size wins,
  * then the first by content position by position (`ContentOrder`), as the
  * extraction breaks its own ties; where a part's worse alternative of one
  * reading gives the thunk the same cost, the extraction's choice among the
  * combinations of equal cost may differ from the one the full product
  * gives, while the cost of each reading's best does not
  * (ThunkCandidatesLawTest).
  */
object ThunkCandidates:

  /** The thunk's candidate entries over its fillings' entries, in filling
    * order.
    */
  def candidates[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      shape: Shape[C],
      thunk: Thunk[Int],
      options: Vector[Vector[Entry[C, ModuleCost]]]
  ): Vector[Entry[C, ModuleCost]] =
    decomposed(model, shape, thunk, options, Objective.CostFirst)

  /** The thunk's least entry of each reading by `ContentOrder` over its
    * fillings' entries, whatever its cost (`CostModel.leastCandidates`): the
    * same decomposition with the alternatives of each part ordered by size,
    * then content position by position. The size of a thunk's entry is one
    * more than the sum of its fillings', so the least of each reading of the
    * whole is made of the least of each reading of its parts.
    */
  def leastCandidates[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      shape: Shape[C],
      thunk: Thunk[Int],
      options: Vector[Vector[Entry[C, ModuleCost]]]
  ): Vector[Entry[C, ModuleCost]] =
    gezi.extraction.CostModel.leastOfEachReading(model, decomposed(model, shape, thunk, options, Objective.SizeFirst))

  /** The fillings, in filling order, that the thunk's candidates settle to
    * their first entry when each filling has as many entries as
    * `entryCounts` says (`gezi.extraction.CostModel.settledChildren`), of
    * the path `decomposed` takes at those numbers: the jointly read
    * fillings, each of more than one entry, when the product of their
    * numbers exceeds the enumeration bound (`CodeCandidates.settledPositions`),
    * and the fillings the code does not read, each of more than one entry,
    * whose first entry is taken at every number.
    */
  def settledFillings[C <: NativeSpecializer & Singleton](model: ModuleCostModel[C], thunk: Thunk[Int], entryCounts: Vector[Int]): Vector[Boolean] =
    val Thunk(code, holes, _) = thunk
    val (joint, unread) =
      if byParts(model, thunk, entryCounts) then
        (CodeCandidates.jointPositions(code, holes, entryCounts.size), CodeCandidates.unreadPositions(code, holes, entryCounts.size))
      else
        val read = readFillings(code, holes, entryCounts.size)
        (jointFillings(code, holes, entryCounts.size), entryCounts.indices.filterNot(read.contains).toSet)
    val settled = CodeCandidates.settledPositions(joint, entryCounts, model.jointReading.enumerationBound) ++ unread.filter(entryCounts(_) > 1)
    entryCounts.indices.toVector.map(settled.contains)

  /** Whether `decomposed` folds the thunk part by part at the numbers of
    * entries given (`CodeCandidates`) rather than reading it whole.
    */
  private def byParts[C <: NativeSpecializer & Singleton](model: ModuleCostModel[C], thunk: Thunk[Int], entryCounts: Vector[Int]): Boolean =
    val Thunk(code, holes, _) = thunk
    model.modules.forall(_.codeFolding.isDefined) && jointProduct(thunk, entryCounts) > BigInt(model.jointReading.wholeFoldLimit) &&
    CodeCandidates.foldsByParts(code, holes, entryCounts.size) &&
    CodeCandidates.contractListingsWithinBound(code, holes, entryCounts, model.jointReading.enumerationBound)

  /** What the alternatives of a part are ordered by. */
  private enum Objective:
    case CostFirst
    case SizeFirst

  private def decomposed[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      shape: Shape[C],
      thunk: Thunk[Int],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      objective: Objective
  ): Vector[Entry[C, ModuleCost]] =
    val Thunk(code, holes, _) = thunk
    val foldings = model.modules.flatMap(_.codeFolding)
    // A thunk whose jointly read fillings have at most the model's
    // `JointReading.wholeFoldLimit` combinations of entries is read whole
    // (`JointReading.measured` gives the measurement of the bound 1). That
    // both paths give the extraction each reading's least cost is the law
    // `CostMonotonicityLaws.wholeFoldBoundKeepsLeastCosts`, and at product 1
    // the same least entry, ties included, `productOneReadWhole`.
    //
    // FIXME (2026-11-16, rewritten 2026-11-24): paths remain. A thunk is read https://github.com/Atry/private-overlay/issues/1961
    // whole (`wholeCandidates`, every combination of its jointly read
    // fillings' entries up to `JointReading.enumerationBound`) when a module of
    // the model has no code folding, when its code holds a choice of more
    // than two members, a choice inside an inner thunk, or a parallel whose
    // criterion is no filling slot (`CodeCandidates.foldsByParts`), or when
    // its contract fillings' entries make more listings than the bound
    // (`CodeCandidates.contractListingsWithinBound`); a choice of two members
    // outside the inner thunks is folded by parts, its dispatch included. The modules
    // of the lemma route (narrow_blocks, compression) and of the native route
    // (specialization_attraction, compression) all fold codes; the other six
    // modules of `BaselineModules.table` do not, and an extraction that names
    // one of them reads every thunk whole. A code fold of a longer choice, of
    // a choice inside an inner thunk and of a criterion read whole would close
    // it.
    if byParts(model, thunk, options.map(_.size))
    then CodeCandidates.candidates(model, foldings, shape, code, holes, options, objective == Objective.CostFirst)
    else wholeCandidates(model, shape, code, holes, options, objective)

  /** The fillings, by position, that the whole fold (`wholeCandidates`) reads
    * jointly: those of the slots `jointSlots` lists.
    */
  def jointFillings(code: Code, holes: Vector[Hole], fillingCount: Int): Vector[Int] =
    val fillingOfSlot = Defunctionalization.slotValues(holes, holes.map(_ => -1), Vector.range(0, fillingCount))
    jointSlots(code, holes).toVector.map(fillingOfSlot).filter(_ >= 0).sorted

  /** The fillings, by position, that the code reads, its inner thunks'
    * fillings included.
    */
  private def readFillings(code: Code, holes: Vector[Hole], fillingCount: Int): Set[Int] =
    val fillingOfSlot = Defunctionalization.slotValues(holes, holes.map(_ => -1), Vector.range(0, fillingCount))
    slotsRead(code).map(fillingOfSlot).filter(_ >= 0)

  /** The candidates of a thunk whose inner thunks are read whole: every
    * combination of the entries of its jointly read fillings, those under an
    * inner thunk or a choice among them, each decomposed over the rest.
    */
  private def wholeCandidates[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      shape: Shape[C],
      code: Code,
      holes: Vector[Hole],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      objective: Objective
  ): Vector[Entry[C, ModuleCost]] =
    val fillingOfSlot = Defunctionalization.slotValues(holes, holes.map(_ => -1), options.indices.toVector)
    val reader = Reader(model, holes, fillingOfSlot, options, objective)
    val read = readFillings(code, holes, options.size)
    val (joint, settled) = CodeCandidates.enumeratedOrSettled(jointFillings(code, holes, options.size), options, model.jointReading.enumerationBound)
    val unread = options.indices.filterNot(read.contains).map(position => position -> CodeCandidates.first(options(position))).toMap ++ settled
    // The product over the jointly read fillings is bounded
    // (`CodeCandidates.enumeratedOrSettled`): above the bound each is settled
    // to its first entry and the code is read once. Since an unpriced child
    // carries its reading, a filter's class has two readings (Value, Closed),
    // and the product doubles with each jointly read filter: on
    // repeated_library_hotspots_inlined_calls_10000_hot/direct with
    // `contest-entries-solo` one thunk, 29 nested lets over 30 fillings, 15 of them filters,
    // has a product of 2^15 = 32,768, which the extraction did not end in
    // 60 s when it enumerated it.
    // FIXME (2026-11-17): https://github.com/Atry/private-overlay/issues/2050
    // above the bound the thunk's entries are not the least over every
    // combination, so its extraction may miss a cheaper term (a narrow block
    // a joint choice of Value and Closed would have allowed). A let's
    // argument such as ((s3 s4) s5) is a closed constant when all its slots
    // are Closed and must parse as an expression otherwise, so grouping a
    // filling's readings by what the code reads at its slot does not merge
    // them. A candidate remedy is a dynamic program over the narrow parse
    // with a summary per operand subcode, which may or may not stay
    // polynomial. The least over every combination under one entry per
    // filling is extraction with sharing, whose exact elimination over the
    // repeated fillings costs R to the power of one more than their induced
    // width, R a filling's number of readings: measured 2026-11-24 on
    // repeated_cses_distinct_numbers_numbers_200000 (seed 20261031, one repetition)
    // under the native route, 25 to 40 readings per repeated filling, 1,600
    // to about 27,000 combinations, a bound of 65,536 running past 300 s.
    // The readings are many because specialization attraction's carries its
    // holes' use counts (`SpecializationReading`); a narrower reading of that
    // module, if its parents can do without the counts, is a candidate fix.
    // The settling depends on the numbers of entries offered, so
    // `CountedExtraction` fixes it from its first run (`CostModel.settledChildren`)
    // and reads such a thunk under the combinations that run kept, in every
    // pass alike.
    // The combinations are drawn on demand (`CostModel.lazyCombinations`) and
    // drawing ends when a stop is requested (`model.stop`): the candidates
    // found so far are given, and the extraction that reads the same signal
    // gives its inputs as written. Unstopped, the candidates and their order
    // are those of `CostModel.combinations`.
    CostModel
      .lazyCombinations(joint.map(options(_)))
      .takeWhile(_ => !model.stop.stopRequested)
      .flatMap { chosen =>
        val fixed = joint.zip(chosen).toMap ++ unread
        reader.alternatives(code, fixed).map { alternative =>
          val entries = options.indices.toVector.map(position => fixed.getOrElse(position, alternative.chosen(position)))
          Entry(model.cost(shape, entries.map(_.cost)), shape, entries)
        }
      }
      .toVector

  /** The number of combinations the candidates of the thunk list jointly:
    * the product of the numbers of entries of its jointly read fillings.
    */
  def jointProduct(thunk: Thunk[Int], optionCounts: Vector[Int]): BigInt =
    val Thunk(code, holes, _) = thunk
    jointFillings(code, holes, optionCounts.size).map(position => BigInt(optionCounts(position))).product

  /** A part of the body: its cost, the modules' fold of it with the fillings
    * read jointly in place, and the entries chosen for the other fillings it
    * reads, by filling position.
    */
  private final case class Alternative[C <: NativeSpecializer & Singleton](cost: ModuleCost, chosen: Map[Int, Entry[C, ModuleCost]]):
    def size: BigInt = chosen.values.map(_.size).sum

  private final case class Reader[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      holes: Vector[Hole],
      fillingOfSlot: Vector[Int],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      objective: Objective
  ):

    /** The best alternative of each reading of the part, the fillings in
      * `fixed` read as given.
      */
    def alternatives(code: Code, fixed: Map[Int, Entry[C, ModuleCost]]): Vector[Alternative[C]] = code.layer match
      case Slot(slot) if fillingOfSlot(slot) >= 0 && !fixed.contains(fillingOfSlot(slot)) =>
        val position = fillingOfSlot(slot)
        pruned(options(position).map(entry => Alternative(entry.cost, Map(position -> entry))))
      case Apply(function, argument) =>
        val arguments = alternatives(argument, fixed)
        pruned(
          for
            functionAlternative <- alternatives(function, fixed)
            argumentAlternative <- arguments
          yield combined(functionAlternative, argumentAlternative, OrderTerm.Apply(_, _))
        )
      case Parallel(left, right) =>
        val criteria = wholes(right, fixed)
        pruned(
          for
            leftAlternative <- alternatives(left, fixed)
            criterion <- criteria
          yield combined(leftAlternative, criterion, OrderTerm.Parallel(_, _, false))
        )
      case _ => wholes(code, fixed)

    /** The part read whole, the fillings in `fixed` as given and every other
      * filling, read only in a criterion, unpriced: of each such filling the
      * first of its entries of each reading by size and content, since a
      * module reads an unpriced child's reading (`OrderTerm.Unpriced`); the
      * best alternative of each reading.
      */
    private def wholes(code: Code, fixed: Map[Int, Entry[C, ModuleCost]]): Vector[Alternative[C]] =
      val free = slotsRead(code).toVector.map(fillingOfSlot).filter(position => position >= 0 && !fixed.contains(position)).distinct.sorted
      pruned(CostModel.combinations(free.map(position => firstOfEachReading(options(position)))).map { chosen =>
        val unpriced = free.zip(chosen).toMap
        val terms = model.modules.indices.toVector.map(position => resolved(code, fixed, unpriced, position))
        val states = model.modules.zip(terms).map((module, term) => module.folded(term, model.reading))
        val identity = terms.headOption.exists(TermReading.identityContract)
        Alternative(costOf(states, identity), unpriced)
      })

    /** The first entry of each reading among the entries, by size, then
      * content, in the order the readings first occur.
      */
    private def firstOfEachReading(entries: Vector[Entry[C, ModuleCost]]): Vector[Entry[C, ModuleCost]] =
      entries
        .foldLeft(Vector.empty[Vector[Entry[C, ModuleCost]]]) { (groups, entry) =>
          groups.indexWhere(group => group.headOption.exists(member => model.sameReading(member.cost, entry.cost))) match
            case -1       => groups :+ Vector(entry)
            case position => groups.updated(position, groups(position) :+ entry)
        }
        .map(CodeCandidates.first)

    /** The part's term at the module, its holes `Bound`, the fillings in
      * `fixed` read through their states and those in `unpriced` through
      * their readings at the module (`OrderTerm.Unpriced`).
      */
    private def resolved(
        code: Code,
        fixed: Map[Int, Entry[C, ModuleCost]],
        unpriced: Map[Int, Entry[C, ModuleCost]],
        modulePosition: Int
    ): OrderTerm[C] =
      val module = model.modules(modulePosition)
      val fillings = options.indices.toVector.map(position =>
        fixed.get(position) match
          case Some(entry) => OrderTerm.Folded[C](entry.cost.states(modulePosition), entry.cost.identityContract)
          case None =>
            val entry = unpriced.getOrElse(position, CodeCandidates.first(options(position)))
            OrderTerm.Unpriced[C](module.reading(entry.cost.states(modulePosition)))
      )
      TermReading.resolved(code, holes, fillings)

    /** The application or parallel of two parts, each read through its
      * state.
      */
    private def combined(left: Alternative[C], right: Alternative[C], layer: (OrderTerm[C], OrderTerm[C]) => OrderTerm[C]): Alternative[C] =
      val states = model.modules.indices.toVector.map(position =>
        model.modules(position).folded(
          layer(
            OrderTerm.Folded[C](left.cost.states(position), left.cost.identityContract),
            OrderTerm.Folded[C](right.cost.states(position), right.cost.identityContract)
          ),
          model.reading
        )
      )
      Alternative(costOf(states, false), left.chosen ++ right.chosen)

    private def costOf(states: Vector[FoldState], identity: Boolean): ModuleCost =
      ModuleCost(states, model.modules.zip(states).map((module, state) => module.rank(state)), identity)

    /** The best alternative of each reading, in the order the readings
      * first occur.
      */
    private def pruned(found: Vector[Alternative[C]]): Vector[Alternative[C]] =
      found.foldLeft(Vector.empty[Alternative[C]]) { (kept, next) =>
        kept.indexWhere(alternative => model.sameReading(alternative.cost, next.cost)) match
          case -1       => kept :+ next
          case position => if better(next, kept(position)) then kept.updated(position, next) else kept
      }

    /** Less cost (unless the objective orders by size alone); at one cost,
      * less size, then the first by content at the first filling where the
      * two differ.
      */
    private def better(candidate: Alternative[C], alternative: Alternative[C]): Boolean =
      val order = objective match
        case Objective.CostFirst => model.ordering.compare(candidate.cost, alternative.cost)
        case Objective.SizeFirst => 0
      if order != 0 then order < 0
      else
        val bySize = candidate.size.compare(alternative.size)
        if bySize != 0 then bySize < 0
        else
          candidate.chosen.keys.toVector.sorted.view
            .map(position => ContentOrder.compare(candidate.chosen(position), alternative.chosen(position)))
            .find(_ != 0)
            .exists(_ < 0)

  /** The slots of the code, its inner thunks' fillings included and their
    * codes, whose slots are their own, not.
    */
  private def slotsRead(code: Code): Set[Int] = occurrences(code).keySet

  private def occurrences(code: Code): Map[Int, Int] = code.layer match
    case Slot(slot)                => Map(slot -> 1)
    case Apply(function, argument) => summed(Vector(function, argument))
    case Parallel(left, right)     => summed(Vector(left, right))
    case Choice(left, right)       => summed(Vector(left, right))
    case Thunk(_, _, fillings)     => summed(fillings)

  private def summed(codes: Vector[Code]): Map[Int, Int] =
    codes.map(occurrences).foldLeft(Map.empty[Int, Int])((sum, counts) =>
      counts.foldLeft(sum) { case (total, (slot, count)) => total.updated(slot, total.getOrElse(slot, 0) + count) }
    )

  /** The slots read jointly: those that occur more than once, those under a
    * choice or an inner thunk, and, of a thunk of two holes, the function of
    * its body's application.
    */
  private def jointSlots(code: Code, holes: Vector[Hole]): Set[Int] =
    val repeated = occurrences(code).collect { case (slot, count) if count > 1 => slot }.toSet
    val headed = (holes.size, code.layer) match
      case (2, Apply(Code.Slot(function), _)) => Set(function)
      case _                                            => Set.empty[Int]
    repeated ++ underRecognizers(code) ++ headed

  private def underRecognizers(code: Code): Set[Int] = code.layer match
    case Slot(_)                   => Set.empty
    case Apply(function, argument) => underRecognizers(function) ++ underRecognizers(argument)
    case Parallel(left, right)     => underRecognizers(left) ++ underRecognizers(right)
    case Choice(_, _) | Thunk(_, _, _) => slotsRead(code)
