package gezi.strategies

import gezi.ir.NativeSpecializer

import gezi.extraction.ContentOrder
import gezi.extraction.CostModel
import gezi.extraction.Entry
import gezi.extraction.Shape
import gezi.frontend.Defunctionalization
import gezi.ir.Code
import gezi.ir.DispatchPattern
import gezi.ir.SpecializationRange
import gezi.ir.Hole
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** A thunk's candidates by a dynamic program over its code, inner thunks'
  * codes included, when every module of the model folds codes
  * (`NormalityModule.codeFolding`, `CodeFold`) and the fillings
  * `ThunkCandidates` would read jointly have more combinations of entries
  * than the model's `JointReading.wholeFoldLimit` (`ThunkCandidates.jointProduct`;
  * at the bound or below the thunk is read whole,
  * `CostMonotonicityLaws.productOneReadWhole`): each part of the code keeps
  * its least alternative of each reading, the readings being the modules'
  * readings of the part's code state, as `ThunkCandidates` keeps them over
  * a code whose inner thunks it reads whole. The fillings a part of the
  * code reads more than once, counted through inner thunks (an inner
  * filling read twice reads its slots twice), take one entry everywhere:
  * they are listed jointly, one combination of their entries at a time, as
  * `ThunkCandidates` lists its jointly read fillings, so that the parts
  * choose only the fillings read once. Each candidate is priced by
  * `ModuleCostModel.cost` over its whole combination; the parts only choose
  * which combinations are priced.
  *
  * A choice of two members outside the code's inner thunks is folded by
  * parts (`CodeFold.Choice`), read as the dispatch patterns read it: one
  * choice of its members, a specialization's typed member, or a judgment's
  * value. The dispatch reads of the fillings only whether a contract slot's
  * filling is λf. f (`DispatchPattern.typedApplications`), and a thunk read
  * as a contract ends its contract domains with its contract filling's;
  * both are part of an entry's reading (`ModuleCostModel.sameReading`), so
  * the candidates are listed once for each value of both of the fillings
  * in such slots, each filling's entries restricted to that value
  * (`candidates`), and within one the dispatch is known. The listings are
  * at most the product of the contract fillings' numbers of entries, which
  * `ThunkCandidates` keeps within `JointReading.enumerationBound` by reading
  * a thunk whole above it (`contractListingsWithinBound`), and each listing
  * enumerates the jointly read fillings within the same bound
  * (`enumeratedOrSettled`), so a thunk's reading evaluates its code at most
  * the square of the bound times. A choice's parts are the combinations of
  * its two members' parts, at most the product of their numbers of readings;
  * a typed member read with its range is made of its application's and its
  * range's parts, so a ranged choice's parts are at most the product of
  * three such numbers. A choice of more members, a choice inside an
  * inner thunk, and a parallel whose criterion is no slot of a filling of
  * the thunk are not folded by parts (`foldsByParts`): `ThunkCandidates`
  * reads such a thunk whole.
  */
object CodeCandidates:

  /** What the dispatch patterns read a choice of two codes as
    * (`choiceReading`).
    */
  enum ChoiceReading:

    /** One choice of its members. */
    case Plain

    /** The member at the position: a specialization's typed member with no
      * range, or with a contract, or a judgment's value.
      */
    case Member(position: Int)

    /** The member at the position, a specialization's typed member
      * `F (A ∥ D) ∥ R`, read with its range marked.
      */
    case Ranged(position: Int)

  /** Whether the code is folded by parts: every choice it holds is of two
    * members and outside its inner thunks, and the criterion of each of its
    * parallels is a slot that holds a filling of the thunk, directly or
    * through an inner thunk's filling that is that slot.
    */
  def foldsByParts(code: Code, holes: Vector[Hole], fillingCount: Int): Boolean =
    val fillingOfSlot = Defunctionalization.slotValues(holes, holes.map(_ => Origin.Elsewhere), Vector.tabulate(fillingCount)(Origin.Outer(_)))
    folds(code, fillingOfSlot, outermost = true)

  /** Where a slot's value comes from, as far as a criterion is concerned. */
  private enum Origin:
    case Outer(position: Int)
    case Elsewhere

  private def folds(code: Code, origins: Vector[Origin], outermost: Boolean): Boolean = code.layer match
    case Slot(_)                   => true
    case Apply(function, argument) => folds(function, origins, outermost) && folds(argument, origins, outermost)
    case Parallel(left, right) =>
      folds(left, origins, outermost) && (right.layer match
        case Slot(slot) => origins.lift(slot).exists { case Origin.Outer(_) => true; case _ => false }
        case _          => false)
    case Choice(_, _) =>
      val Code.ChoiceMembers(members) = code
      outermost && readAsOneChoice(code) && members.forall(folds(_, origins, outermost))
    case Thunk(inner, innerHoles, fillings) =>
      fillings.forall(folds(_, origins, outermost)) && {
        val innerOrigins = Defunctionalization.slotValues(
          innerHoles,
          innerHoles.map(_ => Origin.Elsewhere),
          fillings.map(filling =>
            filling.layer match
              case Slot(slot) => origins.lift(slot).getOrElse(Origin.Elsewhere)
              case _          => Origin.Elsewhere
          )
        )
        folds(inner, innerOrigins, outermost = false)
      }

  /** Whether the choice has two members, the choices folded by parts: a
    * choice's parts are the combinations of its members' parts
    * (`Reader.chosen`), at most the product of their numbers of readings,
    * which more members would raise to a power of their number.
    */
  private def readAsOneChoice(code: Code): Boolean =
    val Code.ChoiceMembers(members) = code
    members.size == 2

  /** Whether the candidates' listings by contract value (`candidates`), at
    * most the product of the contract fillings' numbers of entries, are
    * within `bound` (`JointReading.enumerationBound`): above it the thunk is
    * read whole (`ThunkCandidates`).
    */
  def contractListingsWithinBound(code: Code, holes: Vector[Hole], entryCounts: Vector[Int], bound: Long): Boolean =
    productWithinBound(contractFillings(code, holes, entryCounts.size).toVector.sorted.map(entryCounts(_)), 0, 1, bound)

  /** What the dispatch patterns read a choice of two codes as, the slots
    * whose filling is λf. f given (`identity`), as `TermReading.resolved`
    * reads it: one choice of its members, or the member at a position, the
    * typed member of a specialization or a judgment's value, or the typed
    * member at a position read with its range marked (`CodeFold.RangeParallel`).
    * The typed member is the member as written, `F (A ∥ D)`,
    * `C (F (A ∥ D))` or `F (A ∥ D) ∥ R` (`DispatchPattern.typedApplications`).
    */
  def choiceReading(left: Code, right: Code, identity: Code => Boolean): ChoiceReading =
    DispatchPattern.specializations(left, right, DispatchPattern.codeLayers, identity).headOption match
      case Some(specialization) =>
        val typed = if specialization.untypedFirst then 1 else 0
        specialization.range match
          case SpecializationRange.Filtered(_) => ChoiceReading.Ranged(typed)
          case _                               => ChoiceReading.Member(typed)
      case None =>
        DispatchPattern.fallbacks(left, right, DispatchPattern.codeLayers).headOption match
          case Some(fallback) => ChoiceReading.Member(if fallback.valueFirst then 0 else 1)
          case None           => ChoiceReading.Plain

  /** The fillings, by position, in the contract slots of the code's choices
    * outside its inner thunks: the slots whose filling's flag λf. f the
    * dispatch patterns read (`DispatchPattern.typedApplications`), a
    * member's function applied to an application.
    */
  def contractFillings(code: Code, holes: Vector[Hole], fillingCount: Int): Set[Int] =
    val fillingOfSlot = Defunctionalization.slotValues(holes, holes.map(_ => -1), Vector.range(0, fillingCount))
    def contracts(part: Code): Set[Int] = part.layer match
      case Slot(_)                   => Set.empty
      case Apply(function, argument) => contracts(function) ++ contracts(argument)
      case Parallel(left, right)     => contracts(left) ++ contracts(right)
      case Choice(left, right) =>
        val tested = Vector(left, right).flatMap(member =>
          member.layer match
            case Apply(Code.Slot(slot), argument) =>
              argument.layer match
                case Apply(_, _) => fillingOfSlot.lift(slot).filter(_ >= 0)
                case _           => None
            case _ => None
        )
        tested.toSet ++ contracts(left) ++ contracts(right)
      case Thunk(_, _, fillings) => fillings.flatMap(contracts).toSet
    contracts(code)

  /** The state a module's code folding gives the thunk over the fillings'
    * terms (`CodeFold.Closing`), its code folded part by part, the code one
    * that `foldsByParts` folds: the state the module's `folded` gives
    * `OrderTerm.Thunk(code, holes, fillings)` by `CodeFolding`'s contract
    * (`CostMonotonicityLaws.foldedByParts`).
    */
  def closedByParts[C <: NativeSpecializer & Singleton](folding: CodeFolding[C], reading: TermReading[C], code: Code, holes: Vector[Hole], fillings: Vector[OrderTerm[C]]): FoldState =
    val items = Defunctionalization.slotValues(
      holes,
      holes.indices.toVector.map(position => Fixed.HoleOf(0, position, holes.size)),
      fillings.indices.toVector.map(Fixed.Outer(_))
    )
    val repeated = repeatedFillings(code, holes, fillings.size).toVector.sorted
    def folded(code: Code, items: Vector[Fixed], depth: Int): FoldState = code.layer match
      case Slot(slot) =>
        items.lift(slot) match
          case Some(Fixed.Outer(position)) =>
            folding.folded(CodeFold.Filling(fillings(position), repeated.contains(position)), reading)
          case Some(Fixed.HoleOf(holeDepth, position, count)) => folding.folded(CodeFold.HoleSlot(holeDepth, position, count), reading)
          case Some(Fixed.Inner(state))                     => folding.folded(CodeFold.InnerFilling(state), reading)
          case None                                         => throw IllegalArgumentException(s"the slot $slot of $code holds nothing")
      case Apply(function, argument) =>
        folding.folded(CodeFold.Apply(folded(function, items, depth), folded(argument, items, depth)), reading)
      case Parallel(left, right) =>
        folding.folded(CodeFold.Parallel(folded(left, items, depth), folded(right, items, depth)), reading)
      case Choice(left, right) =>
        if depth != 0 then throw IllegalArgumentException(s"a choice inside an inner thunk, which is not folded by parts: $code")
        val Code.ChoiceMembers(members) = code
        val memberStates = members.map(folded(_, items, depth))
        val identity = (slotCode: Code) =>
          slotCode.layer match
            case Slot(slot) =>
              items.lift(slot) match
                case Some(Fixed.Outer(position)) => TermReading.identityContract(fillings(position))
                case _                           => false
            case _ => false
        val dispatched = choiceReading(left, right, identity) match
          case ChoiceReading.Plain            => None
          case ChoiceReading.Member(position) => Some(memberStates(position))
          case ChoiceReading.Ranged(position) =>
            members(position).layer match
              case Parallel(application, range) =>
                Some(folding.folded(CodeFold.RangeParallel(folded(application, items, depth), folded(range, items, depth)), reading))
              case other => throw IllegalStateException(s"a typed member read with its range is no parallel: $other")
        folding.folded(CodeFold.Choice(memberStates, dispatched), reading)
      case Thunk(inner, innerHoles, innerFillings) =>
        val states = innerFillings.map(folded(_, items, depth))
        val innerItems = Defunctionalization.slotValues(
          innerHoles,
          innerHoles.indices.toVector.map(position => Fixed.HoleOf(depth + 1, position, innerHoles.size)),
          states.map(Fixed.Inner(_))
        )
        val unread = unreadFillings(inner, innerHoles, innerFillings.size)
        folding.folded(
          CodeFold.InnerThunk(depth, inner, innerHoles, innerFillings, folded(inner, innerItems, depth + 1), unread.map(states)),
          reading
        )
    val unread = unreadFillings(code, holes, fillings.size)
    folding.folded(CodeFold.Closing(code, holes, folded(code, items, 0), unread.map(fillings), repeated.map(fillings)), reading)

  /** What a slot holds where every filling is given. */
  private enum Fixed:
    case Outer(position: Int)
    case HoleOf(depth: Int, position: Int, count: Int)
    case Inner(state: FoldState)

  /** What a slot of a code being folded holds: a filling of the thunk, a
    * hole, or an inner thunk's filling, with its parts and, when its code is
    * a slot that holds a filling of the thunk, that filling's position.
    */
  private enum Item[C <: NativeSpecializer & Singleton]:
    case Outer[C <: NativeSpecializer & Singleton](position: Int) extends Item[C]
    case HoleOf[C <: NativeSpecializer & Singleton](depth: Int, position: Int, count: Int) extends Item[C]
    case Inner(parts: Vector[Part[C]], outer: Option[Int], counts: Map[Int, Int])

    /** While the code is laid out (`Plan`): an inner thunk's filling whose
      * parts depend on a jointly read filling, known only in each
      * combination.
      */
    case Joint[C <: NativeSpecializer & Singleton](outer: Option[Int], reads: Vector[Int]) extends Item[C]

  /** The code laid out once per call for the combinations of the jointly
    * read fillings' entries: a part that reads no jointly read filling is
    * the same in every combination (a part depends on the entries given
    * only through the fillings it reads, and the unread fillings' entries
    * are the same in all), so its parts are computed once (`Shared`), and
    * only the parts that read one are read again in each combination. The
    * plan mirrors the code, a part's place in it being its place in the
    * code: one `Code` can stand at two places whose slots hold different
    * items (under two inner thunks), so a table keyed by `Code` could not
    * hold it.
    */
  private enum Plan[C <: NativeSpecializer & Singleton]:
    case Shared(parts: Vector[Part[C]])
    case Read[C <: NativeSpecializer & Singleton](code: Code, slot: Int, identifier: Int, reads: Vector[Int]) extends Plan[C]
    case Applied(function: Plan[C], argument: Plan[C], identifier: Int, reads: Vector[Int])
    case Filtered(left: Plan[C], criterion: Code, identifier: Int, reads: Vector[Int])

    /** A choice the dispatch reads as `choiceReading` says: its members'
      * plans, in the order `Code.ChoiceMembers` lists them, and for a typed
      * member read with its range, the plan of its typed application and its
      * range's code in place of the member's own plan, so that the member as
      * written and its marked reading are made from the same parts.
      */
    case Chosen(
        choiceReading: ChoiceReading,
        members: Vector[Plan[C]],
        ranged: Option[(Plan[C], Code)],
        identifier: Int,
        reads: Vector[Int]
    )
    case InnerRead(
        inner: Code,
        holes: Vector[Hole],
        fillings: Vector[Code],
        fillingPlans: Vector[Plan[C]],
        body: Plan[C],
        depth: Int,
        outers: Vector[Option[Int]],
        identifier: Int,
        reads: Vector[Int]
    )

  /** The jointly read fillings a part of the plan reads, directly or through
    * an inner thunk's filling, by increasing position: its parts depend on
    * their entries alone, every other filling's entry being the same in all
    * combinations.
    */
  private def readsOf[C <: NativeSpecializer & Singleton](plan: Plan[C]): Vector[Int] = plan match
    case Plan.Shared(_)                                => Vector.empty
    case Plan.Read(_, _, _, reads)                     => reads
    case Plan.Applied(_, _, _, reads)                  => reads
    case Plan.Filtered(_, _, _, reads)                 => reads
    case Plan.Chosen(_, _, _, _, reads)                => reads
    case Plan.InnerRead(_, _, _, _, _, _, _, _, reads) => reads

  /** The parts of the plan's dependent parts already read, by the part's
    * identifier and the indices of the entries chosen for the jointly read
    * fillings it reads, in the order of their positions: a part read again
    * under a combination that chooses the same entries for those fillings
    * has the same parts.
    */
  private type ReadParts[C <: NativeSpecializer & Singleton] = Map[(Int, Vector[Int]), Vector[Part[C]]]

  /** The positions of both, by increasing position, each once. */
  private def readsJoined(left: Vector[Int], right: Vector[Int]): Vector[Int] =
    if right.isEmpty then left else if left.isEmpty then right else (left ++ right).distinct.sorted

  /** A part of the code: its code state at each module, the entries chosen
    * for the fillings of the thunk it reads, by position, and the size of
    * those entries, summed as the part is made (a part around two parts
    * chooses for the fillings each chose for, no filling in both, since a
    * filling read more than once is listed jointly).
    */
  private final case class Part[C <: NativeSpecializer & Singleton](states: Vector[FoldState], chosen: Map[Int, Entry[C, ModuleCost]], size: BigInt)

  /** The thunk's candidates over its fillings' entries (the code folded by
    * parts, `foldsByParts`).
    *
    * FIXME (2026-11-16): at the joint products the whole fold handles well https://github.com/Atry/private-overlay/issues/1951
    * (2 to 64 on the hot points of a published points file), this program costs more than the
    * whole fold. Inside `ThunkCandidates`, on those 18 hot points,
    * 2026-11-16:
    * allocation, table 7 (the entries solo and wren, `contest-entries-solo`
    * and `contest-entries-wren`), 1.57 times the whole fold's at
    * products above 1, 1.04 times at product 1 (where the thunk is read
    * whole), 1.46 times overall; time, table 7's wren rows, 1.72, 1.04 and
    * 1.50 times, and table 8's solo rows (table 7's solo times were read
    * under a load of 439 to 721), 1.34, 1.15 and 1.30 times. On the wren entry's
    * nested_calls_1000000_hot it allocates 3.21 GB per round against 2.56 GB.
    * The parts that read no jointly read filling are computed once per call
    * (`Plan`), not once per combination. On those hot points the jointly
    * read fillings reach nearly every subtree and this saves little (table
    * 10 of code-fold-reuse); where a graph respells its thunks,
    * about 90% of a
    * 118-filling thunk's code nodes read none of its seven jointly read
    * fillings, at a product of 128 (solo nested_calls_10000_hot/direct,
    * measured 2026-11-17).
    * Interning the parts' readings was
    * measured not to be the lever (their equality and hashing were about 6%
    * of the program's samples, 2026-11-17). The crossover, the whole fold at
    * products up to k and this program above, is chosen by configuration
    * (`JointReading.wholeFoldBound`, 1 as measured), under the law that both
    * give each reading's least cost on either side
    * (`CostMonotonicityLaws.wholeFoldBoundKeepsLeastCosts`); what remains is
    * a k above 1 measured from the per-reading costs (this program already
    * wins at 256).
    */
  def candidates[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      foldings: Vector[CodeFolding[C]],
      shape: Shape[C],
      code: Code,
      holes: Vector[Hole],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      costFirst: Boolean
  ): Vector[Entry[C, ModuleCost]] =
    // The flag λf. f of a filling in a contract slot of the code's choices
    // decides what the dispatch reads its choice as, and, where the thunk is
    // read as a contract, the filling's own contract domains are the end of
    // the thunk's (`ModuleCostModel`'s contract domains,
    // `DispatchPattern.contractChecks`). Both are part of an entry's reading
    // (`ModuleCostModel.sameReading`), so the candidates are listed once for
    // each value of both of every such filling, its entries restricted to
    // the value: the entries of one value hold each reading's least of that
    // value, and the candidates of every value are the candidates of all,
    // while the parts, pruned by the modules' readings of the code, never
    // trade one value for another. The listings are the products of the
    // values the contract fillings' entries take, at most their numbers of
    // readings, and a code holds one contract filling per choice at most.
    // The jointly read fillings settled above the bound are settled on the
    // numbers of entries given, before the listing by contract values, so
    // that what is settled is a function of those numbers alone
    // (`settledPositions`, `ThunkCandidates.settledFillings`).
    val settledAbove = settledPositions(jointPositions(code, holes, options.size), options.map(_.size), model.jointReading.enumerationBound)
    val settledOptions = options.indices.toVector.map(position =>
      if settledAbove.contains(position) then Vector(first(options(position))) else options(position)
    )
    val contracts = contractFillings(code, holes, options.size).toVector.sorted
    val values = contracts.map(position => settledOptions(position).map(entry => (entry.cost.identityContract, entry.cost.contractDomains)).distinct)
    CostModel.combinations(values).flatMap { chosen =>
      val fixedValues = contracts.zip(chosen).toMap
      val restricted = settledOptions.indices.toVector.map(position =>
        fixedValues.get(position).fold(settledOptions(position))(value =>
          settledOptions(position).filter(entry => (entry.cost.identityContract, entry.cost.contractDomains) == value)
        )
      )
      val flags = fixedValues.view.mapValues(_._1).toMap
      flaggedCandidates(model, foldings, shape, code, holes, restricted, flags, costFirst)
    }

  /** `candidates` where the fillings of the contract slots have the flags
    * given, their entries restricted to them.
    */
  private def flaggedCandidates[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      foldings: Vector[CodeFolding[C]],
      shape: Shape[C],
      code: Code,
      holes: Vector[Hole],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      flags: Map[Int, Boolean],
      costFirst: Boolean
  ): Vector[Entry[C, ModuleCost]] =
    val outerItems = outerItemsOf[C](holes, options.size)
    val counts = occurrences(code, outerItems)
    val headed = (holes.size, code.layer) match
      case (2, Apply(Code.Slot(function), _)) =>
        outerItems.lift(function).collect { case Item.Outer(position) => position }.toSet
      case _ => Set.empty[Int]
    val repeated = readMoreThanOnce(counts)
    val (joint, settled) = enumeratedOrSettled((repeated ++ headed).toVector.sorted, options, model.jointReading.enumerationBound)
    val unread = options.indices.filterNot(counts.contains).map(position => position -> first(options(position))).toMap ++ settled
    val (plan, _) = Reader(model, foldings, options, unread, repeated, flags, costFirst).planned(joint.toSet, code, outerItems, 0, 0)
    CostModel
      .lazyCombinations(joint.map(position => options(position).indices.toVector))
      .takeWhile(_ => !model.stop.stopRequested)
      .foldLeft((Vector.empty[Entry[C, ModuleCost]], Map.empty: ReadParts[C])) { case ((found, readParts), indices) =>
        val chosen = joint.zip(indices).toMap
        val fixed = chosen.map((position, index) => position -> options(position)(index)) ++ unread
        val reader = Reader(model, foldings, options, fixed, repeated, flags, costFirst)
        val (parts, afterReading) = reader.evaluated(plan, outerItems, chosen, readParts)
        val made = parts.map { part =>
          val entries = options.indices.toVector.map(position => fixed.getOrElse(position, part.chosen(position)))
          Entry(model.cost(shape, entries.map(_.cost)), shape, entries)
        }
        (found ++ made, afterReading)
      }
      ._1

  /** The fillings, by position, the dynamic program lists jointly: those the
    * code reads more than once, counted through inner thunks
    * (`repeatedFillings`), and, of a thunk of two holes whose code applies a
    * filling, that filling (the headed one).
    */
  def jointPositions(code: Code, holes: Vector[Hole], fillingCount: Int): Vector[Int] =
    val outerItems = outerItemsOf(holes, fillingCount)
    val headed = (holes.size, code.layer) match
      case (2, Apply(Code.Slot(function), _)) =>
        outerItems.lift(function).collect { case Item.Outer(position) => position }.toSet
      case _ => Set.empty[Int]
    (readMoreThanOnce(occurrences(code, outerItems)) ++ headed).toVector.sorted

  /** The fillings, by position, that the code does not read, counted
    * through inner thunks: those `flaggedCandidates` gives their first entry
    * at every number of entries.
    */
  def unreadPositions(code: Code, holes: Vector[Hole], fillingCount: Int): Set[Int] =
    val outerItems = outerItemsOf(holes, fillingCount)
    val counts = occurrences(code, outerItems)
    (0 until fillingCount).filterNot(counts.contains).toSet

  /** The fillings, by position, that a thunk of the code and holes reads
    * more than once, counted through inner thunks: those the dynamic program
    * lists jointly besides the headed one, and those `CodeFold.Closing`
    * counts once.
    */
  def repeatedFillings(code: Code, holes: Vector[Hole], fillingCount: Int): Set[Int] =
    readMoreThanOnce(
      occurrences(
        code,
        outerItemsOf(holes, fillingCount)
      )
    )

  /** The items of an outermost code's slots: its holes', then its
    * fillings', by position.
    */
  private def outerItemsOf[C <: NativeSpecializer & Singleton](holes: Vector[Hole], fillingCount: Int): Vector[Item[C]] =
    Defunctionalization.slotValues(
      holes,
      holes.indices.toVector.map(position => Item.HoleOf[C](0, position, holes.size)),
      Vector.tabulate(fillingCount)(Item.Outer[C](_))
    )

  private def readMoreThanOnce(counts: Map[Int, Int]): Set[Int] = counts.collect { case (position, count) if count > 1 => position }.toSet

  /** How many times the code reads each filling of the thunk, an inner
    * thunk's filling counted once for each time its code reads it and its
    * unread fillings once.
    */
  private def occurrences[C <: NativeSpecializer & Singleton](code: Code, items: Vector[Item[C]]): Map[Int, Int] = counted(code, items, Map.empty)

  /** `total` with the code's occurrences added, slot by slot, so that no
    * part's counts are merged into its parent's.
    */
  private def counted[C <: NativeSpecializer & Singleton](code: Code, items: Vector[Item[C]], total: Map[Int, Int]): Map[Int, Int] = code.layer match
    case Slot(slot) =>
      items.lift(slot) match
        case Some(Item.Outer(position))         => added(total, Map(position -> 1))
        case Some(Item.Inner(_, _, counts))    => added(total, counts)
        case _                                  => total
    case Apply(function, argument) => counted(argument, items, counted(function, items, total))
    case Parallel(left, right)     => counted(right, items, counted(left, items, total))
    case Choice(left, right)       => counted(right, items, counted(left, items, total))
    case Thunk(inner, innerHoles, fillings) =>
      val fillingCounts = fillings.map(occurrences(_, items))
      val innerItems = Defunctionalization.slotValues(
        innerHoles,
        innerHoles.indices.toVector.map(position => Item.HoleOf[C](1, position, innerHoles.size)),
        fillingCounts.map(counts => Item.Inner(Vector.empty, None, counts))
      )
      unreadFillings(inner, innerHoles, fillings.size).foldLeft(counted(inner, innerItems, total))((sum, index) =>
        added(sum, fillingCounts(index))
      )

  private def added(total: Map[Int, Int], counts: Map[Int, Int]): Map[Int, Int] =
    counts.foldLeft(total) { case (sum, (position, count)) => sum.updated(position, sum.getOrElse(position, 0) + count) }

  /** The fillings, by index, of a thunk of the code and holes that the code
    * does not read, the slots the code reads taken from the facts the IR
    * holds once per code (`Code.facts`).
    */
  private def unreadFillings(code: Code, holes: Vector[Hole], fillingCount: Int): Vector[Int] =
    val read = Code.facts(code).slotsRead
    val fillingSlots = Defunctionalization.slotValues(holes, holes.map(_ => -1), (0 until fillingCount).toVector)
    val readFillings = fillingSlots.indices.collect { case slot if read.contains(slot) && fillingSlots(slot) >= 0 => fillingSlots(slot) }.toSet
    (0 until fillingCount).toVector.filterNot(readFillings.contains)

  private final case class Reader[C <: NativeSpecializer & Singleton](
      model: ModuleCostModel[C],
      foldings: Vector[CodeFolding[C]],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      fixed: Map[Int, Entry[C, ModuleCost]],
      repeated: Set[Int],
      flags: Map[Int, Boolean],
      costFirst: Boolean
  ):

    /** The code laid out (`Plan`), its slots holding the items given,
      * `depth` thunks in: of each part that reads no filling of `joint`, its
      * parts, read with this reader, whose entries given are the unread
      * fillings' alone; each part that reads one, left to be read in each
      * combination (`evaluated`).
      */
    def planned(joint: Set[Int], code: Code, items: Vector[Item[C]], depth: Int, next: Int): (Plan[C], Int) = code.layer match
      case Slot(slot) =>
        items.lift(slot) match
          case Some(Item.Outer(position)) if joint.contains(position) => (Plan.Read[C](code, slot, next, Vector(position)), next + 1)
          case Some(Item.Joint(_, reads))                             => (Plan.Read[C](code, slot, next, reads), next + 1)
          case _                                                      => (Plan.Shared(slotParts(code, slot, items)), next)
      case Apply(function, argument) =>
        val (functionPlan, afterFunction) = planned(joint, function, items, depth, next)
        val (argumentPlan, afterArgument) = planned(joint, argument, items, depth, afterFunction)
        (functionPlan, argumentPlan) match
          case (Plan.Shared(functions), Plan.Shared(arguments)) => (Plan.Shared(applied(functions, arguments)), afterArgument)
          case _ =>
            (Plan.Applied(functionPlan, argumentPlan, afterArgument, readsJoined(readsOf(functionPlan), readsOf(argumentPlan))), afterArgument + 1)
      case Parallel(left, right) =>
        val criterionReads = criterionPosition(right, items).filter(joint.contains).toVector
        planned(joint, left, items, depth, next) match
          case (Plan.Shared(lefts), afterLeft) if criterionReads.isEmpty =>
            (Plan.Shared(filtered(lefts, criteria(right, items))), afterLeft)
          case (leftPlan, afterLeft) =>
            (Plan.Filtered(leftPlan, right, afterLeft, readsJoined(readsOf(leftPlan), criterionReads)), afterLeft + 1)
      case Choice(left, right) =>
        if depth != 0 then throw IllegalArgumentException(s"a choice inside an inner thunk, which is not folded by parts: $code")
        val Code.ChoiceMembers(members) = code
        val choice = choiceReading(left, right, slotIdentity(items))
        val rangedAt = choice match
          case ChoiceReading.Ranged(position) => Some(position)
          case _                              => None
        // The ranged member's own plan stands in as nothing: its parts are
        // made from its application's and its range's (`chosen`).
        val (memberPlans, afterMembers) = members.zipWithIndex.foldLeft((Vector.empty[Plan[C]], next)) { case ((made, current), (member, position)) =>
          if rangedAt.contains(position) then (made :+ Plan.Shared(Vector.empty), current)
          else
            val (memberPlan, following) = planned(joint, member, items, depth, current)
            (made :+ memberPlan, following)
        }
        val (ranged, afterRanged) = rangedAt match
          case None => (None, afterMembers)
          case Some(position) =>
            members(position).layer match
              case Parallel(application, range) =>
                val (applicationPlan, following) = planned(joint, application, items, depth, afterMembers)
                (Some((applicationPlan, range)), following)
              case other => throw IllegalStateException(s"a typed member read with its range is no parallel: $other")
        val rangeReads = ranged.toVector.flatMap((_, range) => criterionPosition(range, items).filter(joint.contains))
        val reads = (memberPlans ++ ranged.map(_._1)).foldLeft(rangeReads)((joined, part) => readsJoined(joined, readsOf(part)))
        if reads.isEmpty then
          val rangedParts = ranged.map((applicationPlan, range) => (sharedParts(applicationPlan), criteria(range, items)))
          (Plan.Shared(chosen(choice, memberPlans.map(sharedParts), rangedParts)), afterRanged)
        else (Plan.Chosen(choice, memberPlans, ranged, afterRanged, reads), afterRanged + 1)
      case Thunk(inner, innerHoles, fillings) =>
        val (fillingPlans, afterFillings) = fillings.foldLeft((Vector.empty[Plan[C]], next)) { case ((made, current), filling) =>
          val (fillingPlan, following) = planned(joint, filling, items, depth, current)
          (made :+ fillingPlan, following)
        }
        val outers = fillings.map(outerOf(_, items))
        val innerItems = Defunctionalization.slotValues(
          innerHoles,
          innerHoles.indices.toVector.map(position => Item.HoleOf[C](depth + 1, position, innerHoles.size)),
          fillingPlans.zip(outers).map {
            case (Plan.Shared(fillingParts), outer) => Item.Inner(fillingParts, outer, Map.empty)
            case (fillingPlan, outer)               => Item.Joint[C](outer, readsOf(fillingPlan))
          }
        )
        val (bodyPlan, afterBody) = planned(joint, inner, innerItems, depth + 1, afterFillings)
        (fillingPlans.forall(isShared), bodyPlan) match
          case (true, Plan.Shared(bodies)) =>
            (Plan.Shared(innerThunk(depth, inner, innerHoles, fillings, fillingPlans.map(sharedParts), bodies)), afterBody)
          case _ =>
            val reads = fillingPlans.foldLeft(readsOf(bodyPlan))((joined, fillingPlan) => readsJoined(joined, readsOf(fillingPlan)))
            (Plan.InnerRead(inner, innerHoles, fillings, fillingPlans, bodyPlan, depth, outers, afterBody, reads), afterBody + 1)

    /** The code's least part of each reading under this reader's entries
      * given, read from its plan: a shared part as it was laid out, every
      * other part again.
      */
    def evaluated(plan: Plan[C], items: Vector[Item[C]], chosen: Map[Int, Int], readParts: ReadParts[C]): (Vector[Part[C]], ReadParts[C]) =
      plan match
        case Plan.Shared(parts) => (parts, readParts)
        case dependent =>
          val key = (identifierOf(dependent), readsOf(dependent).map(chosen))
          readParts.get(key) match
            case Some(parts) => (parts, readParts)
            case None =>
              val (parts, afterReading) = computed(dependent, items, chosen, readParts)
              (parts, afterReading.updated(key, parts))

    /** The parts of a part read again in a combination, its own parts read
      * through `evaluated`.
      */
    private def computed(plan: Plan[C], items: Vector[Item[C]], chosen: Map[Int, Int], readParts: ReadParts[C]): (Vector[Part[C]], ReadParts[C]) =
      plan match
        case Plan.Shared(parts)        => (parts, readParts)
        case Plan.Read(code, slot, _, _) => (slotParts(code, slot, items), readParts)
        case Plan.Applied(function, argument, _, _) =>
          val (functions, afterFunction) = evaluated(function, items, chosen, readParts)
          val (arguments, afterArgument) = evaluated(argument, items, chosen, afterFunction)
          (applied(functions, arguments), afterArgument)
        case Plan.Filtered(left, criterion, _, _) =>
          val (lefts, afterLeft) = evaluated(left, items, chosen, readParts)
          (filtered(lefts, criteria(criterion, items)), afterLeft)
        case Plan.Chosen(choice, members, ranged, _, _) =>
          val (memberParts, afterMembers) = members.foldLeft((Vector.empty[Vector[Part[C]]], readParts)) { case ((made, current), memberPlan) =>
            val (parts, following) = evaluated(memberPlan, items, chosen, current)
            (made :+ parts, following)
          }
          ranged match
            case None => (this.chosen(choice, memberParts, None), afterMembers)
            case Some((applicationPlan, range)) =>
              val (applications, afterApplication) = evaluated(applicationPlan, items, chosen, afterMembers)
              (this.chosen(choice, memberParts, Some((applications, criteria(range, items)))), afterApplication)
        case Plan.InnerRead(inner, innerHoles, fillings, fillingPlans, body, depth, outers, _, _) =>
          val (fillingParts, afterFillings) = fillingPlans.foldLeft((Vector.empty[Vector[Part[C]]], readParts)) {
            case ((made, current), fillingPlan) =>
              val (parts, following) = evaluated(fillingPlan, items, chosen, current)
              (made :+ parts, following)
          }
          val innerItems = Defunctionalization.slotValues(
            innerHoles,
            innerHoles.indices.toVector.map(position => Item.HoleOf[C](depth + 1, position, innerHoles.size)),
            fillingParts.zip(outers).map((parts, outer) => Item.Inner(parts, outer, Map.empty))
          )
          val (bodies, afterBody) = evaluated(body, innerItems, chosen, afterFillings)
          (innerThunk(depth, inner, innerHoles, fillings, fillingParts, bodies), afterBody)

    private def identifierOf(plan: Plan[C]): Int = plan match
      case Plan.Shared(_) => throw IllegalStateException("a shared part has no identifier: it is read once")
      case Plan.Read(_, _, identifier, _)                     => identifier
      case Plan.Applied(_, _, identifier, _)                  => identifier
      case Plan.Filtered(_, _, identifier, _)                 => identifier
      case Plan.Chosen(_, _, _, identifier, _)                => identifier
      case Plan.InnerRead(_, _, _, _, _, _, _, identifier, _) => identifier

    private def isShared(plan: Plan[C]): Boolean = plan match
      case Plan.Shared(_) => true
      case _              => false

    private def sharedParts(plan: Plan[C]): Vector[Part[C]] = plan match
      case Plan.Shared(parts) => parts
      case other              => throw IllegalStateException(s"a part read in each combination where a shared one was expected: $other")

    /** The filling of the thunk an inner thunk's filling is, where it is a
      * slot that holds one.
      */
    private def outerOf(filling: Code, items: Vector[Item[C]]): Option[Int] = filling.layer match
      case Slot(slot) =>
        items.lift(slot).flatMap {
          case Item.Outer(position)              => Some(position)
          case Item.Inner(_, outer, _)           => outer
          case Item.Joint(outer, _)              => outer
          case Item.HoleOf(_, _, _)              => None
        }
      case _ => None

    /** The filling of the thunk a criterion holds. */
    private def criterionPosition(criterion: Code, items: Vector[Item[C]]): Option[Int] = criterion.layer match
      case Slot(slot) =>
        items.lift(slot) match
          case Some(Item.Outer(position))              => Some(position)
          case Some(Item.Inner(_, Some(position), _)) => Some(position)
          case Some(Item.Joint(Some(position), _))     => Some(position)
          case other => throw IllegalArgumentException(s"a criterion that holds no filling of the thunk: $other")
      case _ => throw IllegalArgumentException(s"a criterion that is no slot: $criterion")

    private def slotParts(code: Code, slot: Int, items: Vector[Item[C]]): Vector[Part[C]] =
      items.lift(slot) match
        case Some(Item.Outer(position)) =>
          fixed.get(position) match
            case Some(entry) => Vector(Part(filled(position, entry, priced = true), Map.empty, 0))
            case None =>
              pruned(options(position).map(entry => Part(filled(position, entry, priced = true), Map(position -> entry), entry.size)))
        case Some(Item.HoleOf(holeDepth, position, count)) =>
          Vector(Part(foldings.map(_.folded(CodeFold.HoleSlot(holeDepth, position, count), model.reading)), Map.empty, 0))
        case Some(Item.Inner(fillingParts, _, _)) =>
          fillingParts.map(filling =>
            Part(
              foldings.indices.toVector.map(module => foldings(module).folded(CodeFold.InnerFilling(filling.states(module)), model.reading)),
              filling.chosen,
              filling.size
            )
          )
        case Some(Item.Joint(_, _)) => throw IllegalStateException(s"the slot $slot of $code is read before its inner filling's parts are known")
        case None                => throw IllegalArgumentException(s"the slot $slot of $code holds nothing")

    /** Whether the slot's filling is λf. f, as the dispatch reads it: a
      * filling of the thunk by its flag, which the listing fixed
      * (`candidates`), anything else not.
      */
    private def slotIdentity(items: Vector[Item[C]])(slotCode: Code): Boolean = slotCode.layer match
      case Slot(slot) =>
        items.lift(slot) match
          case Some(Item.Outer(position)) => flags.getOrElse(position, false)
          case _                          => false
      case _ => false

    /** The parts of a choice from its members' parts: every combination of
      * one part of each member, the member the dispatch reads (`choice`)
      * giving its reading too, the typed member read with its range made
      * from each pair of its application's and its range's parts, both as
      * written and marked. The least of each reading of the combinations is
      * kept; the members are not pruned first, since a part's dispatched
      * reading is no function of its reading as written.
      */
    private def chosen(choice: ChoiceReading, memberParts: Vector[Vector[Part[C]]], ranged: Option[(Vector[Part[C]], Vector[Part[C]])]): Vector[Part[C]] =
      val alternatives = memberParts.indices.toVector.map(position =>
        (choice, ranged) match
          case (ChoiceReading.Ranged(at), Some((applications, ranges))) if at == position =>
            for
              application <- applications
              range <- ranges
            yield (
              combined(application, range, CodeFold.Parallel(_, _)),
              Some(combined(application, range, CodeFold.RangeParallel(_, _)).states)
            )
          case (ChoiceReading.Member(at), _) if at == position => memberParts(position).map(part => (part, Some(part.states)))
          case _                                                => memberParts(position).map(part => (part, None))
      )
      pruned(CostModel.combinations(alternatives).map { combination =>
        val dispatched = combination.collectFirst { case (_, Some(states)) => states }
        Part(
          foldings.indices.toVector.map(module =>
            foldings(module).folded(CodeFold.Choice(combination.map(_._1.states(module)), dispatched.map(_(module))), model.reading)
          ),
          combination.foldLeft(Map.empty[Int, Entry[C, ModuleCost]])(_ ++ _._1.chosen),
          combination.foldLeft(BigInt(0))(_ + _._1.size)
        )
      })

    private def applied(functions: Vector[Part[C]], arguments: Vector[Part[C]]): Vector[Part[C]] =
      pruned(
        for
          functionPart <- functions
          argumentPart <- arguments
        yield combined(functionPart, argumentPart, CodeFold.Apply(_, _))
      )

    private def criteria(criterion: Code, items: Vector[Item[C]]): Vector[Part[C]] =
      criterionParts(
        criterionPosition(criterion, items).getOrElse(throw IllegalArgumentException(s"a criterion that holds no filling of the thunk: $criterion"))
      )

    private def filtered(lefts: Vector[Part[C]], criteria: Vector[Part[C]]): Vector[Part[C]] =
      pruned(
        for
          leftPart <- lefts
          criterion <- criteria
        yield combined(leftPart, criterion, CodeFold.Parallel(_, _))
      )

    private def innerThunk(
        depth: Int,
        inner: Code,
        innerHoles: Vector[Hole],
        fillings: Vector[Code],
        fillingParts: Vector[Vector[Part[C]]],
        bodies: Vector[Part[C]]
    ): Vector[Part[C]] =
      val unread = unreadFillings(inner, innerHoles, fillings.size)
      pruned(
        for
          body <- bodies
          unreadParts <- CostModel.combinations(unread.map(fillingParts))
        yield Part(
          foldings.indices.toVector.map(module =>
            foldings(module).folded(
              CodeFold.InnerThunk(depth, inner, innerHoles, fillings, body.states(module), unreadParts.map(_.states(module))),
              model.reading
            )
          ),
          unreadParts.foldLeft(body.chosen)(_ ++ _.chosen),
          unreadParts.foldLeft(body.size)(_ + _.size)
        )
      )

    /** The parts of a filling read as a criterion: its first entry of each
      * reading by size and content, read by its reading
      * (`OrderTerm.Unpriced`), or its entry where it is listed jointly.
      */
    private def criterionParts(position: Int): Vector[Part[C]] =
      fixed.get(position) match
        case Some(entry) => Vector(Part(filled(position, entry, priced = false), Map.empty, 0))
        case None =>
          firstOfEachReading(options(position)).map(entry => Part(filled(position, entry, priced = false), Map(position -> entry), entry.size))

    /** A filling of the thunk at each module, by its state where priced and
      * by its reading where not.
      */
    private def filled(position: Int, entry: Entry[C, ModuleCost], priced: Boolean): Vector[FoldState] =
      foldings.indices.toVector.map(module =>
        val state = entry.cost.states(module)
        val term =
          if priced then OrderTerm.Folded[C](state, entry.cost.identityContract)
          else OrderTerm.Unpriced[C](model.modules(module).reading(state))
        foldings(module).folded(CodeFold.Filling(term, repeated(position)), model.reading)
      )

    private def combined(left: Part[C], right: Part[C], layer: (FoldState, FoldState) => CodeFold[C]): Part[C] =
      Part(
        foldings.indices.toVector.map(module => foldings(module).folded(layer(left.states(module), right.states(module)), model.reading)),
        left.chosen ++ right.chosen,
        left.size + right.size
      )

    private def firstOfEachReading(entries: Vector[Entry[C, ModuleCost]]): Vector[Entry[C, ModuleCost]] =
      entries
        .foldLeft(Vector.empty[Vector[Entry[C, ModuleCost]]]) { (groups, entry) =>
          groups.indexWhere(group => group.headOption.exists(member => model.sameReading(member.cost, entry.cost))) match
            case -1       => groups :+ Vector(entry)
            case position => groups.updated(position, groups(position) :+ entry)
        }
        .map(first)

    /** The least part of each reading, in the order the readings first
      * occur.
      */
    private def pruned(found: Vector[Part[C]]): Vector[Part[C]] =
      if found.size < 2 then found
      else
        found
          .foldLeft((Vector.empty[Part[C]], Map.empty[Vector[ModuleReading], Int])) { case ((kept, positions), next) =>
            val readings = foldings.indices.toVector.map(module => foldings(module).reading(next.states(module)))
            positions.get(readings) match
              case None => (kept :+ next, positions.updated(readings, kept.size))
              case Some(position) =>
                if better(next, kept(position)) then (kept.updated(position, next), positions) else (kept, positions)
          }
          ._1

    private def ranks(part: Part[C]): Vector[OrderValue] = foldings.indices.toVector.map(module => foldings(module).rank(part.states(module)))

    /** Less rank, module by module (unless by size alone); at one rank, less
      * size, then the first by content at the first filling where the two
      * differ.
      */
    private def better(candidate: Part[C], kept: Part[C]): Boolean =
      val order = if costFirst then OrderValue.ranksOrdering.compare(ranks(candidate), ranks(kept)) else 0
      if order != 0 then order < 0
      else
        val bySize = candidate.size.compare(kept.size)
        if bySize != 0 then bySize < 0
        else
          candidate.chosen.keys.toVector.sorted.view
            .map(position => ContentOrder.compare(candidate.chosen(position), kept.chosen(position)))
            .find(_ != 0)
            .exists(_ < 0)

  /** The jointly read fillings a reading enumerates, and those it settles: a
    * filling of one entry is settled to it, as it has no choice; the others
    * are all enumerated when the product of their entries is at most
    * `bound` (`JointReading.enumerationBound`), otherwise none, each settled to its first entry
    * (`first`, the rule of a filling the code does not read). A settled
    * filling's entry is chosen on its own, not with the others, so above the
    * bound the thunk's least entry is the least over the settled choice, not
    * over every combination. So at most log2 of the bound fillings are
    * enumerated, each of two entries or more: the combinations are drawn by
    * a nest of one `LazyList.flatMap` per enumerated filling
    * (`CostModel.lazyCombinations`), which threw `StackOverflowError` when
    * the thousands of one-entry fillings of `contest-entries-solo`'s
    * repeated_library_hotspots_calls_1000 direct point were enumerated
    * (2026-11-18).
    */
  def enumeratedOrSettled[C <: NativeSpecializer & Singleton](
      joint: Vector[Int],
      options: Vector[Vector[Entry[C, ModuleCost]]],
      bound: Long
  ): (Vector[Int], Map[Int, Entry[C, ModuleCost]]) =
    val settled = settledPositions(joint, options.map(_.size), bound)
    val (chosen, alone) = joint.partition(position => options(position).size > 1 && !settled.contains(position))
    (chosen, alone.map(position => position -> first(options(position))).toMap)

  /** The jointly read fillings, by position, settled to their first entry
    * at the numbers of entries given: every one of more than one entry when
    * the product of their numbers exceeds `bound`
    * (`JointReading.enumerationBound`), none otherwise. A function of the
    * numbers alone, which `CountedExtraction`'s passes give alike
    * (`gezi.extraction.CostModel.settledChildren`).
    */
  def settledPositions(joint: Vector[Int], entryCounts: Vector[Int], bound: Long): Set[Int] =
    val chosen = joint.filter(entryCounts(_) > 1)
    if productWithinBound(chosen.map(entryCounts(_)), 0, 1, bound) then Set.empty else chosen.toSet

  /** Whether the product of the sizes from `place` on, times `product`, is
    * at most `bound`, read until it exceeds the bound, so that a
    * thunk of many jointly read fillings is not multiplied out.
    */
  @scala.annotation.tailrec
  private def productWithinBound(sizes: Vector[Int], place: Int, product: Long, bound: Long): Boolean =
    if product > bound then false
    else if place == sizes.size then true
    else productWithinBound(sizes, place + 1, product * sizes(place), bound)

  /** The first entry by size, then content: the entry a settled or unread
    * filling is given (`ThunkCandidates` reads it too).
    */
  private[strategies] def first[C <: NativeSpecializer & Singleton](entries: Vector[Entry[C, ModuleCost]]): Entry[C, ModuleCost] =
    entries.reduce((kept, next) =>
      val bySize = next.size.compare(kept.size)
      if bySize < 0 || (bySize == 0 && ContentOrder.compare(next, kept) < 0) then next else kept
    )
