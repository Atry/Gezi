package com.yang_bo.gezi.extraction

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.saturation.StopSignal
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The extraction's fixed point, reached without reading a production's
  * children while one of them has no entry.
  *
  * THE DEFINITION (2026-11-13). The kept entry of each class and reading is the
  * least finite derivation tree of that class and reading, by `model.ordering`
  * then `ContentOrder`, each child any finite tree of its class of the reading
  * the parent needs (a child that is the class itself any tree of a production
  * that does not read it); and likewise the kept entry of each reading among
  * the productions that do not read the class. A non-empty set of finite trees
  * ordered by cost and then by `ContentOrder`, which compares the size first,
  * has a least element, so the definition gives one entry for each class and
  * reading whatever the order in which they are found. It was first stated over
  * the children's kept entries only, which has no finite solution where a cycle
  * adds no cost: a class whose reading is reached at its least cost only
  * through a parallel's unpriced criterion that reads back to the class
  * (measured 2026-11-13 on a generated graph, CountedExtractionLawTest). Its
  * costs are those of the retired baseline's fixed point (`Extraction.fixed`,
  * read back with
  * `git show c33817721:lambda_jit/extraction/src/main/scala/lambdajit/extraction/Extraction.scala`).
  * The kept entry used to be the best ever produced, replaced only by a
  * strictly better one, so that a parent whose cost did not change when a child
  * improved kept the child's earlier entry inside it, and which one it kept
  * depended on the order of the improvements (measured 2026-11-13 on
  * programfamilies' list at 32: 262 of 3,426 classes held an entry over a child
  * entry strictly worse than that child's final one, at an equal cost of the
  * parent).
  *
  * FIXME (2026-11-16): one entry per class and reading is not THE DEFINITION
  * https://github.com/Atry/private-overlay/issues/1954 where a module that
  * comes first does not read a child that a later one prices: the lexicographic
  * order is then not monotone there (Gurney and Griffin, ICNP 2007, Theorem 4),
  * and the kept child, least under (A, B), can make the parent's tree cost more
  * than its least. The witness is settles-front-joint's law (5) at seed 1: a
  * leaf L, a class of `L + L` reading 1, a class of `L L` and `L ∥ L` united,
  * costing (1, 0) and (0, 1), and the root, the first class applied to the
  * second, at which A does not read the second child; the least tree takes
  * `L L` and costs (1, 0), and this extraction keeps `L ∥ L` and gives the root
  * (1, 1). It is accepted, judged by the vision (`CONTRIBUTING.md`, "The
  * Vision"): by THE DICHOTOMY the second entry is taken only at a child A does
  * not read, so it never changes A's value, here narrow_blocks', the part of a
  * program compiled whole, only B's, the term's size among terms of equal A; on
  * the 18 hot points of a published points file no trade was accepted and
  * outcomes, steps and costs were the same with it, while it cost 1.47 times
  * (`contest-entries-solo`) and 1.23 times (`contest-entries-wren`) this
  * extraction's time. The fix, two entries per reading, least under (A, B) and
  * under (B, A), with the trades of jointly read fillings, is on branch
  * settles-front-joint at 82beefb2b (its table 9). Reopen it when a family
  * shows B changing compiled speed or recognition and trades accepted on the
  * corpus.
  *
  * The retired baseline read every child of a production each time the
  * production was popped, and tested only then whether a child had no entry
  * yet. A production pops once for each child that gains an entry, so a choice
  * of n members whose members gain their first entries one by one costs n²
  * child reads. Here each production keeps the number of its children still
  * without the entry they are read by (`Work.missing`), lowered when a class
  * gains its first entry of a kind, and a production with a child missing is
  * popped and left as it was. MEASURED (2026-11-02, CPUs 2 and 3, the
  * calls_10000 respelled point of a published points file at its seed, counters
  * added to the baseline's extraction in a scratch worktree, not committed):
  * the first round's extraction popped 64,749 productions and read 182,133,891
  * children, the graph's 10,546 productions having 64,727 children, the largest
  * a choice of 4,772.
  *
  * READINGS (2026-11-12): a class keeps its best entry of each reading of the
  * cost model (`CostModel`, THE CONTRACT), and a production is entered over
  * every combination of its children's entries, one of each reading, so that a
  * parent that does better over a child of a reading other than that of the
  * child class's best entry finds it. Under a cost model of one reading a class
  * keeps one entry, as the retired baseline did.
  *
  * Three passes reach it. The first (`worked`) finds the costs: a production is
  * keyed on the heap by the least cost it gives now (`readerKey`), not by its
  * class's best entry as the retired baseline keyed it. The other two
  * (`settled`) find the least entries whatever their cost, and then the entries
  * of those costs, in the order of content. Among entries of equal cost a class
  * keeps the first in the order of content (`ContentOrder`), where the retired
  * baseline kept the first found, which followed the graph's numbering of its
  * nodes: an extraction tie between two typed spellings of one cell, equal
  * under specialization_attraction (3-1) and compression (33), was decided by
  * the input's size (measured 2026-11-07 on `list_ending_in_a_boolean` with the
  * residual thunks of the binary choice branch). The productions, their readers
  * and the spelling are the baseline's own (`Extraction.productions`,
  * `Extraction.spelled`), less the classes the model repels, which have no
  * entry (`Extraction.productions` over the model, `CostModel.repeller`).
  * Nothing here reads a type or names a lemma or a combinator: it reads the
  * graph's layers, the costs the caller's model gives and the productions it
  * calls repellers.
  *
  * It began as a copy of the baseline extraction (`com.yang_bo.gezi.extraction.Extraction`,
  * a port of the Prolog baseline's), changed only by the count, in a module of
  * its own, contest-modules-counted-extraction, and was moved into the
  * framework when that module retired.
  */
object CountedExtraction:

  /** Every class's kept entries (THE DEFINITION above), read from the
    * productions without children: the costs first (`worked`), then the entries
    * of those costs (`settled`); or nothing when `stop` is requested at a
    * check. The checks are once per production taken from a heap (`worked`,
    * `settledAll`) and once after each pass, since a cost model that reads the
    * same signal (`ModuleCostModel.stop`) cuts its candidate enumeration short
    * and leaves the pass incomplete. A caller that gets nothing gives its
    * inputs as written. The model's memo (`CostModel.Memo`) is threaded through
    * every call of its candidates in all three passes, from `emptyMemo`, and
    * dropped when the extraction ends: a memoized call gives the candidates the
    * plain call gives, so the memo changes cost, not the extraction.
    */
  def fixed[C <: NativeSpecializer & Singleton, Cost](
      graph: EGraph[C],
      names: Set[Configured[C]],
      model: CostModel[C, Cost],
      stop: StopSignal
  )(using C): Option[Extracted[C, Cost]] =
    fixedFrom[C, Cost, model.Memo](graph, names, model, stop)

  /** A cost model whose memo is `Held`. */
  private type Remembering[C <: NativeSpecializer & Singleton, Cost, Held] =
    CostModel[C, Cost] { type Memo = Held }

  /** `fixed`, the model's memo threaded through every call of its candidates,
    * from `emptyMemo` at the start to the end of the last pass, where it is
    * dropped.
    */
  private def fixedFrom[C <: NativeSpecializer & Singleton, Cost, Memo](
      graph: EGraph[C],
      names: Set[Configured[C]],
      model: Remembering[C, Cost, Memo],
      stop: StopSignal
  )(using C): Option[Extracted[C, Cost]] =
    val (listed, readers) = Extraction.productions(graph, names, model)
    given Ordering[Option[Cost]] = keyOrdering(model.ordering)
    val childless = listed.filter(_.shape.children.isEmpty)
    val heap = PairingHeap.of[Option[Cost], Int](
      childless.map(production => (None, production.number))
    )
    val initial = Work[C, Cost](
      readers.map((root, numbers) =>
        (root, ClassEntries.unentered[C, Cost](numbers))
      ),
      listed.map(_.shape.children.size),
      childless.map(_.number).toSet,
      Map.empty,
      Map.empty,
      Map.empty,
      Map.empty
    )
    // Only the costs of the first pass are kept, so that its entries are
    // collected before the second pass makes its own (measured 2026-11-13:
    // with both held, CriterionFourTest's list item ran out of its 304 MB).
    // The first pass is reduced to its costs by `map`, which returns before
    // `settled` starts: when `settled` ran inside a `flatMap` over the first
    // pass, the `Some` (`flatMap`'s receiver) and the lambda's parameter held
    // every entry of the first pass through the later passes (measured
    // 2026-11-16, the list item alone: the smallest heap that passed rose
    // from 376 MB to above 392 MB at d7a60af59, which brought the `flatMap`).
    //
    // A model that settles a production's children above a bound on their
    // numbers of entries (`CostModel.settledChildren`) makes the first pass
    // depend on the heap's order: an entering at fewer entries enumerates
    // what a later one settles, and the least entry of any entering is kept.
    // So the first pass is run once, and, where a production settles some
    // children at its final numbers of entries, the combinations of its
    // children's readings at the nodes it made in the trees the run kept are
    // recorded (`directivesOf`), every node of every kept tree, an entry the
    // run later superseded included; the first pass is then run again from
    // the start with each such production read once per recorded
    // combination, every child by that combination's reading, one entry
    // each, and the later passes read it alike. A directed production then
    // makes no reading the first run did not, and a production with no
    // directive, unsettled at the first run's final numbers, is unsettled at
    // any numbers no larger (`CostModel.settledChildren` is monotone), so
    // enumerates; by induction over the run no class holds a reading the
    // first run's did not, so no class has more entries than there (both
    // checked, `rerunChecked`). Under fixed directives every production's
    // candidates are monotone in its children's entries of each reading, so
    // the second run is the least fixed point whatever the heap's order, and
    // the later passes reach it. Every reading the first run kept is kept
    // again at no higher cost (checked as well), by induction on its kept
    // tree: a leaf is made again, a node of a directed production is made
    // over its recorded combination, and one of a production with no
    // directive is among that production's enumerated combinations; each
    // over its children's readings kept again at no higher cost.
    //
    // The cost: the first pass runs twice when some production settles at
    // its final numbers of entries, once otherwise, and the trees the first
    // run kept are walked once, each entry object once. In every pass a
    // directed production makes one candidate call per recorded combination
    // at each entering, at most the number of distinct combinations of its
    // children's readings among its nodes in the kept trees, each call over
    // one entry per child, so enumerating nothing.
    val firstRun = worked(listed, model, initial, heap, model.emptyMemo, stop)
      .map((run, memo) =>
        (targetsOf(run.classes), directivesOf(listed, model, run.classes), memo)
      )
    val costed = firstRun.flatMap((firstTargets, directives, memo) =>
      if directives.isEmpty then Some((firstTargets, directives, memo))
      else
        worked(
          listed,
          model,
          initial.copy(directives = directives),
          heap,
          memo,
          stop
        ).map((rerun, after) =>
          (
            rerunChecked(
              listed,
              model,
              firstTargets,
              directives,
              rerun.classes
            ),
            directives,
            after
          )
        )
    )
    costed.flatMap((costs, directives, memo) =>
      settled(listed, model, costs, directives, memo, stop).map(
        Extracted(_, model)
      )
    )

  /** Each production's directive (`directivesOf`), by its number: the
    * combinations of its children's readings it is read by, each a cost of each
    * child's reading in the order of `Shape.children`.
    */
  private type Directives[Cost] = Map[Int, Vector[Vector[Cost]]]

  /** The second run's targets, checked against the first run's: no production
    * without a directive is settled at the second run's numbers of entries,
    * each reading of each class the first run kept is kept at no higher cost,
    * and no class keeps a reading the first run's did not. Throws
    * `IllegalStateException` otherwise, naming the production or the class and
    * reading: the directives would then not fix every settling, and the passes
    * could disagree.
    */
  private def rerunChecked[C <: NativeSpecializer & Singleton, Cost](
      listed: Vector[Production[C]],
      model: CostModel[C, Cost],
      firstTargets: Map[Int, Targets[Cost]],
      directives: Directives[Cost],
      classes: Map[Int, ClassEntries[C, Cost]]
  ): Map[Int, Targets[Cost]] =
    listed
      .filterNot(production => directives.contains(production.number))
      .foreach { production =>
        val children = production.shape.children
        if children.nonEmpty then
          val counts = children.map(child =>
            classes
              .get(child)
              .fold(0)(entries =>
                if child == production.root then entries.looplessEntries.size
                else entries.entries.size
              )
          )
          if model.settledChildren(production.shape, counts).contains(true) then
            throw IllegalStateException(
              s"the production ${production.number} has no directive but is settled at the second run's numbers of entries $counts: ${production.shape}"
            )
      }
    val targets = targetsOf(classes)
    firstTargets.foreach { (root, first) =>
      val again = targets.getOrElse(root, Targets.none[Cost])
      def keptAgain(before: Vector[Cost], after: Vector[Cost]): Unit =
        before.foreach(cost =>
          if !after.exists(found =>
              model.sameReading(found, cost) && model.ordering
                .compare(found, cost) <= 0
            )
          then
            throw IllegalStateException(
              s"the class $root kept the reading of $cost in the first run and not at that cost in the second: $after"
            )
        )
      keptAgain(first.costs, again.costs)
      keptAgain(first.looplessCosts, again.looplessCosts)
    }
    targets.foreach { (root, again) =>
      val first = firstTargets.getOrElse(root, Targets.none[Cost])
      def notAdded(before: Vector[Cost], after: Vector[Cost]): Unit =
        after.foreach(cost =>
          if !before.exists(model.sameReading(_, cost)) then
            throw IllegalStateException(
              s"the class $root keeps the reading of $cost in the second run, which the first run's did not: $before"
            )
        )
      notAdded(first.costs, again.costs)
      notAdded(first.looplessCosts, again.looplessCosts)
    }
    targets

  /** The first pass's costs of each class, by reading, and its readers. */
  private def targetsOf[C <: NativeSpecializer & Singleton, Cost](
      classes: Map[Int, ClassEntries[C, Cost]]
  ): Map[Int, Targets[Cost]] =
    classes.view
      .mapValues(entries =>
        Targets(
          entries.entries.map(_.cost),
          entries.looplessEntries.map(_.cost),
          entries.readers
        )
      )
      .toMap

  /** The productions' directives: for a production the model settles some
    * children of at the numbers of entries the classes hold
    * (`CostModel.settledChildren`), one combination for each node it made in
    * the trees of the entries the classes kept, a kept entry's tree holding
    * entries its class later superseded, its children's readings those of the
    * node's child entries; no combination when no kept tree holds a node it
    * made. A production the model settles no child of has no directive.
    */
  private def directivesOf[C <: NativeSpecializer & Singleton, Cost](
      listed: Vector[Production[C]],
      model: CostModel[C, Cost],
      classes: Map[Int, ClassEntries[C, Cost]]
  ): Directives[Cost] =
    val settledOf = listed.flatMap { production =>
      val children = production.shape.children
      val counts = children.map(child =>
        classes
          .get(child)
          .fold(0)(entries =>
            if child == production.root then entries.looplessEntries.size
            else entries.entries.size
          )
      )
      val settled = if children.isEmpty then Vector.empty
      else model.settledChildren(production.shape, counts)
      if settled.contains(true) && model
          .mayDropChildren(production.shape)
          .contains(true)
      then
        throw IllegalStateException(
          s"the model settles children of ${production.shape}, some of whose children it may drop"
        )
      Option.when(settled.contains(true))(
        production.shape -> (production.number, settled)
      )
    }.toMap
    if settledOf.isEmpty then Map.empty
    else
      val numbers = settledOf.view.mapValues(_._1).toMap
      val recorded = combinationsRecorded(
        model,
        numbers,
        classes.values.toList.flatMap(entries =>
          entries.entries ++ entries.looplessEntries
        ),
        Set.empty,
        numbers.values.map(_ -> Vector.empty[Vector[Cost]]).toMap
      )
      recorded

  /** The combinations of children's readings at the nodes the directed
    * productions (`numbers`, by shape) made in the trees of the pending
    * entries, each entry object visited once (`EntryIdentity`), so that a tree
    * whose entries share child entries is walked in time linear in its distinct
    * entries; one combination per production for each set of readings
    * (`CostModel.sameReading`), whatever their costs.
    */
  @scala.annotation.tailrec
  private def combinationsRecorded[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      numbers: Map[Shape[C], Int],
      pending: List[Entry[C, Cost]],
      met: Set[EntryIdentity],
      found: Directives[Cost]
  ): Directives[Cost] =
    pending match
      case Nil           => found
      case entry :: rest =>
        val identity = EntryIdentity(entry)
        if met.contains(identity) then
          combinationsRecorded(model, numbers, rest, met, found)
        else
          val withEntry = numbers.get(entry.shape).fold(found) { number =>
            val combination = entry.childEntries.map(_.cost)
            val known = found(number)
            if known.exists(recorded =>
                recorded
                  .zip(combination)
                  .forall((left, right) => model.sameReading(left, right))
              )
            then found
            else found.updated(number, known :+ combination)
          }
          combinationsRecorded(
            model,
            numbers,
            entry.childEntries.toList ++ rest,
            met + identity,
            withEntry
          )

  /** An entry identified by the object on the heap, not by its structure, so
    * that a set of the entries met costs a lookup and no walk.
    */
  private final class EntryIdentity(val entry: Entry[?, ?]):
    override def equals(other: Any): Boolean = other match
      case that: EntryIdentity => entry eq that.entry
      case _                   => false
    override def hashCode: Int = System.identityHashCode(entry)

  /** The production's candidates over the options: without a directive the
    * candidates `call` gives over them; with one, those it gives over each
    * recorded combination's options, each child offered by its entries of the
    * combination's reading only, and none for a combination some child of which
    * has no such entry.
    */
  private def directedCandidates[
      C <: NativeSpecializer & Singleton,
      Cost,
      Memo
  ](
      model: CostModel[C, Cost],
      directive: Option[Vector[Vector[Cost]]],
      options: Vector[Vector[Entry[C, Cost]]],
      memo: Memo,
      call: (Vector[Vector[Entry[C, Cost]]], Memo) => (
          Vector[Entry[C, Cost]],
          Memo
      )
  ): (Vector[Entry[C, Cost]], Memo) =
    directive match
      case None               => call(options, memo)
      case Some(combinations) =>
        combinations.foldLeft((Vector.empty[Entry[C, Cost]], memo)) {
          case ((found, current), readings) =>
            val restricted = options
              .zip(readings)
              .map((entries, reading) =>
                entries.filter(entry => model.sameReading(entry.cost, reading))
              )
            if restricted.exists(_.isEmpty) then (found, current)
            else
              val (more, after) = call(restricted, current)
              (found ++ more, after)
        }

  /** The costs a class reached in the first pass, one per reading, and of its
    * productions that do not read it, and the productions that read the class.
    */
  private final case class Targets[Cost](
      costs: Vector[Cost],
      looplessCosts: Vector[Cost],
      readers: Vector[Int]
  )

  private object Targets:
    def none[Cost]: Targets[Cost] =
      Targets(Vector.empty, Vector.empty, Vector.empty)

  /** The classes' entries so far; the number of each production's children, by
    * its number, that have no entry of the kind they are read by: a child that
    * is the production's own class an entry of a production that does not read
    * it, any other child any entry of its class; the productions on the heap
    * (`pending`); how many times each class's entries and its entries of
    * productions that do not read it have changed (`entriesChanges`,
    * `looplessChanges`, by class); and of each production entered with every
    * child present, those counts of its children when it was last entered
    * (`stamps`) and its least candidate cost then (`lastKeys`).
    */
  private final case class Work[C <: NativeSpecializer & Singleton, Cost](
      classes: Map[Int, ClassEntries[C, Cost]],
      missing: Vector[Int],
      pending: Set[Int],
      entriesChanges: Map[Int, Int],
      looplessChanges: Map[Int, Int],
      stamps: Map[Int, Vector[Int]],
      lastKeys: Map[Int, Cost],
      directives: Directives[Cost] = Map.empty[Int, Vector[Vector[Cost]]]
  ):
    def entries(root: Int): ClassEntries[C, Cost] =
      classes.getOrElse(root, ClassEntries.unentered[C, Cost](Vector.empty))

    /** The change counts of the classes the production reads, in the order of
      * its children: the count of its own class's entries of productions that
      * do not read it where the child is its own class, of the child's entries
      * otherwise.
      */
    def stampOf(production: Production[C]): Vector[Int] =
      production.shape.children.map(child =>
        if child == production.root then looplessChanges.getOrElse(child, 0)
        else entriesChanges.getOrElse(child, 0)
      )

    /** The counts after the class `root` gained its first entry of a kind: one
      * less for each child of its readers that reads that kind, the children in
      * readers of the class itself when `loopless`, the children in other
      * readers otherwise. `readers` lists a reader once for each of its
      * children that is the class.
      */
    def missingLowered(
        listed: Vector[Production[C]],
        root: Int,
        readers: Vector[Int],
        loopless: Boolean
    ): Work[C, Cost] =
      val lowered = readers.foldLeft(missing) { (counts, reader) =>
        if (listed(reader).root == root) == loopless then
          val count = counts(reader)
          assert(
            count > 0,
            s"the production $reader has no child of the class $root left without an entry"
          )
          counts.updated(reader, count - 1)
        else counts
      }
      copy(missing = lowered)

  /** The order of heap keys: a class with no entry first, then by cost. */
  private def keyOrdering[Cost](
      ordering: Ordering[Cost]
  ): Ordering[Option[Cost]] =
    (left: Option[Cost], right: Option[Cost]) =>
      (left, right) match
        case (None, None)                      => 0
        case (None, Some(_))                   => -1
        case (Some(_), None)                   => 1
        case (Some(leftCost), Some(rightCost)) =>
          ordering.compare(leftCost, rightCost)

  /** The productions on the heap entered until none is left, the least key
    * first. A reader of a class whose entries changed is put on the heap unless
    * it is there already (`Work.pending`), keyed by `readerKey`; a production
    * popped is entered over its children's entries as they are then, unless
    * none of the classes it reads changed since it was last entered
    * (`Work.stampOf`), and an entering that changes nothing leaves the classes
    * as they are.
    *
    * The pass is label-correcting: its result, each class's costs of each
    * reading, is the least fixed point of entering, whatever the order of the
    * heap, where a production's candidates are monotone in its children's
    * entries. FIXME (2026-11-24): a thunk's candidates are not, under a model
    * that https://github.com/Atry/private-overlay/issues/2050 settles jointly
    * read fillings above a bound on their numbers of entries
    * (`com.yang_bo.gezi.strategies.ThunkCandidates`), or reads a thunk whole once its
    * contract fillings' entries grow past it: an entering at fewer entries
    * enumerates what a later one settles, and the least entry of any entering
    * is kept. `fixedFrom` runs this pass again under the combinations the first
    * run kept (`directivesOf`), monotone, so that every pass agrees; which
    * combinations the first run kept, and so the extraction above the bound,
    * may still depend on its heap's order. After any change of a class, every
    * production that reads it is on the heap, and each is entered, or skipped,
    * after it is popped; a skip is exact, since a production's candidates are a
    * function of its shape and its children's entries (`CostModel.candidates`)
    * and merging the same candidates again changes nothing, a class's entries
    * of a reading only improving under each ordering. So when the heap is empty
    * every production's last entering read its children's final entries. The
    * key orders the heap only: it decides how many enterings the pass takes,
    * not their result (CountedExtractionLawTest: the fixed point law, law (4),
    * and the extraction of a graph built in any order). Before, a reader was
    * put on the heap once for each change of each class it reads, its key
    * computed each time, and every pop entered it again: on
    * `contest-entries-solo`'s
    * repeated_library_hotspots_inlined_calls_10000_hot/respelled
    * (settles-front-joint, 2026-11-16) a thunk of 30 fillings was put on the
    * heap 358 times and entered 325 times over one input; on main 04d3cd817^1,
    * 8 of 12 enterings of that point's large thunks read unchanged children.
    */
  @tailrec
  private def worked[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      work: Work[C, Cost],
      heap: PairingHeap[Option[Cost], Int],
      memo: Memo,
      stop: StopSignal
  )(using Ordering[Option[Cost]]): Option[(Work[C, Cost], Memo)] =
    heap.taken match
      case None => Option.unless(stop.stopRequested)((work, memo))
      case Some(_) if stop.stopRequested => None
      case Some((_, number, rest))       =>
        val production = listed(number)
        val popped = work.copy(pending = work.pending - number)
        val (entered, readers, afterEntering) =
          if popped.stamps.get(number).contains(popped.stampOf(production)) then
            (popped, Vector.empty, memo)
          else productionEntered(listed, model, popped, production, memo)
        val (nextHeap, next, nextMemo) =
          readers.distinct.foldLeft((rest, entered, afterEntering)) {
            case ((current, state, memoSoFar), reader) =>
              if state.pending.contains(reader) then (current, state, memoSoFar)
              else
                val (key, keyed) =
                  readerKey(listed, model, state, reader, memoSoFar)
                (
                  current.added(key, reader),
                  state.copy(pending = state.pending + reader),
                  keyed
                )
          }
        worked(listed, model, next, nextHeap, nextMemo, stop)

  /** The key of a production put on the heap: none, first, while a child has no
    * entry of the kind it is read by; the least cost among the entries it gave
    * when last entered with every child present (`Work.lastKeys`); and only for
    * a production never so entered, the least cost among the entries it gives
    * over its children's entries now. The key of a production entered before is
    * that stale cost, not one computed again, since computing it lists the
    * production's candidates (a thunk's joint enumeration), and no cheaper
    * bound exists: a production's cost is not monotone across a child's
    * readings (a filter's Value and Closed), so its cost over each child's
    * least entry bounds nothing. A stale key is at or above the current one,
    * since a child's entries only improve, so a production is popped late,
    * never early. The retired baseline keyed a production by its class's best
    * entry, so that a class whose productions read n different children of
    * falling costs took the n of them in the order of its best entry's cost,
    * worst first, and its readers were entered again for each (measured
    * 2026-11-13 on programfamilies' list at 32, 64 and 128: one class of each
    * item entered 33, 66 and 130 times, its 128, 256 and 512 readers again each
    * time).
    */
  private def readerKey[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      work: Work[C, Cost],
      reader: Int,
      memo: Memo
  ): (Option[Cost], Memo) =
    if work.missing(reader) > 0 then (None, memo)
    else
      work.lastKeys.get(reader) match
        case Some(key) => (Some(key), memo)
        case None      =>
          val production = listed(reader)
          val (candidates, after) = directedCandidates(
            model,
            work.directives.get(reader),
            childOptions(model, production, work.classes),
            memo,
            model.memoizedCandidates(production.shape, _, _)
          )
          (candidates.map(_.cost).minOption(using model.ordering), after)

  /** The entries a production's children are read by: the class itself by its
    * entries of productions that do not read it, any other class by its
    * entries; an empty list for a child that has none.
    */
  private def childOptions[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      production: Production[C],
      classes: Map[Int, ClassEntries[C, Cost]]
  ): Vector[Vector[Entry[C, Cost]]] =
    admitted(
      model,
      production,
      production.shape.children.map(child =>
        classes
          .get(child)
          .fold(Vector.empty[Entry[C, Cost]])(entries =>
            if child == production.root then entries.looplessEntries
            else entries.entries
          )
      )
    )

  /** The children's entries less, at an application's function, each entry that
    * is a contract of a domain whose filter of the argument is repelled
    * (`Production.repelledDomains`, `CostModel.contractDomain`).
    */
  private def admitted[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      production: Production[C],
      options: Vector[Vector[Entry[C, Cost]]]
  ): Vector[Vector[Entry[C, Cost]]] =
    if production.repelledDomains.isEmpty then options
    else
      options.zipWithIndex.map((entries, position) =>
        if position != 0 then entries
        else
          entries.filterNot(entry =>
            model
              .contractDomain(entry.cost)
              .exists(production.repelledDomains.contains)
          )
      )

  /** The kept entries of the costs the classes reached (`costed`, THE
    * DEFINITION), in two passes of Knuth's generalization of Dijkstra's
    * algorithm over the order of content (`ContentOrder`). That order is
    * superior (an entry is larger than each of its children: the size comes
    * first) and monotone in the children (two entries of one shape compare by
    * their children, left to right), and a production's reading is a function
    * of its children's (`CostModel`, THE CONTRACT), so the first entry popped
    * for a class and reading is the least the pass admits.
    *
    * The first pass (`Pass.Least`) settles each class's least entry of each
    * reading whatever its cost: the least finite tree a child at an unpriced
    * position may be (`CostModel.pricedChildren`), since the parent's cost does
    * not read it. The second (`Pass.AtCost`) settles each class's entry of each
    * reading at its cost in `costed`, a child at a priced position read by its
    * entry of that pass and at an unpriced one by its least entry. Each class's
    * entries are listed by cost, then content.
    *
    * The second pass is THE DEFINITION under the contract's strictness at
    * priced positions (`CostModel`, THE CONTRACT): a priced child costlier than
    * its class's least cost of its reading makes the parent costlier, so only
    * children at their least cost keep the parent at its least. Under a cost
    * that saturates at a priced position it keeps a non-least tree without
    * throwing (CountedExtractionLawTest, law (6)), so the contract is the
    * guard: the modules an extraction may use say they meet it
    * (`com.yang_bo.gezi.strategies.NormalityModule.meetsExtractionContract`), checked by
    * laws on generated terms (`CostMonotonicityLawTest`,
    * `NarrowBlockCostMonotonicityLawTest`), not proved. Throws
    * `IllegalStateException` when an entry of `costed` is left unsettled,
    * naming the class, the reading's cost and the class's productions, and when
    * an entry over the settled children costs less than `costed` says (the
    * costs were then not the fixed point).
    */
  private def settled[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      costed: Map[Int, Targets[Cost]],
      directives: Directives[Cost],
      memo: Memo,
      stop: StopSignal
  ): Option[Map[Int, ClassEntries[C, Cost]]] =
    given Ordering[Entry[C, Cost]] =
      (left: Entry[C, Cost], right: Entry[C, Cost]) =>
        ContentOrder.compare(left, right)
    val unentered = costed.view
      .mapValues(target => ClassEntries.unentered[C, Cost](target.readers))
      .toMap
    for
      leastSettling <- settledAll(
        listed,
        model,
        Pass.Least(directives),
        seeded(listed, model, Pass.Least(directives), unentered, memo),
        stop
      )
      least = leastSettling.classes
      atCost = Pass.AtCost(costed, least, directives)
      costSettling <- settledAll(
        listed,
        model,
        atCost,
        seeded(listed, model, atCost, unentered, leastSettling.memo),
        stop
      )
    yield checked(listed, model, costed, costSettling.classes)

  /** The entries of the passes checked against the costs of the first pass (the
    * failures `settled` names).
    */
  private def checked[C <: NativeSpecializer & Singleton, Cost](
      listed: Vector[Production[C]],
      model: CostModel[C, Cost],
      costed: Map[Int, Targets[Cost]],
      classes: Map[Int, ClassEntries[C, Cost]]
  ): Map[Int, ClassEntries[C, Cost]] =
    costed.foreach { (root, target) =>
      val kept = classes(root)
      if kept.entries.size != target.costs.size || kept.looplessEntries.size != target.looplessCosts.size
      then
        val missing = target.costs.filterNot(cost =>
          kept.entries.exists(entry => model.sameReading(entry.cost, cost))
        )
        val missingLoopless = target.looplessCosts.filterNot(cost =>
          kept.looplessEntries.exists(entry =>
            model.sameReading(entry.cost, cost)
          )
        )
        throw IllegalStateException(
          s"the class $root has no entry at its least cost of the readings of $missing, nor among the productions that do not read it of $missingLoopless; its productions: ${listed.filter(_.root == root).map(_.shape).mkString(", ")}"
        )
    }
    classes

  /** The two passes of `settled`: the least entries whatever their cost, and
    * the entries at the costs of `costed`, over `least`'s at unpriced
    * positions.
    */
  private enum Pass[C <: NativeSpecializer & Singleton, Cost]:
    case Least(directives: Directives[Cost])
    case AtCost(
        costed: Map[Int, Targets[Cost]],
        least: Map[Int, ClassEntries[C, Cost]],
        directives: Directives[Cost]
    )

  /** The pass started: every production whose children it reads from no entry
    * of this pass, its candidates on the heap.
    */
  private def seeded[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      pass: Pass[C, Cost],
      unentered: Map[Int, ClassEntries[C, Cost]],
      memo: Memo
  )(using Ordering[Entry[C, Cost]]): Settling[C, Cost, Memo] =
    val start = Settling[C, Cost, Memo](unentered, PairingHeap.empty, memo)
    val independent = pass match
      case Pass.Least(_)        => listed.filter(_.shape.children.isEmpty)
      case Pass.AtCost(_, _, _) =>
        listed.filter(production =>
          !alwaysPricedOf(model, production).contains(true)
        )
    independent.foldLeft(start)((current, production) =>
      current.candidatesPushed(model, pass, production)
    )

  /** The positions of the production priced under every reading of its
    * children: priced by its shape (`CostModel.pricedChildren`) and never
    * dropped (`CostModel.mayDropChildren`). Throws `IllegalStateException` when
    * the model gives other than one per child.
    */
  private def alwaysPricedOf[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      production: Production[C]
  ): Vector[Boolean] =
    val priced = model.pricedChildren(production.shape)
    val mayDrop = model.mayDropChildren(production.shape)
    val count = production.shape.children.size
    if priced.size != count || mayDrop.size != count then
      throw IllegalStateException(
        s"the model prices ${priced.size} and may drop ${mayDrop.size} of the $count children of ${production.shape}"
      )
    priced.zip(mayDrop).map((isPriced, dropped) => isPriced && !dropped)

  /** The positions of the production priced under no reading of its children:
    * unpriced by its shape.
    */
  private def neverPricedOf[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      production: Production[C]
  ): Vector[Boolean] =
    model.pricedChildren(production.shape).map(!_)

  /** The entries with the entry put in its place by cost, then content. */
  private def inserted[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      entries: Vector[Entry[C, Cost]],
      entry: Entry[C, Cost]
  ): Vector[Entry[C, Cost]] =
    val (before, after) = entries.span(better(model, _, entry))
    (before :+ entry) ++ after

  /** The entries settled so far, by class, the entries on the heap, each with
    * the number of the production that gives it, and the model's memo.
    */
  private final case class Settling[
      C <: NativeSpecializer & Singleton,
      Cost,
      Memo
  ](
      classes: Map[Int, ClassEntries[C, Cost]],
      heap: PairingHeap[Entry[C, Cost], Int],
      memo: Memo
  ):

    /** The production's entries over its children's entries, those that may
      * settle an entry of the pass, put on the heap; nothing while a child has
      * no entry of the kind it is read by. The least pass reads every child by
      * its least entries (`CostModel.leastCandidates`); the pass at cost reads
      * a child priced under every reading by this pass's entries, one priced
      * under none by the least pass's, and one whose readings may drop it
      * (`CostModel.mayDropChildren`) by both: a combination that reads such a
      * child from the list its readings do not call for costs the same and is
      * no less by content, or costs more, so it never settles before the least
      * tree (`CostModel.candidates`).
      */
    def candidatesPushed(
        model: Remembering[C, Cost, Memo],
        pass: Pass[C, Cost],
        production: Production[C]
    )(using
        Ordering[Entry[C, Cost]]
    ): Settling[C, Cost, Memo] =
      val offered = pass match
        case Pass.Least(_) => childOptions(model, production, classes)
        case Pass.AtCost(_, least, _) =>
          val fromThisPass = childOptions(model, production, classes)
          val fromLeast = childOptions(model, production, least)
          val alwaysPriced = alwaysPricedOf(model, production)
          val neverPriced = neverPricedOf(model, production)
          production.shape.children.indices.toVector.map(position =>
            if alwaysPriced(position) then fromThisPass(position)
            else if neverPriced(position) then fromLeast(position)
            else fromThisPass(position) ++ fromLeast(position)
          )
      if offered.exists(_.isEmpty) then this
      else
        val (found, after) = pass match
          case Pass.Least(directives) =>
            directedCandidates(
              model,
              directives.get(production.number),
              offered,
              memo,
              model.memoizedLeastCandidates(production.shape, _, _)
            )
          case Pass.AtCost(_, _, directives) =>
            directedCandidates(
              model,
              directives.get(production.number),
              offered,
              memo,
              model.memoizedCandidates(production.shape, _, _)
            )
        val current = classes.getOrElse(
          production.root,
          ClassEntries.unentered[C, Cost](Vector.empty)
        )
        val wanted = consistent(model, pass, production, found).filter(
          candidate => settlesAny(model, pass, production, candidate, current)
        )
        copy(
          heap = wanted.foldLeft(heap)((current, candidate) =>
            current.added(candidate, production.number)
          ),
          memo = after
        )

    /** The candidates of the pass at cost whose child at each position its
      * readings may drop (`CostModel.mayDropChildren`) comes from the list its
      * own readings call for: a least entry where they drop it, this pass's
      * entry where they price it. The others cost the same and are no less by
      * content, or cost more, so they never settle before the least tree, and
      * pushing them is work only. Every candidate of the least pass.
      *
      * The two lists are not deduplicated, and a child is found in its list by
      * reference: a candidate's child entries are the very objects of the lists
      * it was made over, and comparing or hashing entries by structure walks
      * the whole entry under them, children shared at every level, which is
      * exponential in the term's depth (main's jit NativeRouteCompilationTest
      * hung in Entry.hashCode on a `.distinct` of the two lists, 2026-11-14).
      * An entry of this pass and an entry of the least pass equal by content
      * are of one cost, so of one reading: one reading prices the position or
      * drops it, and only the candidate over the entry its reading calls for is
      * kept, so that no two candidates equal by content reach the heap, whose
      * order would walk them whole (`ContentOrder`).
      */
    private def consistent(
        model: CostModel[C, Cost],
        pass: Pass[C, Cost],
        production: Production[C],
        found: Vector[Entry[C, Cost]]
    ): Vector[Entry[C, Cost]] = pass match
      case Pass.Least(_)            => found
      case Pass.AtCost(_, least, _) =>
        val mayDrop = alwaysPricedOf(model, production)
          .zip(neverPricedOf(model, production))
          .map((always, never) => !always && !never)
        if !mayDrop.contains(true) then found
        else
          val fromThisPass = childOptions(model, production, classes)
          val fromLeast = childOptions(model, production, least)
          found.filter { candidate =>
            val priced = CostModel.pricedUnder(
              model,
              production.shape,
              candidate.childEntries.map(_.cost)
            )
            mayDrop.indices.forall(position =>
              !mayDrop(position) || {
                val entry = candidate.childEntries(position)
                val calledFor = if priced(position) then fromThisPass(position)
                else fromLeast(position)
                calledFor.exists(_ eq entry)
              }
            )
          }

  /** Which of the class's two lists the candidate settles in the pass: its
    * entries, and its entries of productions that do not read it when the
    * production is one.
    */
  private def settling[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      pass: Pass[C, Cost],
      production: Production[C],
      candidate: Entry[C, Cost],
      current: ClassEntries[C, Cost]
  ): (Boolean, Boolean) =
    val loopless = !production.shape.children.contains(production.root)
    pass match
      case Pass.Least(_) =>
        val unsettled = (kept: Vector[Entry[C, Cost]]) =>
          !kept.exists(entry => model.sameReading(entry.cost, candidate.cost))
        (
          unsettled(current.entries),
          loopless && unsettled(current.looplessEntries)
        )
      case Pass.AtCost(costed, _, _) =>
        val target = costed.getOrElse(production.root, Targets.none[Cost])
        (
          settles(model, candidate, target.costs, current.entries),
          loopless && settles(
            model,
            candidate,
            target.looplessCosts,
            current.looplessEntries
          )
        )

  private def settlesAny[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      pass: Pass[C, Cost],
      production: Production[C],
      candidate: Entry[C, Cost],
      current: ClassEntries[C, Cost]
  ): Boolean =
    val (entry, loopless) =
      settling(model, pass, production, candidate, current)
    entry || loopless

  /** The candidate is of the cost of its reading among `target`, and that
    * reading is not yet among `kept`; false when `target` has no cost of its
    * reading. Throws `IllegalStateException` when it costs less than `target`'s
    * cost of its reading.
    */
  private def settles[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      candidate: Entry[C, Cost],
      target: Vector[Cost],
      kept: Vector[Entry[C, Cost]]
  ): Boolean =
    target.find(cost => model.sameReading(cost, candidate.cost)) match
      case None       => false
      case Some(cost) =>
        val order = model.ordering.compare(candidate.cost, cost)
        if order < 0 then
          throw IllegalStateException(
            s"an entry costs ${candidate.cost}, less than the fixed point's $cost of its reading: ${candidate.shape}"
          )
        order == 0 && !kept.exists(settledEntry =>
          model.sameReading(settledEntry.cost, candidate.cost)
        )

  /** The heap taken until it is empty, the least entry by content first. */
  @tailrec
  private def settledAll[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      pass: Pass[C, Cost],
      state: Settling[C, Cost, Memo],
      stop: StopSignal
  )(using Ordering[Entry[C, Cost]]): Option[Settling[C, Cost, Memo]] =
    state.heap.taken match
      case None => Option.unless(stop.stopRequested)(state)
      case Some(_) if stop.stopRequested   => None
      case Some((candidate, number, rest)) =>
        val production = listed(number)
        val root = production.root
        val current = state.classes.getOrElse(
          root,
          ClassEntries.unentered[C, Cost](Vector.empty)
        )
        val (entrySettled, looplessSettled) =
          settling(model, pass, production, candidate, current)
        val classes =
          if !entrySettled && !looplessSettled then state.classes
          else
            val entries = if entrySettled then
              inserted(model, current.entries, candidate)
            else current.entries
            val looplessEntries = if looplessSettled then
              inserted(model, current.looplessEntries, candidate)
            else current.looplessEntries
            state.classes.updated(
              root,
              current.copy(
                entries = entries,
                looplessEntries = looplessEntries,
                best = entries.headOption,
                bestLoopless = looplessEntries.headOption
              )
            )
        val next = Settling(classes, rest, state.memo)
        val pushed =
          if !entrySettled && !looplessSettled then next
          else
            current.readers.distinct.foldLeft(next)((pushedSoFar, reader) =>
              pushedSoFar.candidatesPushed(model, pass, listed(reader))
            )
        settledAll(listed, model, pass, pushed, stop)

  /** The production's entries over every combination of the entries its
    * children are read by, one per reading of the child (`CostModel`, THE
    * CONTRACT), the best of each reading among them kept by its class when
    * better than the class's entry of that reading, or when the class has none
    * of it, and likewise among the class's entries of productions that do not
    * read the class when the production is one; the readers of the class when
    * anything changed, none otherwise. A production with a child that has no
    * entry yet is left as it is, its children not read.
    */
  private def productionEntered[C <: NativeSpecializer & Singleton, Cost, Memo](
      listed: Vector[Production[C]],
      model: Remembering[C, Cost, Memo],
      work: Work[C, Cost],
      production: Production[C],
      memo: Memo
  ): (Work[C, Cost], Vector[Int], Memo) =
    if work.missing(production.number) > 0 then (work, Vector.empty, memo)
    else
      val root = production.root
      val children = production.shape.children
      val childOptions = children.map(child =>
        val kept = if child == root then work.entries(root).looplessEntries
        else work.entries(child).entries
        if kept.isEmpty then
          throw IllegalStateException(
            s"the production ${production.number} counts no child missing, and its child $child has no entry"
          )
        kept
      )
      // A function whose entries are all contracts repelled at this call
      // gives no candidate now; the production is entered again when its
      // class gains another entry, as a reader of it.
      val (candidates, after) = directedCandidates(
        model,
        work.directives.get(production.number),
        admitted(model, production, childOptions),
        memo,
        model.memoizedCandidates(production.shape, _, _)
      )
      val stamped = work.copy(
        stamps =
          work.stamps.updated(production.number, work.stampOf(production)),
        lastKeys = candidates
          .map(_.cost)
          .minOption(using model.ordering)
          .fold(work.lastKeys)(key =>
            work.lastKeys.updated(production.number, key)
          )
      )
      val bestOfEachReading = merged(model, Vector.empty, candidates)._1
      val current = work.entries(root)
      val (entries, entriesChanged) =
        merged(model, current.entries, bestOfEachReading)
      val loopless = !children.contains(root)
      val (looplessEntries, looplessChanged) =
        if loopless then
          merged(model, current.looplessEntries, bestOfEachReading)
        else (current.looplessEntries, false)
      if !entriesChanged && !looplessChanged then (stamped, Vector.empty, after)
      else
        val updated = current.copy(
          entries = entries,
          looplessEntries = looplessEntries,
          best = bestOf(model, entries),
          bestLoopless = bestOf(model, looplessEntries)
        )
        val kept = stamped.copy(
          classes = stamped.classes.updated(root, updated),
          entriesChanges =
            if entriesChanged then
              stamped.entriesChanges
                .updated(root, stamped.entriesChanges.getOrElse(root, 0) + 1)
            else stamped.entriesChanges,
          looplessChanges =
            if looplessChanged then
              stamped.looplessChanges
                .updated(root, stamped.looplessChanges.getOrElse(root, 0) + 1)
            else stamped.looplessChanges
        )
        val bestCounted =
          if current.entries.isEmpty && entries.nonEmpty then
            kept.missingLowered(listed, root, current.readers, loopless = false)
          else kept
        val looplessCounted =
          if current.looplessEntries.isEmpty && looplessEntries.nonEmpty then
            bestCounted.missingLowered(
              listed,
              root,
              current.readers,
              loopless = true
            )
          else bestCounted
        (looplessCounted, current.readers, after)

  /** The candidate is better than the entry: of less cost, or of equal cost and
    * first in the order of content.
    */
  private def better[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      candidate: Entry[C, Cost],
      entry: Entry[C, Cost]
  ): Boolean =
    val order = model.ordering.compare(candidate.cost, entry.cost)
    order < 0 || (order == 0 && ContentOrder.compare(candidate, entry) < 0)

  /** The entries, one per reading, with each candidate in place of the entry of
    * its reading when better, or added when the reading has none; and whether
    * any changed.
    */
  private def merged[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      entries: Vector[Entry[C, Cost]],
      candidates: Vector[Entry[C, Cost]]
  ): (Vector[Entry[C, Cost]], Boolean) =
    candidates.foldLeft((entries, false)) { case ((kept, changed), candidate) =>
      kept.indexWhere(entry =>
        model.sameReading(entry.cost, candidate.cost)
      ) match
        case -1       => (kept :+ candidate, true)
        case position =>
          if better(model, candidate, kept(position)) then
            (kept.updated(position, candidate), true)
          else (kept, changed)
    }

  /** The best of the entries over all readings. */
  private def bestOf[C <: NativeSpecializer & Singleton, Cost](
      model: CostModel[C, Cost],
      entries: Vector[Entry[C, Cost]]
  ): Option[Entry[C, Cost]] =
    entries.reduceOption((kept, next) =>
      if better(model, next, kept) then next else kept
    )
