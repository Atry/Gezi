package gezi.strategies

import gezi.saturation.StopSignal
import gezi.egraph.EGraph
import gezi.extraction.CostModel
import gezi.extraction.Extraction
import gezi.extraction.Shape
import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.Layer
import gezi.standardlibrary.StandardLibraryIndex
import gezi.ir.NoinlineLeaf
import scala.collection.immutable.TreeSet
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** The best entries a local extraction found for classes that are no
  * opened closure's and read none, which a write-back never changes (it
  * unites an opened closure's class only), and the spellings of those
  * classes: a cost and a spelling kept from one body's spelling to the next
  * within a round, so that a body spells only the classes it reaches and
  * not again the cached classes under them (2026-11-21: with the
  * spellings not kept, 61 bodies of 7518 reached classes in all spent
  * 3.88 GB of allocation re-spelling the classes under them, and the point
  * ran a 2g heap out).
  */
final case class SpellingCache[C <: NativeSpecializer & Singleton, Cost](best: Map[Int, (Cost, Shape[C])], spelled: Map[Int, Configured[C]])

object SpellingCache:
  def empty[C <: NativeSpecializer & Singleton, Cost]: SpellingCache[C, Cost] = SpellingCache(Map.empty, Map.empty)

/** How long the best entries and spellings a pass of write-backs finds for
  * classes that are no opened closure's and read none are kept.
  */
enum SpellingRetention:

  /** Kept from one body's spelling to the next within a pass, and dropped
    * at the next pass.
    */
  case KeptWithinAPass

  /** Dropped after every body: each body spells every class it reaches. */
  case NotKept

  /** Kept from one body to the next within a pass and from one pass to the
    * next of one saturation (`CarriedSpellings`), the entries of every class
    * the graph changed since, or that reads one, dropped at the start of
    * each pass (`LocalExtraction.carriedCache`).
    */
  case KeptAcrossPasses

/** The spellings a pass of write-backs leaves for the next pass under
  * `SpellingRetention.KeptAcrossPasses`: the cache; the cost model and the
  * named classes it was found under, the inputs of the spelling besides the
  * graph; and the marks of the graph the pass started from, its node count
  * and its union count, from which the next pass reads what changed since in
  * the graph's two append-only logs (nodes are numbered by creation, and
  * `EGraph.unions` records every union in order).
  */
final case class CarriedSpellings[C <: NativeSpecializer & Singleton, Cost](
    cache: SpellingCache[C, Cost],
    prepared: LocalExtraction.Prepared[C, Cost],
    nodeCount: Int,
    unionCount: Int
)

object LocalExtraction:

  /** What a pass of write-backs reads once: the cost model, and the class
    * of each name filed in the graph.
    */
  final case class Prepared[C <: NativeSpecializer & Singleton, Cost](model: CostModel[C, Cost], namedClasses: Map[Int, Configured[C]])

  /** The carried cache's entries that the graph has left as they were: those
    * of a class that is still a root, that no node or union made since the
    * marks touched, that is not an opened closure's (a write-back of this
    * pass may unite it), whose name filing is unchanged, and that reads none
    * of these classes, the touched classes closed upward through
    * `EGraph.classUsers`. An entry whose class reads a changed class could
    * have a cheaper production now, or a spelling that misses a typed branch
    * a later pass added; a spelling kept from an earlier graph is still a
    * term of its class, since a union only adds equalities, so a class this
    * misses would cost the spelling's quality and not its soundness. The
    * whole cache is dropped when the cost model differs. Filing a name adds
    * a node or unites the name's node with a class, so a class whose filing
    * changed is touched already; the named classes are compared as well, so
    * that this does not rest on how a filing is made.
    *
    * The upward closure can reach most of the graph when a change lands in
    * a class many classes read, such as a type shared by every element of a
    * list; what the option saves depends on where a pass's changes land.
    */
  def carriedCache[C <: NativeSpecializer & Singleton, Cost](
      carried: CarriedSpellings[C, Cost],
      graph: EGraph[C],
      prepared: Prepared[C, Cost],
      openedClosures: Set[Int]
  ): SpellingCache[C, Cost] =
    if carried.prepared.model != prepared.model then SpellingCache.empty[C, Cost]
    else
      val madeRoots = (carried.nodeCount until graph.nodeCount).map(graph.root)
      val unitedRoots = graph.unions.drop(carried.unionCount).flatMap(union => Vector(graph.root(union.first), graph.root(union.second)))
      val carriedNames = carried.prepared.namedClasses.map((root, name) => graph.root(root) -> name)
      val renamedRoots = (carriedNames.keySet ++ prepared.namedClasses.keySet).filter(root => carriedNames.get(root) != prepared.namedClasses.get(root))
      val touched = readersClosed(graph, (madeRoots ++ unitedRoots ++ openedClosures.map(graph.root) ++ renamedRoots).toList)
      def kept(root: Int): Boolean = graph.root(root) == root && !touched.contains(root)
      SpellingCache(
        carried.cache.best.filter((root, _) => kept(root)),
        carried.cache.spelled.filter((root, _) => kept(root))
      )

  /** The classes given and every class that reads one of them, through the
    * live nodes that read a class as a child in any role.
    */
  private def readersClosed[C <: NativeSpecializer & Singleton](graph: EGraph[C], roots: List[Int]): Set[Int] =
    @scala.annotation.tailrec
    def visited(pending: List[Int], seen: Set[Int]): Set[Int] = pending match
      case Nil                        => seen
      case next :: rest if seen(next) => visited(rest, seen)
      case next :: rest               => visited(graph.classUsers(next).map(graph.root).toList ::: rest, seen + next)
    visited(roots, Set.empty)

  /** The finalization's state: the finalized classes' best entries; the
    * number of each production's children, by its number, not yet finalized
    * (a child read twice counted twice); each class not yet finalized that
    * has a candidate, with its least candidate's cost and production number;
    * and those candidates ordered by cost and then class.
    */
  private final case class Finalization[C <: NativeSpecializer & Singleton, Cost](
      best: Map[Int, (Cost, Shape[C])],
      missing: Vector[Int],
      candidates: Map[Int, (Cost, Int)],
      queue: TreeSet[(Cost, Int)]
  )

/** An extraction of one best entry for each class a body reads, and the
  * body's class spelled by them, so that a write-back costs the body's size
  * and not the graph's.
  * The
  * best entries are found by Knuth's generalization of Dijkstra's algorithm
  * to grammars (D. E. Knuth, "A generalization of Dijkstra's algorithm",
  * Information Processing Letters 6(1), 1977; `finalized`), so that every
  * class's best entry reads only classes finalized before it: the best
  * entries form a DAG, and the spelling ends, whatever the cost model. A
  * class is finalized at the least cost of its finite derivations when the
  * model is superior (a production costs no less than each of its
  * children). `ModuleCostModel` is not: an unpriced child (a parallel's
  * criterion, a thunk's filling that its code reads only in a criterion or
  * not at all, a choice's member a module says the backend does not run)
  * can cost more than its parent, and there
  * a class can be finalized before a cheaper production of it has all its
  * children finalized, and keeps the dearer entry. One entry per class could
  * not hold the cheaper tree in every such case anyway: where a cycle
  * through an unpriced position is cheaper than the class's other
  * productions, the least finite tree reads the class inside itself through
  * a dearer production. The case (2026-11-21, on
  * repeated_library_hotspots_calls_10000_hot direct with a round that opens
  * closures): class 7683's least entry was `Apply(8173, 7361)` and class
  * 8173's `Thunk(Slot, [Ignored], [7683])`, the constant closure λ_. ⟨7683⟩;
  * the relaxation that this algorithm replaced kept both, and spelling 7683
  * as `(λ_. 7683) 7361` never ended. A class
  * that holds a name of `names` is spelled by the name and not read
  * through, so a library define's body is never visited. A class that holds
  * no closure and reads none keeps its best entry in the cache: a
  * write-back unites closures only, so its entry stays the best.
  *
  * The productions and their order are those of `Extraction.productions`:
  * the live nodes of each class, a choice that absorbs its class left out,
  * and the names filed into it.
  */
final case class LocalExtraction[C <: NativeSpecializer & Singleton](
    modules: Vector[NormalityModule[C]],
    names: StandardLibraryIndex[C] => Set[Configured[C]],
    spellingRetention: SpellingRetention
):

  TermOrder.extractionModulesChecked(modules)

  /** The cost model and the classes of the names, read once for every body
    * a pass of write-backs spells: a write-back unites closures, never a
    * name's class.
    */
  def prepared(index: StandardLibraryIndex[C], graph: EGraph[C]): LocalExtraction.Prepared[C, ModuleCost] =
    LocalExtraction.Prepared(
      // FIXME: `prepared` has no signal of its own; its write-backs read none, so a stop reaches only the extraction proper. https://github.com/Atry/private-overlay/issues/2032
      // FIXME: the write-backs read jointly read fillings as https://github.com/Atry/private-overlay/issues/2032
      // `JointReading.measured` says, fixed for the saturator that opens bodies; the round's extractor is given its own.
      ModuleCostModel(modules, TermReading(index), StopSignal.NeverStopped),
      names(index).flatMap(name => graph.instructionNode(name).map(node => graph.root(node) -> name)).toMap
    )

  /** The body's class spelled, and the cache with the entries it found for
    * classes that hold no closure.
    */
  def spelled[Cost](
      prepared: LocalExtraction.Prepared[C, Cost],
      graph: EGraph[C],
      body: Int,
      cache: SpellingCache[C, Cost],
      openedClosures: Set[Int]
  ): (Configured[C], SpellingCache[C, Cost]) =
    val model = prepared.model
    val namedClasses = prepared.namedClasses
    val classes = reached(graph, graph.root(body), namedClasses, cache)
    val productions = classes.toVector.flatMap(root =>
      namedClasses.get(root) match
        case Some(name) => Vector((root, Shape.Name(name)))
        case None =>
          graph
            .classMembers(root)
            .filterNot(member => graph.patternViews.contains(member.node) || Extraction.absorbedChoice(graph, root, member.layer))
            .map(member => (root, Shape.Node(member.node, member.layer)))
    )
    val best = finalized(graph, productions, model, cache.best)
    val (made, spelling) = spelledClass(graph, graph.root(body), best, cache.spelled)
    val closureFree = classesWithoutClosures(graph, classes, cache, openedClosures.map(graph.root))
    (
      spelling,
      SpellingCache(
        cache.best ++ closureFree.flatMap(root => best.get(root).map(root -> _)),
        cache.spelled ++ closureFree.flatMap(root => made.get(root).map(root -> _))
      )
    )

  /** The classes the root reads through the productions of the classes it
    * reaches, not read through a named class nor through one the cache
    * holds, each after the classes it reads where no cycle passes through
    * them (a postorder, which `classesWithoutClosures` reads in one pass, and
    * whose productions, in this order, break the ties of `finalized`).
    *
    * A member that is no production, a choice its class absorbs
    * (`Extraction.absorbedChoice`), is not read through: a class reached only
    * through such members is read by no production, so leaving it out changes
    * no best entry and no spelling of the classes still reached. Finalization
    * reads only productions, its queue is ordered by cost and class, and its
    * ties compare production numbers within one class only, whose members
    * keep their order. The judgments of a typing, `x + (x ∥ t)`, are such
    * choices, and through them every body reached the classes of its types.
    * `classesWithoutClosures` keeps reading every member, so a class whose
    * absorbed member reads a class this walk leaves out is not cached: a
    * write-back's congruence through that class could unite the class with
    * another and give it new productions.
    */
  private def reached[Cost](
      graph: EGraph[C],
      root: Int,
      namedClasses: Map[Int, Configured[C]],
      cache: SpellingCache[C, Cost]
  ): Vector[Int] =
    @scala.annotation.tailrec
    def visited(pending: List[(Int, Boolean)], seen: Set[Int], order: Vector[Int]): Vector[Int] = pending match
      case Nil => order
      case (next, true) :: rest => visited(rest, seen, order :+ next)
      case (next, false) :: rest if seen(next) || cache.best.contains(next) => visited(rest, seen, order)
      case (next, false) :: rest if namedClasses.contains(next) => visited(rest, seen + next, order :+ next)
      case (next, false) :: rest =>
        val children = graph
          .classMembers(next)
          .filterNot(member => Extraction.absorbedChoice(graph, next, member.layer))
          .flatMap(_.layer.children.map(graph.root))
          .distinct
        visited(children.toList.map((_, false)) ::: (next, true) :: rest, seen + next, order)
    visited(List((root, false)), Set.empty, Vector.empty)

  /** The classes of `classes` that hold no closure and read none, a class of
    * the cache reading none.
    */
  private def classesWithoutClosures[Cost](
      graph: EGraph[C],
      classes: Vector[Int],
      cache: SpellingCache[C, Cost],
      openedClosures: Set[Int]
  ): Set[Int] =
    classes.foldLeft(Set.empty[Int]) { (found, root) =>
      val free = !openedClosures.contains(root) && graph.classMembers(root).forall(member =>
        member.layer.children.map(graph.root).forall(child => found.contains(child) || cache.best.contains(child))
      )
      if free then found + root else found
    }

  /** Each class's best production and its cost, by Knuth's generalization
    * of Dijkstra's algorithm: a production is a candidate of its class once
    * every child of it is finalized, and the class whose least candidate is
    * least, by cost and then by class, is finalized with that candidate as
    * its best, which no later candidate changes; among candidates of equal
    * cost a class keeps the first production in the order of
    * `productions`. The cache's entries are finalized from the start and
    * stay. A class none of whose productions ever has every child finalized
    * (one with no finite derivation within the reached classes) gets no
    * entry, and spelling it throws. Each production is counted down once for
    * each of its children and offered at most once more, so the time is
    * O(P log P) in the productions and their children.
    */
  private def finalized[Cost](
      graph: EGraph[C],
      productions: Vector[(Int, Shape[C])],
      model: CostModel[C, Cost],
      cached: Map[Int, (Cost, Shape[C])]
  ): Map[Int, (Cost, Shape[C])] =
    val childRoots = productions.map((_, shape) => shape.children.map(graph.root))
    val readers = childRoots.zipWithIndex
      .flatMap((children, number) => children.filterNot(cached.contains).map(_ -> number))
      .groupMap(_._1)(_._2)
    val missing = childRoots.map(_.count(child => !cached.contains(child)))
    given Ordering[(Cost, Int)] = Ordering.Tuple2(using model.ordering, Ordering.Int)
    val start = LocalExtraction.Finalization(cached, missing, Map.empty, TreeSet.empty[(Cost, Int)])
    val offered = missing.indices
      .filter(missing(_) == 0)
      .foldLeft(start)((state, number) => candidateOffered(productions, childRoots, model, state, number))
    finalizedFrom(productions, childRoots, readers, model, offered)

  /** The classes finalized one at a time, the least candidate first, until
    * no candidate is left.
    */
  @scala.annotation.tailrec
  private def finalizedFrom[Cost](
      productions: Vector[(Int, Shape[C])],
      childRoots: Vector[Vector[Int]],
      readers: Map[Int, Vector[Int]],
      model: CostModel[C, Cost],
      state: LocalExtraction.Finalization[C, Cost]
  ): Map[Int, (Cost, Shape[C])] =
    state.queue.headOption match
      case None => state.best
      case Some(least @ (_, root)) =>
        val (cost, number) =
          state.candidates.getOrElse(root, throw IllegalStateException(s"the class $root is queued with no candidate"))
        val (productionRoot, shape) = productions(number)
        assert(productionRoot == root, s"the candidate $number of the class $root is a production of $productionRoot")
        val fixed = state.copy(
          best = state.best.updated(root, (cost, shape)),
          candidates = state.candidates - root,
          queue = state.queue - least
        )
        val lowered = readers.getOrElse(root, Vector.empty).foldLeft(fixed) { (current, reader) =>
          val count = current.missing(reader) - 1
          assert(count >= 0, s"the production $reader has no child of the class $root left unfinalized")
          val next = current.copy(missing = current.missing.updated(reader, count))
          if count == 0 then candidateOffered(productions, childRoots, model, next, reader) else next
        }
        finalizedFrom(productions, childRoots, readers, model, lowered)

  /** The production, every child of which is finalized, offered as a
    * candidate of its class: taken when its class is not finalized and it
    * costs less than the class's candidate, or as much and comes before it
    * in `productions`.
    */
  private def candidateOffered[Cost](
      productions: Vector[(Int, Shape[C])],
      childRoots: Vector[Vector[Int]],
      model: CostModel[C, Cost],
      state: LocalExtraction.Finalization[C, Cost],
      number: Int
  ): LocalExtraction.Finalization[C, Cost] =
    val (root, shape) = productions(number)
    if state.best.contains(root) then state
    else
      val childCosts = childRoots(number).map(child =>
        state.best
          .getOrElse(child, throw IllegalStateException(s"the production $number reads the unfinalized class $child"))
          ._1
      )
      val cost = model.cost(shape, childCosts)
      state.candidates.get(root) match
        case Some((known, knownNumber))
            if model.ordering.compare(known, cost) < 0 ||
              (model.ordering.compare(known, cost) == 0 && knownNumber < number) =>
          state
        case known =>
          state.copy(
            candidates = state.candidates.updated(root, (cost, number)),
            queue = known.fold(state.queue)((knownCost, _) => state.queue - ((knownCost, root))) + ((cost, root))
          )

  /** The class spelled by its best production, each class once. Stack-safe
    * by trampolining (`TailCalls`): a spelling as deep as the program's
    * nesting recursed once per level and overflowed the stack on deep
    * programs (2026-11-21: a JVM's StackOverflowError at this method on
    * six direct points of repeated_library_hotspots, the first round opening
    * closures).
    */
  private def spelledClass[Cost](
      graph: EGraph[C],
      root: Int,
      best: Map[Int, (Cost, Shape[C])],
      made: Map[Int, Configured[C]]
  ): (Map[Int, Configured[C]], Configured[C]) =
    spelledClassStep(graph, root, best, made).result

  private def spelledClassStep[Cost](
      graph: EGraph[C],
      root: Int,
      best: Map[Int, (Cost, Shape[C])],
      made: Map[Int, Configured[C]]
  ): TailRec[(Map[Int, Configured[C]], Configured[C])] =
    made.get(root) match
      case Some(spelled) => done((made, spelled))
      case None =>
        val (_, shape) = best.getOrElse(root, throw IllegalStateException(s"the class $root has no entry"))
        shape match
          case Shape.Name(name)                => done((made.updated(root, name), name))
          case Shape.Node(_, NoinlineLeaf(leaf)) => done((made.updated(root, leaf), leaf))
          case Shape.Node(_, layer) =>
            childrenSpelled(graph, layer.children.toList.map(graph.root), best, made, Vector.empty).map((afterChildren, children) =>
              val spelledOf = layer.children.map(graph.root).zip(children).toMap
              val instruction = graph.store.construction.instruction(layer)(child => spelledOf(graph.root(child)))
              (afterChildren.updated(root, instruction), instruction)
            )
          case pattern =>
            throw IllegalStateException(s"the local extraction lists names and nodes only, not $pattern")

  /** The children's classes spelled in order, each through `spelledClassStep`. */
  private def childrenSpelled[Cost](
      graph: EGraph[C],
      pending: List[Int],
      best: Map[Int, (Cost, Shape[C])],
      made: Map[Int, Configured[C]],
      spelled: Vector[Configured[C]]
  ): TailRec[(Map[Int, Configured[C]], Vector[Configured[C]])] =
    pending match
      case Nil => done((made, spelled))
      case child :: rest =>
        tailcall(spelledClassStep(graph, child, best, made)).flatMap((next, instruction) =>
          tailcall(childrenSpelled(graph, rest, best, next, spelled :+ instruction))
        )
