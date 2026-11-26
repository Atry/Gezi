package gezi.extraction

import gezi.egraph.EGraph
import gezi.egraph.MemberShape
import gezi.ir.DispatchPattern
import gezi.ir.Fallback
import gezi.ir.{Layer, LayerWith}
import gezi.ir.NotTerm
import gezi.ir.Specialization
import gezi.ir.SpecializationRange
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel}
import gezi.ir.{Configured, NativeSpecializer}

/** What a production spells: a live node's layer over the roots of its
  * children's classes; a name, an instruction whose node is in the class and
  * that spells its term in one leaf; or a dispatch pattern a live choice
  * node is read as (`DispatchPattern`), over the classes of its parts and
  * spelled as the pattern is built (`DispatchPattern.spelled`): a
  * specialization choice `F A + T`, T its typed member, or a judgment
  * `X + (X ∥ T)`.
  */
enum Shape[C <: NativeSpecializer & Singleton]:
  case Node(node: Int, layer: LayerWith[Int, Configured[C]])
  case Name(instruction: Configured[C])
  case Specialized[C <: NativeSpecializer & Singleton](node: Int, specialization: Specialization[Int]) extends Shape[C]
  case Judged[C <: NativeSpecializer & Singleton](node: Int, fallback: Fallback[Int]) extends Shape[C]

  /** The classes the production reads, in the order of its layer or of the
    * pattern's parts.
    */
  def children: Vector[Int] = this match
    case Node(_, layer)                 => layer.children
    case Name(_)                        => Vector.empty
    case Specialized(_, specialization) => specialization.parts
    case Judged(_, fallback)            => fallback.parts

object Shape:

  /** What the production's shape spells over its children's spellings, in
    * the order of `children`, each layer made by `make`: a name or a leaf
    * its instruction, made by `leaf`.
    */
  def spelled[C <: NativeSpecializer & Singleton, Node](
      shape: Shape[C],
      children: Vector[Node],
      leaf: Configured[C] => Node,
      make: Layer[Node] => Node
  )(using NotTerm[Node]): Node =
    shape match
      case Name(instruction)                => leaf(instruction)
      case Node(_, NoinlineLeaf(instruction)) => leaf(instruction)
      case Node(_, layer)              => make(layer.over(children))
      case Specialized(_, specialization) =>
        DispatchPattern.spelled(partsOver(specialization, children), make)
      case Judged(_, fallback) =>
        val Vector(value, criterion) = children: @unchecked
        DispatchPattern.spelled(Fallback(value, criterion, fallback.valueFirst), make)

  /** The term the production's shape spells over its children's terms, in the order of `children`: a name or a leaf
    * its instruction, a layer built over the children through the configuration (`NativeSpecializer.built`), and a
    * dispatch pattern spelled as its term (`DispatchPattern.spelledTerm`), so that a term is never a layer's child that
    * the IR's public constructors build.
    */
  def spelledTerm[C <: NativeSpecializer & Singleton](shape: Shape[C], children: Vector[Configured[C]])(using
      specializer: C
  ): Configured[C] =
    shape match
      case Name(instruction)                  => instruction
      case Node(_, NoinlineLeaf(instruction)) => instruction
      case Node(_, layer)                     => specializer.built(layer.over(children.indices.toVector))(children)
      case Specialized(_, specialization)     => DispatchPattern.spelledTerm(partsOver(specialization, children))
      case Judged(_, fallback) =>
        val Vector(value, criterion) = children: @unchecked
        DispatchPattern.spelledTerm(Fallback(value, criterion, fallback.valueFirst))

  /** The specialization with its parts replaced, in the order of `parts`,
    * by the nodes given.
    */
  def partsOver[Node](specialization: Specialization[Int], nodes: Vector[Node]): Specialization[Node] =
    specialization.range match
      case SpecializationRange.Absent =>
        val Vector(function, argument, domain) = nodes: @unchecked
        Specialization(function, argument, domain, SpecializationRange.Absent, specialization.untypedFirst)
      case SpecializationRange.Filtered(_) =>
        val Vector(function, argument, domain, range) = nodes: @unchecked
        Specialization(function, argument, domain, SpecializationRange.Filtered(range), specialization.untypedFirst)
      case SpecializationRange.Contracted(_) =>
        val Vector(function, argument, domain, contract) = nodes: @unchecked
        Specialization(function, argument, domain, SpecializationRange.Contracted(contract), specialization.untypedFirst)

/** A production of a class: its number, in the order the productions were
  * listed, the root of its class and its shape; and, for an application,
  * the criteria whose filter of its argument is a repelled class
  * (`Extraction.productions` over a model), so that its function is read by
  * no entry that is a contract of such a domain (`CostModel.contractDomain`):
  * the call keeps the function's other entries, the specialization at that
  * call being taken from the knowledge's repeller as at its typed version.
  */
final case class Production[C <: NativeSpecializer & Singleton](
    number: Int,
    root: Int,
    shape: Shape[C],
    repelledDomains: Set[Int] = Set.empty
)

/** An entry: a production's shape with an entry for each child, made before
  * it, and its cost, so that an entry spells a finite term.
  *
  * The hash code is computed once, when the entry is made, from its shape
  * and the hash codes its child entries already hold, so it costs the
  * entry's arity and never walks the term. The cost is left out of the
  * hash: a cost is the model's function of the shape and the child entries'
  * costs, so entries of one shape over equal children are of one cost
  * anyway, and a cost's own hash is the caller's, whose size the extraction
  * does not bound (a module's state may hold a map of terms). Equality walks the two
  * entries together as graphs: it stops at a pair that is one entry on the
  * heap, at a pair whose held hash codes differ, and at a pair already met
  * in the same comparison, so it costs the pairs of distinct entries it
  * meets and not the size of the term. An extraction's entries share their
  * children at every level, and the hash and equality that Scala derives for
  * a case class walk them as a tree, exponentially in the depth: a
  * `.distinct` of entries in the extraction's pass at cost held main's jit
  * NativeRouteCompilationTest for 11 to 13 minutes in `Entry.hashCode`
  * (2026-11-14), as `gezi.frontend.Structural`'s hash once held
  * ParallelSetLawTest for two hours.
  */
final case class Entry[C <: NativeSpecializer & Singleton, Cost](cost: Cost, shape: Shape[C], childEntries: Vector[Entry[C, Cost]]):

  /** The number of layers and names of the term the entry spells, a shared
    * child entry counted at each of its places; read from the children's,
    * which were made before the entry.
    */
  val size: BigInt =
    // The sizes of the children are numbers, no term: the layer made over them is counted, never built as a term.
    given NotTerm[BigInt] = NotTerm.granted[BigInt]
    Shape.spelled[C, BigInt](shape, childEntries.map(_.size), _ => BigInt(1), layer => layer.children.foldLeft(BigInt(1))(_ + _))

  /** The hash code, from the shape's and the child entries' held hash codes
    * (`Entry.entryHash`).
    */
  private val heldHash: Int = Entry.entryHash(shape, childEntries)

  override def hashCode: Int = heldHash

  override def equals(other: Any): Boolean = other match
    case that: Entry[?, ?] => Entry.allEqual(List(Entry.EntryPair(this, that)), Set.empty)
    case _              => false

object Entry:

  /** Two entries compared, identified by the entries themselves on the heap
    * and not by their structure, so that a set of the pairs met costs a
    * lookup and no walk.
    */
  private final class EntryPair(val left: Entry[?, ?], val right: Entry[?, ?]):
    override def equals(other: Any): Boolean = other match
      case that: EntryPair => (left eq that.left) && (right eq that.right)
      case _               => false
    override def hashCode: Int =
      scala.util.hashing.MurmurHash3.mix(System.identityHashCode(left), System.identityHashCode(right))

  /** Whether every pending pair is of equal entries. A pair already met is
    * skipped: it is either pending still or was found equal, and in both
    * cases its first meeting decides it.
    */
  @scala.annotation.tailrec
  private def allEqual(pending: List[EntryPair], met: Set[EntryPair]): Boolean =
    pending match
      case Nil => true
      case pair :: rest =>
        val left = pair.left
        val right = pair.right
        if (left eq right) || met.contains(pair) then allEqual(rest, met)
        // FIXME (2026-11-14): `left.cost != right.cost` is the https://github.com/Atry/private-overlay/issues/1973
        // caller's equality. A ModuleCost compares its fold states by
        // structure, and some hold order terms (SpecializationState's
        // Map[OrderTerm, HoleUse] and rootHole, FilterState's absorbs). An
        // OrderTerm.Folded holds a child's state, which may hold order terms
        // over its own children's states, so one state can reach another
        // twice, and a case class's equality would then walk it as a tree.
        // Not measured: it runs only on a pair whose held hashes, shapes and
        // arities agree. The candidate fixes are a held hash with
        // graph-walking equality on OrderTerm, or the states' own.
        else if left.heldHash != right.heldHash || left.shape != right.shape ||
          left.childEntries.size != right.childEntries.size || left.cost != right.cost
        then false
        else allEqual(left.childEntries.lazyZip(right.childEntries).map(EntryPair(_, _)).toList ++ rest, met + pair)

  /** The hash of one entry: its shape's, the number of its child entries and
    * their held hash codes, in order.
    */
  private def entryHash(shape: Shape[?], childEntries: Vector[Entry[?, ?]]): Int =
    val mixed = childEntries.foldLeft(
      scala.util.hashing.MurmurHash3.mix(scala.util.hashing.MurmurHash3.mix(19, shape.##), childEntries.size)
    )((hash, child) => scala.util.hashing.MurmurHash3.mix(hash, child.heldHash))
    scala.util.hashing.MurmurHash3.finalizeHash(mixed, childEntries.size)

/** How an extraction ranks its entries: the cost of a production over the
  * costs of its children's entries, a function of the two only, the order
  * of costs, less better, and the reading of a cost. The extraction names no
  * lemma, combinator or module; what a cost holds is the caller's.
  *
  * THE CONTRACT (2026-11-12). The READING of a cost is the
  * part of it a parent's cost depends on beyond the order: two costs of one
  * reading stand for each other in every production up to their order: two
  * that tie give every parent one cost (`tiesAreIndistinguishable` of the
  * strategies' `CostMonotonicityLaws`). Readings are finitely many for a
  * graph, and a production's reading is a function of its children's
  * readings. Within one reading the cost is
  * monotone: for every production and every child position, replacing a
  * child's cost by one of the same reading that is not worse under
  * `ordering` gives a cost of the same reading that is not worse. At a
  * position the model prices over the children's readings
  * (`CostModel.pricedUnder`: what the shape prices, less what those
  * readings drop) it is strictly monotone:
  * replacing the child's cost by a strictly costlier one of the same
  * reading gives a strictly costlier cost. The
  * extraction keeps one best entry per class and reading, and a production
  * combines its children's entries of every reading
  * (`CountedExtraction`), which is exact under the contract; its last pass
  * reads a priced child by its class's entries at their least cost, which
  * strictness makes the only ones that keep the parent at its least (a
  * cost that saturates at a priced position gives a non-least kept entry,
  * measured on a generated model whose priced child counted min(cost, 0),
  * CountedExtractionLawTest). A cost model that is monotone across all its
  * costs has one reading, the default.
  */
trait CostModel[C <: NativeSpecializer & Singleton, Cost]:

  /** The cost of the production's shape over its children's costs, in the
    * order of `Shape.children`.
    */
  def cost(shape: Shape[C], childCosts: Vector[Cost]): Cost

  /** The order of costs, the lesser better. */
  def ordering: Ordering[Cost]

  /** The two costs have one reading. */
  def sameReading(left: Cost, right: Cost): Boolean = true

  /** The production's entries over the entries each child is read by, in
    * the order of `Shape.children`: for every reading some combination of
    * the options has, an entry of that reading whose cost is the best of
    * that reading among all the combinations, each entry's cost `cost` over
    * its child entries' costs. `CountedExtraction` keeps the best of each
    * reading among them. Every combination by default; a model whose
    * productions have many children of several readings finds the best of
    * each reading without listing the product
    * (`gezi.strategies.ThunkCandidates`).
    */
  def candidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]]): Vector[Entry[C, Cost]] =
    CostModel.combinations(options).map(entries => Entry(cost(shape, entries.map(_.cost)), shape, entries))

  /** Whether the production's cost reads each child's cost beyond its
    * reading, in the order of `Shape.children`: false where the cost is the
    * same whatever entry of a reading the child has, such as a parallel's
    * criterion. Every model states it (a model
    * that wrongly calls a child priced makes the extraction's last pass fail
    * to settle, and a default would say so silently).
    */
  def pricedChildren(shape: Shape[C]): Vector[Boolean]

  /** The children whose cost the production drops under these children's
    * readings, in the order of `Shape.children`: the cost reads only their
    * readings there, as at an unpriced position. A function of the
    * children's readings only, never of their costs within a reading, so
    * that replacing a child by another entry of its reading keeps the priced
    * positions, on which the least tree's settling in `CountedExtraction`
    * rests. Nothing by default.
    */
  def droppedChildren(shape: Shape[C], childCosts: Vector[Cost]): Vector[Boolean] = shape.children.map(_ => false)

  /** The children `droppedChildren` may drop under some readings: the
    * extraction's last pass offers their classes' least entries there as
    * well. Nothing by default.
    */
  def mayDropChildren(shape: Shape[C]): Vector[Boolean] = shape.children.map(_ => false)

  /** The children the model's `candidates` settle to their first entry by
    * size, then content, when each child is given as many entries as
    * `entryCounts` says, in the order of `Shape.children`, each of more than
    * one entry: those it lists jointly but, above a bound on the product of
    * their numbers of entries, does not enumerate, and those it gives their
    * first entry at any numbers, as a thunk's fillings its code does not read,
    * whose states a module's fold of the thunk may still read
    * (`gezi.strategies.ThunkCandidates`, `gezi.strategies.CodeFold.Closing`). A function of
    * the shape and the counts alone, and monotone in the counts: a child
    * settled at some numbers of entries is settled at any numbers at least
    * as large, position by position. A production some of whose children
    * may be dropped (`mayDropChildren`) settles none: the extraction's last
    * pass offers two lists of entries there, so the numbers its candidates
    * see are not its classes'. `CountedExtraction` reads it at the
    * numbers of entries its first run ends with, and runs its passes again
    * with such a production read once per combination of its children's
    * readings found in the trees that run kept, so that every pass settles
    * alike. None by default: a model that enumerates every combination
    * settles nothing, and its extraction runs once.
    */
  def settledChildren(shape: Shape[C], entryCounts: Vector[Int]): Vector[Boolean] = shape.children.map(_ => false)

  /** The production spells a repeller: a class that holds an application of
    * a class with such a production has no entry, and no production reads
    * through it (`Extraction.productions` over the model). A model reads it
    * off a combinator property of the library term the production names,
    * never off a type. None by default.
    */
  def repeller(shape: Shape[C]): Boolean = false

  /** The domain's class an entry of this cost checks its next argument by
    * when its spelling is a contract, or a contract applied to some of its
    * arguments (`gezi.ir.DispatchPattern.contractChecks`), so that a call
    * whose argument's filter by that domain is repelled reads the function
    * by its other entries (`Production.repelledDomains`); none by default. A
    * model that gives domains keeps a contract's entries apart from the
    * class's other entries in its readings (`sameReading`).
    */
  def contractDomain(cost: Cost): Option[Int] = None

  /** The production's entries over the entries each child is read by: for
    * every reading some combination of the options has, the combination of
    * that reading that is least by `ContentOrder`, whatever its cost.
    * Every combination by default, the least of each reading kept; a model
    * whose productions have many children of several readings finds them
    * without listing the product (`gezi.strategies.ThunkCandidates`).
    */
  def leastCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]]): Vector[Entry[C, Cost]] =
    CostModel.leastOfEachReading(
      this,
      CostModel.combinations(options).map(entries => Entry(cost(shape, entries.map(_.cost)), shape, entries))
    )

  /** What the model remembers from one call of `memoizedCandidates` or
    * `memoizedLeastCandidates` to the next within one extraction: a value
    * the extraction hands back with each call and drops when it ends
    * (`CountedExtraction.fixed`), never kept beyond it. A memo holds the
    * results of a pure function of the shape and the options, so that
    * dropping it changes cost only: a call gives the candidates `candidates`
    * or `leastCandidates` give, whatever memo it is handed. Its keys hold
    * every input the result depends on, the shape, every option and which of
    * the two calls it is; and a result cut short because a stop was
    * requested (a model that reads the stop signal, `ThunkCandidates` under
    * `ModuleCostModel.stop`, gives the candidates found so far) is never
    * remembered, since it is no value of that function.
    */
  type Memo

  /** The memo an extraction starts from. */
  def emptyMemo: Memo

  /** `candidates`, given the memo so far, with the memo after the call. */
  def memoizedCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Memo): (Vector[Entry[C, Cost]], Memo)

  /** `leastCandidates`, given the memo so far, with the memo after the
    * call.
    */
  def memoizedLeastCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Memo): (Vector[Entry[C, Cost]], Memo)

/** A cost model that remembers nothing between calls: its memo is `Unit`,
  * and its memoized calls are `candidates` and `leastCandidates`.
  */
trait StatelessCostModel[C <: NativeSpecializer & Singleton, Cost] extends CostModel[C, Cost]:
  final type Memo = Unit
  final def emptyMemo: Unit = ()
  final def memoizedCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Unit): (Vector[Entry[C, Cost]], Unit) =
    (candidates(shape, options), memo)
  final def memoizedLeastCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Unit): (Vector[Entry[C, Cost]], Unit) =
    (leastCandidates(shape, options), memo)

object CostModel:

  /** The positions the production prices over these children's costs: those
    * its shape prices (`pricedChildren`) and these children's readings do
    * not drop (`droppedChildren`).
    */
  def pricedUnder[C <: NativeSpecializer & Singleton, Cost](model: CostModel[C, Cost], shape: Shape[C], childCosts: Vector[Cost]): Vector[Boolean] =
    // A production none of whose children its readings may drop is priced
    // as its shape says, its children's readings not read: the cost reads
    // priced positions on every call.
    if !model.mayDropChildren(shape).contains(true) then model.pricedChildren(shape)
    else model.pricedChildren(shape).zip(model.droppedChildren(shape, childCosts)).map((priced, dropped) => priced && !dropped)

  /** The entries least by `ContentOrder` of each reading, in the order the
    * readings first occur.
    */
  def leastOfEachReading[C <: NativeSpecializer & Singleton, Cost](model: CostModel[C, Cost], entries: Vector[Entry[C, Cost]]): Vector[Entry[C, Cost]] =
    entries.foldLeft(Vector.empty[Entry[C, Cost]]) { (kept, entry) =>
      kept.indexWhere(other => model.sameReading(other.cost, entry.cost)) match
        case -1 => kept :+ entry
        case position =>
          if ContentOrder.compare(entry, kept(position)) < 0 then kept.updated(position, entry) else kept
    }

  /** Every choice of one option at each position, in order. */
  def combinations[Value](options: Vector[Vector[Value]]): Vector[Vector[Value]] =
    lazyCombinations(options).toVector

  /** Every choice of one option at each position, in order, drawn on
    * demand: an element is built only when it is asked for, so a reader
    * that stops asking stops the construction (`ThunkCandidates`).
    */
  def lazyCombinations[Value](options: Vector[Vector[Value]]): LazyList[Vector[Value]] =
    options.foldLeft(LazyList(Vector.empty[Value]))((partial, choices) =>
      for
        chosen <- partial
        choice <- choices
      yield chosen :+ choice
    )

/** The extraction data of one class: its best entry of each reading, its
  * best entry of each reading among the productions that do not read the
  * class, each list by cost and then content (`ContentOrder`); the best
  * of each list over all readings, by cost and then content
  * (`ContentOrder`); and the numbers of the productions that read the class,
  * in order.
  */
final case class ClassEntries[C <: NativeSpecializer & Singleton, Cost](
    entries: Vector[Entry[C, Cost]],
    looplessEntries: Vector[Entry[C, Cost]],
    best: Option[Entry[C, Cost]],
    bestLoopless: Option[Entry[C, Cost]],
    readers: Vector[Int]
)

object ClassEntries:

  /** The data of a class with no entry yet. */
  def unentered[C <: NativeSpecializer & Singleton, Cost](readers: Vector[Int]): ClassEntries[C, Cost] =
    ClassEntries(Vector.empty, Vector.empty, None, None, readers)

/** The fixed point of an extraction: the entries of every class that has
  * one, by the root of the class, and the cost model whose readings the
  * entries are kept by.
  */
final case class Extracted[C <: NativeSpecializer & Singleton, Cost](classes: Map[Int, ClassEntries[C, Cost]], model: CostModel[C, Cost]):

  /** The class's final entry of the entry's reading, of a production that
    * does not read the class when `loopless`. Throws
    * `IllegalArgumentException` when the class has none: a class keeps an
    * entry of every reading it was ever entered with.
    */
  def entryOfReading(root: Int, entry: Entry[C, Cost], loopless: Boolean): Entry[C, Cost] =
    val kept = classes.get(root).map(entries => if loopless then entries.looplessEntries else entries.entries)
    kept
      .flatMap(_.find(candidate => model.sameReading(candidate.cost, entry.cost)))
      .getOrElse(throw IllegalArgumentException(s"the class $root has no entry of the reading of ${entry.cost}"))

  /** The class has a best entry. */
  def hasEntry(root: Int): Boolean = classes.get(root).exists(_.best.isDefined)

  /** The best entry of the class. Throws `IllegalArgumentException` for a
    * class with none.
    */
  def best(root: Int): Entry[C, Cost] =
    classes
      .get(root)
      .flatMap(_.best)
      .getOrElse(throw IllegalArgumentException(s"the class $root has no entry"))

/** The spellings of an extraction, the memo of the classes spelled, each
  * with the position of the class's entry of the reading spelled, and the
  * caller's accumulator, threaded through the spelling of several roots.
  */
final case class Spelled[Spelling, Accumulator](
    accumulator: Accumulator,
    kept: Map[(Int, Int), Spelling]
)

/** The extraction of the Prolog baseline's search strategy
  * (`lambda_jit_baseline_fixpoint_search`, THE EXTRACTION): the best entry of
  * each class by a cost model, read greedily to its fixed point.
  *
  * The PRODUCTIONS of a class are its live nodes, each over the classes of
  * its children, but the absorbed choices (`absorbedChoice`), then the names
  * given whose node is live, in the order the graph filed the instructions. An
  * entry of a production reads each child by its class's best entry, and the
  * class itself, wherever a production of the class reads it, by its best
  * entry of a production that does not read it. A class keeps the entry of
  * the least cost, among equal ones the first in the order of content
  * (`ContentOrder`), and its best entry of a
  * production that does not read it the same way; a production is read
  * again when a class it reads gains a better entry of either kind. The
  * productions waiting to be read are read in the order of the costs of
  * their own classes' best entries, the least first and a class with no
  * entry before any, off a pairing heap with the order of SWI-Prolog's
  * (`PairingHeap`). The fixed point is a greedy one and depends on that
  * order.
  */
object Extraction:

  /** The productions of the graph, the names given, and the readers of each
    * class: the productions with it as a child, in order, a production with
    * a class as two children listed twice. No class is repelled.
    */
  def productions[C <: NativeSpecializer & Singleton](graph: EGraph[C], names: Set[Configured[C]])(using C): (Vector[Production[C]], Map[Int, Vector[Int]]) =
    productionsOutside(graph, names, _ => Set.empty)

  /** The productions of the graph and the names given, as `productions`
    * lists them, but none of a class the model repels
    * (`repelledClasses`), and the readers of each class. A repelled class
    * also reads as no layer to the dispatch patterns
    * (`choiceOperandReadings`), so that no specialization or judgment is
    * read through it: such a pattern reads the classes of its parts' layers,
    * a typed member's filter among them, which are not its children. So the
    * class has no entry, nor has any production that reads it as a child or
    * through a pattern.
    */
  def productions[C <: NativeSpecializer & Singleton](graph: EGraph[C], names: Set[Configured[C]], model: CostModel[C, ?])(using C): (Vector[Production[C]], Map[Int, Vector[Int]]) =
    productionsOutside(graph, names, shapes => repelledClasses(model, shapes))

  /** The classes the model repels: each that holds an application whose
    * function's class holds a repeller (`CostModel.repeller`), among the
    * live nodes and names read, each with the root of its class.
    */
  private def repelledClasses[C <: NativeSpecializer & Singleton](model: CostModel[C, ?], shapes: Vector[(Int, Shape[C])]): Set[Int] =
    val repellers = shapes.collect { case (root, shape) if model.repeller(shape) => root }.toSet
    if repellers.isEmpty then Set.empty
    else shapes.collect { case (root, Shape.Node(_, Apply(function, _))) if repellers.contains(function) => root }.toSet

  /** The productions of `productions`, none of a class in the set `repelled`
    * gives over the live nodes and the names, each with the root of its
    * class.
    */
  private def productionsOutside[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      names: Set[Configured[C]],
      repelled: Vector[(Int, Shape[C])] => Set[Int]
  )(using C): (Vector[Production[C]], Map[Int, Vector[Int]]) =
    // A storage leaf's pattern view (`EGraph.patternViews`) is no production:
    // its class always holds the leaf, and it spells the leaf filtered again.
    val liveNodes = graph.liveNodes.filterNot(live => graph.patternViews.contains(live.node))
    // Each class a choice could be absorbed by is read once, so that the
    // filter costs the graph's size, not the choices times their classes.
    val absorbingParallels = liveNodes
      .flatMap(live => absorbingOperand(live.root, live.layer))
      .distinct
      .map(other => other -> parallelOperands(graph, other))
      .toMap
    val liveRead = liveNodes.filterNot(live =>
      absorbingOperand(live.root, live.layer).exists(other => absorbingParallels(other).contains(live.root))
    )
    val namesRead = graph.instructionFilings.collect {
      case (instruction, node) if names.contains(instruction) && graph.live(node) =>
        (graph.root(node), Shape.Name(instruction))
    }
    val repelledRoots = repelled(liveRead.map(live => (live.root, Shape.Node(live.node, live.layer))) ++ namesRead)
    val readNodes = liveRead.filterNot(live => repelledRoots.contains(live.root))
    val readings = choiceOperandReadings(graph, readNodes.map(_.layer), repelledRoots)
    val nodeShapes = readNodes
      .flatMap(live => (Shape.Node(live.node, live.layer) +: dispatchShapes(live.node, live.layer, readings)).map((live.root, _)))
    val nameShapes = namesRead.filterNot((root, _) => repelledRoots.contains(root))
    // The filters a repelled class holds, each value with the criteria it is
    // filtered by there.
    val repelledFilters = liveRead
      .collect { case live if repelledRoots.contains(live.root) => live.layer }
      .collect { case Parallel(value, criterion) => (value, criterion) }
      .groupMap(_._1)(_._2)
      .view
      .mapValues(_.toSet)
      .toMap
    val listed = (nodeShapes ++ nameShapes).zipWithIndex.map { case ((root, shape), number) =>
      shape match
        case Shape.Node(_, Apply(_, argument)) =>
          Production(number, root, shape, repelledFilters.getOrElse(argument, Set.empty))
        // A specialization's function is its first child too, applied to
        // its argument in both members.
        case Shape.Specialized(_, specialization) =>
          Production(number, root, shape, repelledFilters.getOrElse(specialization.argument, Set.empty))
        case _ => Production(number, root, shape)
    }
    val readers = listed.foldLeft(Map.empty[Int, Vector[Int]]) { (filed, production) =>
      production.shape.children.foldLeft(filed)((current, child) =>
        current.updated(child, current.getOrElse(child, Vector.empty) :+ production.number)
      )
    }
    (listed, readers)

  /** The dispatch patterns a live choice node is read as, each a production
    * of the node's class beside the node's own: its specialization choices
    * and then its judgments (`DispatchPattern`), a class read as the layers
    * of its live members (`choiceOperandReadings`).
    */
  def dispatchShapes[C <: NativeSpecializer & Singleton](
      node: Int,
      layer: LayerWith[Int, Configured[C]],
      readings: Int => DispatchPattern.Reading[Int]
  ): Vector[Shape[C]] = layer match
    case Choice(left, right) =>
      val (leftReading, rightReading) = (readings(left), readings(right))
      DispatchPattern
        .specializationsRead(leftReading, rightReading)
        .map(Shape.Specialized(node, _)) ++
        DispatchPattern.fallbacksRead(left, right, leftReading, rightReading).map(Shape.Judged(node, _))
    case _ => Vector.empty

  /** The dispatch patterns' reading (`DispatchPattern.reading`) of each
    * operand of the choices among the layers, the only classes
    * `dispatchShapes` looks up, over the layers of its live members over the
    * roots in `EGraph.classMembers`' order, no class read as a contract: a
    * value built once by each call of `productions` and passed to all the
    * dispatch patterns, no cache kept across calls. `classMembers` builds a
    * class afresh on each call, which the recognition had made once per
    * member of the other class of a choice (measured 2026-11-13,
    * programfamilies' folds at 256: 606,815 class readings building
    * 146,581,966 members, against 3,061 readings of 6,732 members read
    * once).
    *
    * A reading looks up, besides the operand's own layers, the layers of the
    * application under each of its parallels and the layers of the argument
    * of each application among the operand's layers and those applications'
    * (`DispatchPattern.typedApplications` with no contract, then the
    * argument's parallels): the layers of these classes are read once each
    * and dropped when the readings are built. Reading every class of the
    * live nodes instead held a reading of each class of the graph while the
    * productions were built, which ran out of a 352m heap on programfamilies'
    * list at 1024 (curried-partial-function, 2026-11-13, CriterionFourTest).
    * A class looked up may have no live member, its nodes all duplicates
    * whose union with their twins' classes waits on the agenda
    * (`AnalysisSlot.computed`), and is read as no layer, as `classMembers`
    * reads it; so is a class in `repelled`.
    */
  private def choiceOperandReadings[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      readLayers: Vector[LayerWith[Int, Configured[C]]],
      repelled: Set[Int]
  ): Map[Int, DispatchPattern.Reading[Int]] =
    def layersOf(roots: Vector[Int], known: Map[Int, Vector[LayerWith[Int, Configured[C]]]]): Map[Int, Vector[LayerWith[Int, Configured[C]]]] =
      roots.distinct
        .filterNot(known.contains)
        .foldLeft(known)((read, root) =>
          read.updated(root, if repelled.contains(root) then Vector.empty else graph.classMembers(root).map(_.layer))
        )
    val operands = readLayers.flatMap {
      case Choice(left, right) => Vector(left, right)
      case _                         => Vector.empty
    }.distinct
    val operandLayers = layersOf(operands, Map.empty)
    val applications = operands.flatMap(operand => operandLayers(operand).collect { case Parallel(application, _) => application })
    val withApplications = layersOf(applications, operandLayers)
    val arguments = (operands ++ applications).flatMap(root => withApplications(root).collect { case Apply(_, argument) => argument })
    val layers = layersOf(arguments, withApplications)
    val parallels = DispatchPattern.parallelLayers(layers)
    operands.map(operand => operand -> DispatchPattern.reading(operand, layers, parallels, DispatchPattern.noContract)).toMap

  /** The layer is a choice of the class itself and a class that holds a
    * parallel over the class, `s + (s ∥ t)` in either order, which is `s` by
    * absorption (law (6)): the class has `s`'s other productions to spell it
    * by. Read as a production, its member `s` by the class's best entry of a
    * production that does not read it and its parallel's operand by the
    * class's best entry, it could be better than every entry of `s`, and its
    * two members spelled no longer one `s` (the baseline's
    * `absorbed_choice/3`).
    */
  def absorbedChoice[C <: NativeSpecializer & Singleton](graph: EGraph[C], root: Int, layer: LayerWith[Int, Configured[C]]): Boolean =
    absorbingOperand(root, layer).exists(other => parallelOperands(graph, other).contains(root))

  /** The other member of a choice of the class `root` with the class itself,
    * the class that could absorb it, none for any other layer.
    */
  private def absorbingOperand[C <: NativeSpecializer & Singleton](root: Int, layer: LayerWith[Int, Configured[C]]): Option[Int] = layer match
    case Choice(first, second) => if first == root then Some(second) else if second == root then Some(first) else None
    case _                     => None

  /** The roots of the classes `s` the class holds a parallel `s ∥ t` over:
    * its parallel members' left operands, read from its parallels alone.
    */
  private def parallelOperands[C <: NativeSpecializer & Singleton](graph: EGraph[C], node: Int): Set[Int] =
    graph
      .members(graph.root(node), MemberShape.Parallel)
      .map(member => graph.layer(member))
      .collect { case Parallel(left, _) => graph.root(left) }
      .toSet

  // TODO: the fixed
  // point of the extraction is computed by `CountedExtraction.fixed`, a
  // module moved into this project (extraction/src/main/scala/gezi/extraction/CountedExtraction.scala).
  // The retired `Extraction.fixed` and its helpers (`Work`, `keyOrdering`,
  // `worked`, `readerPushed`, `productionEntered`) read back with
  // `git show c33817721:lambda_jit/extraction/src/main/scala/lambdajit/extraction/Extraction.scala`.

  /** The spelling of the class by its best entry, each class it reads by its
    * own final entry of the reading the reading entry's child entry has, in
    * turn, each class and reading once (`class_spelled/4`): a member of a
    * choice that is the class itself is spelled by the class's final entry of
    * that reading among the productions that do not read it, and a class and
    * reading read again while they are being spelled by the child entry the
    * entry names, over its children's spellings (`entry_freshened/4`). So
    * every entry spelled outside a loop is its class's final entry of its
    * reading, however late the class's entry of that reading improved.
    * `spell` makes the spelling of a shape over its children's spellings, in
    * the order of `Shape.children`, threading the accumulator. The memo of
    * the classes and readings spelled is kept across the roots spelled with
    * one `Spelled`. Throws `IllegalArgumentException` for a class with no
    * entry.
    */
  def spelled[C <: NativeSpecializer & Singleton, Cost, Spelling, Accumulator](
      extracted: Extracted[C, Cost],
      root: Int,
      state: Spelled[Spelling, Accumulator]
  )(spell: (Accumulator, Shape[C], Vector[Spelling]) => (Accumulator, Spelling)): (Spelled[Spelling, Accumulator], Spelling) =
    require(extracted.hasEntry(root), s"the class $root has no entry")
    Speller(extracted, spell).classSpelled(root, extracted.best(root), Set.empty, state).result

  /** The walks of one spelling, trampolined: a spelling is as deep as the
    * term it spells.
    */
  private final case class Speller[C <: NativeSpecializer & Singleton, Cost, Spelled0, Accumulator](
      extracted: Extracted[C, Cost],
      spell: (Accumulator, Shape[C], Vector[Spelled0]) => (Accumulator, Spelled0)
  ):
    type State = Spelled[Spelled0, Accumulator]

    /** The class and the position of its final entry of the reading of the
      * entry given, the key of the memo and of the stack.
      */
    private def readingKey(classId: Int, entry: Entry[C, Cost]): (Int, Int) =
      val finalEntry = extracted.entryOfReading(classId, entry, loopless = false)
      (classId, extracted.classes(classId).entries.indexWhere(_ eq finalEntry))

    def classSpelled(classId: Int, reading: Entry[C, Cost], stack: Set[(Int, Int)], state: State): TailRec[(State, Spelled0)] =
      val key = readingKey(classId, reading)
      state.kept.get(key) match
        case Some(kept) => done((state, kept))
        case None =>
          val finalEntry = extracted.entryOfReading(classId, reading, loopless = false)
          tailcall(entryRespelled(finalEntry, classId, stack + key, state)).map {
            case (after, spelling) => (after.copy(kept = after.kept.updated(key, spelling)), spelling)
          }

    def entryRespelled(
        entry: Entry[C, Cost],
        classId: Int,
        stack: Set[(Int, Int)],
        state: State
    ): TailRec[(State, Spelled0)] =
      childrenSpelled(entry, state)((child, childEntry, current) =>
        if child == classId then
          tailcall(entryRespelled(extracted.entryOfReading(classId, childEntry, loopless = true), classId, stack, current))
        else if stack.contains(readingKey(child, childEntry)) then tailcall(entryFreshened(childEntry, stack, current))
        else tailcall(classSpelled(child, childEntry, stack, current))
      )

    def entryFreshened(entry: Entry[C, Cost], stack: Set[(Int, Int)], state: State): TailRec[(State, Spelled0)] =
      childrenSpelled(entry, state)((child, childEntry, current) =>
        if stack.contains(readingKey(child, childEntry)) then tailcall(entryFreshened(childEntry, stack, current))
        else tailcall(classSpelled(child, childEntry, stack, current))
      )

    /** The entry's shape spelled over its children, each spelled by
      * `child` from its class and the child entry the entry names.
      */
    private def childrenSpelled(entry: Entry[C, Cost], state: State)(
        child: (Int, Entry[C, Cost], State) => TailRec[(State, Spelled0)]
    ): TailRec[(State, Spelled0)] =
      val pairs = entry.shape.children.zip(entry.childEntries).toList
      def loop(rest: List[(Int, Entry[C, Cost])], current: State, spellings: Vector[Spelled0]): TailRec[(State, Spelled0)] =
        rest match
          case Nil =>
            val (accumulator, spelling) = spell(current.accumulator, entry.shape, spellings)
            done((current.copy(accumulator = accumulator), spelling))
          case (childClass, childEntry) :: others =>
            child(childClass, childEntry, current).flatMap { case (after, spelling) =>
              tailcall(loop(others, after, spellings :+ spelling))
            }
      loop(pairs, state, Vector.empty)
