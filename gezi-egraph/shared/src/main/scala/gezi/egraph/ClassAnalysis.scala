package gezi.egraph

import gezi.ir.Layer
import scala.annotation.tailrec
import scala.collection.immutable.HashMap

/** A cost analysis of the classes of an e-graph: each class holds one cost, the join of the costs of its live nodes,
  * a node's cost made from its layer over its children's class costs. A
  * strategy or a cost model reads it; it never merges, prunes, adds a node
  * or orders the agenda.
  *
  * What a cost may be: values of a cost function joined by its order, such
  * as size, depth or the counted cost of the cheapest spelling; `made` may
  * read the node's own layer, a leaf's instruction included, and data the
  * analysis was built with (`combinator_property` facts, backend facts) to
  * price that one node. What it may not be
  * (`CONTRIBUTING.md`, "Types live only in the term"): a value that says a class holds an assertion, a filter, or a
  * define with a type-ness property. A class's value depends on which
  * lemma instances merged the class, so a joined fact about the class's
  * nodes is a record about the class kept beside the term, not a function
  * of a term's syntax; only its cost may be stored.
  *
  * The laws a cost analysis keeps, which make the incremental values equal
  * to the least fixed point computed from scratch (`AnalysisSlot.computed`)
  * whenever the agenda is empty, as it is whenever a saturation ends (while
  * a union of congruence waits, a class may still hold the cost of a node
  * marked a duplicate, which the from-scratch values leave out):
  * `joined` is commutative, associative and idempotent with `identity` its
  * unit; `made` is monotone in each child's cost under `joined`'s order; and
  * the order has no infinite descending chain (the naturals under min), so
  * that repair ends.
  */
trait ClassAnalysis[Value]:

  /** The unit of `joined`: the cost of a class with no node priced yet. */
  def identity: Value

  /** The cost of one node: its layer over its children's class costs. */
  def made(layer: Layer[Value]): Value

  /** The cost of a class holding both costs' nodes. */
  def joined(left: Value, right: Value): Value

/** The cost of each class of a graph under one analysis, by the class's
  * root, kept in the graph (`EGraph.analysis`) and updated by its
  * operations: a new node's class gets the node's cost, a union joins the
  * two classes' costs, and a class whose cost changes has its users priced
  * again until nothing changes (the repair of egg's e-class analyses).
  */
final case class AnalysisSlot[Value](analysis: ClassAnalysis[Value], values: HashMap[Int, Value]):

  /** The cost of the class of the root, when this slot holds the analysis
    * given. The analysis is the key: the slot returns its values only to
    * the caller holding the same analysis object, so the cast below gives
    * back the type that object was built with.
    */
  def valueOf[Wanted](wanted: ClassAnalysis[Wanted], root: Int): Option[Wanted] =
    if wanted eq analysis then values.get(root).map(_.asInstanceOf[Wanted]) else None

  /** The slot with the new node's class priced: the node is its own root. */
  private[egraph] def nodeMade(graph: EGraph, node: Int): AnalysisSlot[Value] =
    copy(values = values.updated(node, nodeCost(graph, node)))

  /** The slot after the union that made `big` the root of `small`'s class,
    * the users of the joined class priced again when its cost differs from
    * either class's before.
    */
  private[egraph] def classesJoined(graph: EGraph, small: Int, big: Int): AnalysisSlot[Value] =
    val smallValue = values(small)
    val bigValue = values(big)
    val joinedValue = analysis.joined(bigValue, smallValue)
    val updated = copy(values = values.removed(small).updated(big, joinedValue))
    if joinedValue == bigValue && joinedValue == smallValue then updated
    else updated.repaired(graph, graph.classUsers(big).toList)

  /** The users priced again, the latest first, a user whose class's cost
    * changes adding its class's users.
    */
  @tailrec
  private def repaired(graph: EGraph, users: List[Int]): AnalysisSlot[Value] = users match
    case Nil => this
    case user :: rest =>
      val userRoot = graph.root(user)
      val before = values(userRoot)
      val after = analysis.joined(before, nodeCost(graph, user))
      if after == before then repaired(graph, rest)
      else copy(values = values.updated(userRoot, after)).repaired(graph, graph.classUsers(userRoot).toList ::: rest)

  /** The node's cost over its children's classes' current costs. */
  private def nodeCost(graph: EGraph, node: Int): Value =
    analysis.made(graph.layer(node).map(child => values(graph.root(child))))

object AnalysisSlot:

  /** The slot of the analysis on the graph computed from scratch: every
    * class starts at the analysis's identity, and each live node's cost is
    * joined into its class's until nothing changes, the least fixed point.
    * A class whose nodes are all duplicates, its union with their twins'
    * classes waiting on the agenda, keeps the identity.
    */
  def computed[Value](graph: EGraph, analysis: ClassAnalysis[Value]): AnalysisSlot[Value] =
    val live = graph.liveNodes
    val start = HashMap.from(graph.nodes.indices.map(node => graph.root(node) -> analysis.identity))
    AnalysisSlot(analysis, settled(graph, live, analysis, start))

  @tailrec
  private def settled[Value](
      graph: EGraph,
      live: Vector[LiveNode],
      analysis: ClassAnalysis[Value],
      values: HashMap[Int, Value]
  ): HashMap[Int, Value] =
    val next = live.foldLeft(values)((current, node) =>
      val cost = analysis.made(node.layer.map(child => current(graph.root(child))))
      current.updated(node.root, analysis.joined(current(node.root), cost))
    )
    if next == values then values else settled(graph, live, analysis, next)
