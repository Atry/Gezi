package com.yang_bo.gezi.egraph

import com.yang_bo.gezi.ir.LayerWith
import scala.annotation.tailrec
import scala.collection.immutable.HashMap
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** An analysis of the classes of an e-graph: each class holds one value, the
  * join of the values of its live nodes, a node's value made from its layer
  * over its children's class values. A strategy, a cost model or a rule reads
  * it as a hint; it never merges, prunes, adds a node or orders the agenda
  * itself.
  *
  * What a value may be: a cost, values of a cost function joined by its order,
  * such as size, depth or the counted cost of the cheapest spelling; or a
  * cached, recursively computed pure function of the class's member nodes, such
  * as which native storages the class holds as leaves (`StorageLeafAnalysis`).
  * `made` may read the node's own layer, a leaf's instruction included, and
  * data the analysis was built with (`combinator_property` facts, backend
  * facts). What it may not be (`CONTRIBUTING.md`, "Types live only in the
  * term"): a verdict, a value that chooses a filter, decides whether a value is
  * of a type, or stands as the proof of a merge. Every merge is the instance of
  * a lemma or a rule, proved as such, whatever an analysis says.
  *
  * The laws an analysis keeps, which make the incremental values equal to the
  * least fixed point computed from scratch (`AnalysisSlot.computed`) whenever
  * the agenda is empty, as it is whenever a saturation ends (while a union of
  * congruence waits, a class may still hold the cost of a node marked a
  * duplicate, which the from-scratch values leave out): `joined` is
  * commutative, associative and idempotent with `identity` its unit; `made` is
  * monotone in each child's cost under `joined`'s order; and the order has no
  * infinite descending chain (the naturals under min), so that repair ends.
  */
trait ClassAnalysis[C <: NativeSpecializer & Singleton, Value]:

  /** The analysis's own key into a graph's slots: one object for each analysis,
    * carrying the type of its values, so that a read through it
    * (`EGraph.analysisValue`) is typed by the key, not by a cast of the
    * caller's.
    */
  final val key: AnalysisKey[Value] = AnalysisKey[Value]()

  /** The unit of `joined`: the cost of a class with no node priced yet. */
  def identity: Value

  /** The cost of one node: its layer over its children's class costs, a leaf
    * the term of the configuration `C` the analysis is of, whose specializer an
    * analysis that reads a storage's criterion holds.
    */
  def made(layer: LayerWith[Value, Configured[C]]): Value

  /** The cost of a class holding both costs' nodes. */
  def joined(left: Value, right: Value): Value

/** The key of one analysis in the slots of a graph, made by [[ClassAnalysis]]
  * alone: it carries the type of the values the analysis gives, so that two
  * keys that are one object have one value type.
  */
final class AnalysisKey[Value] private[egraph] ():

  /** The evidence that the other key's value type is this key's, when the two
    * are one object (the one analysis).
    */
  def sameAs[Other](other: AnalysisKey[Other]): Option[Value =:= Other] =
    // Registered conversion (issue 2261, section 8): the key is the analysis's own and carries its value type, so one
    // key object has one value type, whatever name a caller gives the type it asks for.
    Option.when(this eq other)(
      summon[Value =:= Value].asInstanceOf[Value =:= Other]
    )

/** The cost of each class of a graph under one analysis, by the class's root,
  * one slot of the product the graph keeps (`EGraph.analyses`), updated by its
  * operations: a new node's class gets the node's cost, a union joins the two
  * classes' costs, and a class whose cost changes has its users priced again
  * until nothing changes (the repair of egg's e-class analyses).
  */
final case class AnalysisSlot[C <: NativeSpecializer & Singleton, Value](
    analysis: ClassAnalysis[C, Value],
    values: HashMap[Int, Value]
):

  /** The cost of the class of the root, when this slot holds the analysis of
    * the key given. The key is the analysis's own (`ClassAnalysis.key`), and
    * its type is the type of the values, so the slot returns its values only to
    * the caller holding the key of the analysis it holds.
    */
  def valueOf[Wanted](wanted: AnalysisKey[Wanted], root: Int): Option[Wanted] =
    analysis.key
      .sameAs(wanted)
      .flatMap(sameType => values.get(root).map(sameType))

  /** The slot with the new node's class priced: the node is its own root. */
  private[egraph] def nodeMade(
      graph: EGraph[C],
      node: Int
  ): AnalysisSlot[C, Value] =
    copy(values = values.updated(node, nodeCost(graph, node)))

  /** The slot after the union that made `big` the root of `small`'s class, the
    * users of the joined class priced again when its cost differs from either
    * class's before.
    */
  private[egraph] def classesJoined(
      graph: EGraph[C],
      small: Int,
      big: Int
  ): AnalysisSlot[C, Value] =
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
  private def repaired(
      graph: EGraph[C],
      users: List[Int]
  ): AnalysisSlot[C, Value] = users match
    case Nil          => this
    case user :: rest =>
      val userRoot = graph.root(user)
      val before = values(userRoot)
      val after = analysis.joined(before, nodeCost(graph, user))
      if after == before then repaired(graph, rest)
      else
        copy(values = values.updated(userRoot, after))
          .repaired(graph, graph.classUsers(userRoot).toList ::: rest)

  /** The node's cost over its children's classes' current costs. */
  private def nodeCost(graph: EGraph[C], node: Int): Value =
    // An analysis's values are no terms: a layer over them is no term either.
    analysis.made(
      graph
        .layer(node)
        .map(child => values(graph.root(child)))(using com.yang_bo.gezi.ir.NotTerm.granted)
    )

object AnalysisSlot:

  /** The slot of the analysis on the graph computed from scratch: every class
    * starts at the analysis's identity, and each live node's cost is joined
    * into its class's until nothing changes, the least fixed point. A class
    * whose nodes are all duplicates, its union with their twins' classes
    * waiting on the agenda, keeps the identity.
    */
  def computed[C <: NativeSpecializer & Singleton, Value](
      graph: EGraph[C],
      analysis: ClassAnalysis[C, Value]
  ): AnalysisSlot[C, Value] =
    val live = graph.liveNodes
    val start = HashMap.from(
      graph.nodes.indices.map(node => graph.root(node) -> analysis.identity)
    )
    AnalysisSlot(analysis, settled(graph, live, analysis, start))

  @tailrec
  private def settled[C <: NativeSpecializer & Singleton, Value](
      graph: EGraph[C],
      live: Vector[LiveNode[C]],
      analysis: ClassAnalysis[C, Value],
      values: HashMap[Int, Value]
  ): HashMap[Int, Value] =
    val next = live.foldLeft(values)((current, node) =>
      val cost = analysis.made(
        node.layer.map(child => current(graph.root(child)))(using
          com.yang_bo.gezi.ir.NotTerm.granted
        )
      )
      current.updated(node.root, analysis.joined(current(node.root), cost))
    )
    if next == values then values else settled(graph, live, analysis, next)
