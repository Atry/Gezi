package gezi.weakhead

import gezi.frontend.Term
import gezi.frontend.Term.*

/** The shape of a graph of the family. */
enum GraphShape:

  /** Two rings of the size each: ring A from the start, ring B holding the
    * target at its last node; A's last node goes first back to A's first, then
    * over to B's first.
    */
  case TwoRings

  /** A ring of the size with chords: node i goes first back to node i - 1 (node
    * 0 has no chord), then on to node i + 1, and the last node back to node 0;
    * the target is the last node.
    */
  case ChordRing

/** A graph: its node count, its edges in order, its start and its target. */
final case class Graph(
    count: Int,
    edges: Vector[(Int, Int)],
    start: Int,
    target: Int
)

/** The generator and the reference of graph reachability in lambda plus choice,
  * the port of the pieces of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_graph.pl`) that `weak_head.plt`
  * reads (`graph/6`, `graph_term/5`, `reference_reachable/4`), written with the
  * front end's HOAS; the module `corpora` ports the whole family.
  *
  * THE PROGRAM. Node i is the Scott unary numeral i, let bound once as the
  * successor of node i - 1. A table over the nodes is a nested case on the
  * numeral, `v C0 (\p. p C1 (\p. ...))`, top beyond the last case. reach(v) is
  * the choice `is_target v + successors v`, where the case of node i in
  * successors is the choice of reach applied to each successor of node i, in
  * the edges' order, and in is_target the Church boolean, true at the target;
  * reach is recursive by self-application, and the program is the Church
  * boolean of reach(start). The edge back into a cycle comes before the edge
  * that leaves it, so a reading that tries the first member first, and never
  * gives it up, runs around the cycle forever.
  */
object MergeGraph:

  /** The graph of the shape and the size. */
  def graph(shape: GraphShape, size: Int): Graph = shape match
    case GraphShape.TwoRings =>
      val count = 2 * size
      Graph(
        count,
        ringEdges(0, size - 1) ++ Vector((size - 1, size)) ++ ringEdges(
          size,
          count - 1
        ),
        0,
        count - 1
      )
    case GraphShape.ChordRing =>
      Graph(size, chordEdges(0, size - 1), 0, size - 1)

  /** First -> First + 1 -> ... -> Last, and Last back to First. */
  private def ringEdges(first: Int, last: Int): Vector[(Int, Int)] =
    (first until last).toVector.map(node => (node, node + 1)) :+ ((last, first))

  /** Each node first back to the one before it (not node 0), then on to the
    * next, and the last back to 0.
    */
  private def chordEdges(first: Int, last: Int): Vector[(Int, Int)] =
    (first to last).toVector.flatMap(node =>
      (if node > 0 then Vector((node, node - 1)) else Vector.empty) ++
        (if node == last then Vector((last, 0)) else Vector((node, node + 1)))
    )

  /** Breadth-first reachability, the expected algorithm. */
  def referenceReachable(graph: Graph, start: Int, target: Int): Boolean =
    val adjacency = graph.edges.groupMap(_._1)(_._2)
    def reached(frontier: Vector[Int], seen: Set[Int]): Boolean =
      if frontier.contains(target) then true
      else if frontier.isEmpty then false
      else
        val (nextFrontier, nextSeen) = frontier.foldLeft(
          (Vector.empty[Int], seen)
        ) { case ((found, seenSoFar), node) =>
          adjacency.getOrElse(node, Vector.empty).foldLeft((found, seenSoFar)) {
            case ((foundSoFar, current), successor) =>
              if current.contains(successor) then (foundSoFar, current)
              else (foundSoFar :+ successor, current + successor)
          }
        }
        reached(nextFrontier, nextSeen)
    reached(Vector(start), Set(start))

  /** The Church boolean of "the target is reachable from the start", under the
    * lets of the booleans, the nodes, is_target and reach.
    */
  def graphTerm(graph: Graph, start: Int, target: Int): Term =
    λ(trueVariable =>
      λ(falseVariable =>
        numeralLets(graph.count, None, Vector.empty)(nodes =>
          λ(isTarget =>
            λ(reach => reach(nodes(start)))(
              reachBody(graph, nodes, isTarget)(
                reachBody(graph, nodes, isTarget)
              )
            )
          )(
            λ(v =>
              numeralCase(
                (0 until graph.count).toVector.map(index =>
                  if index == target then trueVariable else falseVariable
                ),
                v
              )
            )
          )
        )
      )(λ(_ => λ(f => f)))
    )(λ(t => λ(_ => t)))

  /** The case of the node among the cases, a nested case on the numeral; beyond
    * the last case, top (`Term.top`), the term of no answer.
    */
  private def numeralCase(cases: Vector[Term], node: Term): Term =
    if cases.isEmpty then Term.top
    else
      node(cases.head)(λ(predecessor => numeralCase(cases.tail, predecessor)))

  /** \self. \v. is_target v + successors v. */
  private def reachBody(
      graph: Graph,
      nodes: Vector[Term],
      isTarget: Term
  ): Term =
    λ(self =>
      λ(v =>
        choice(
          isTarget(v),
          numeralCase(
            (0 until graph.count).toVector.map(index =>
              choice(
                graph.edges
                  .filter(_._1 == index)
                  .map((_, to) => self(self)(nodes(to)))*
              )
            ),
            v
          )
        )
      )
    )

  /** The lets of the nodes around the body; node 0 is zero, and each next node
    * the successor of the one before it.
    */
  private def numeralLets(
      count: Int,
      previous: Option[Term],
      nodes: Vector[Term]
  )(
      body: Vector[Term] => Term
  ): Term =
    if nodes.size == count then body(nodes)
    else
      val nodeTerm = previous match
        case None       => λ(z => λ(_ => z))
        case Some(node) => λ(_ => λ(s => s(node)))
      λ(node => numeralLets(count, Some(node), nodes :+ node)(body))(nodeTerm)
