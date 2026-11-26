package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** The set of the nodes reachable from a start, the port of
  * `problems/reachable_set`: the reach of the Boolean family with
  * the identity where it applies is_target, read whole.
  */
object ReachableSet:

  private val family = "reachable_set"

  /** `reach Count Start` on the graph under the lets of the nodes and of the
    * identity, a step budget of the node count (`Graphs.budgetedReachBody`).
    */
  def reachableSetTerm(count: Int, edges: Vector[(Int, Int)], start: Int): ProblemTerm =
    Graphs.numeralLets(
      count,
      nodes =>
        λ(identity =>
          λ(reach => reach(unary(count))(nodes(start)))(
            Graphs.budgetedReachBody(count, edges, nodes, identity)(Graphs.budgetedReachBody(count, edges, nodes, identity))
          )
        )(λ(vertex => vertex))
    )

  /** The nodes reachable from the start, in order, by breadth-first search
    * node by node (`reachable_nodes/4`).
    */
  def reachableNodes(count: Int, edges: Vector[(Int, Int)], start: Int): Vector[Int] =
    (0 until count).toVector.filter(Graphs.reachable(edges, start, _))

  /** The graph of a point, the constructors of problems/reachable_set/graph
    * in order: the whole graph of a shape and size, and the same graph cut,
    * the edge taken out after which the target is not reachable.
    */
  enum PointGraph:
    case Whole(shape: GraphShape, size: Int)
    case Cut(shape: GraphShape, size: Int)

  /** The graph a field writes, a constructor of problems/reachable_set/graph
    * read by its position (`ProblemData.alternative`), its fields the shape
    * (a constructor of problems/schema/graph_shape) and the size.
    */
  def pointGraph(field: ProblemField): PointGraph =
    ProblemData.alternative(field, ProblemData.caseCount[PointGraph]) match
      case (0, Vector(shape, size)) => PointGraph.Whole(Graphs.shape(shape), ProblemData.small(size))
      case (1, Vector(shape, size)) => PointGraph.Cut(Graphs.shape(shape), ProblemData.small(size))
      case (position, fields) =>
        throw IllegalArgumentException(s"the graph of $family at position $position has ${fields.size} fields")

  /** The built graph of a point's graph (`point_graph/4`). */
  private def built(graph: PointGraph): Graph = graph match
    case PointGraph.Whole(shape, size) => Graphs.graph(shape, size)
    case PointGraph.Cut(shape, size)   => EmptySetReachability.cutGraph(shape, size)._1

  /** The problems (`reachable_set_point/2`). */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("reachable_set_point").map {
      case Vector(point, graph) =>
        val built = this.built(pointGraph(graph))
        ReductionProblem(
          ProblemData.text(point),
          reachableSetTerm(built.count, built.edges, built.start),
          "unary",
          Reduction.expectedOf(reachableNodes(built.count, built.edges, built.start).map(Scott.unaryTree)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a reachable set point: $other")
    }
