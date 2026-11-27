package com.yang_bo.gezi.contest.corpora.reductions

import com.yang_bo.gezi.contest.corpora.common.ProblemData
import com.yang_bo.gezi.contest.corpora.common.ProblemField

import com.yang_bo.gezi.contest.corpora.reductions.Encodings.*
import com.yang_bo.gezi.frontend.Term
import com.yang_bo.gezi.frontend.Term.*
import scala.annotation.tailrec

/** The shortest walk that visits every node, the port of
  * `problems/hidden_37_visit_all`.
  */
object Hidden37VisitAll:

  private val family = "hidden_37_visit_all"

  /** The slack of a point, the constructors of
    * problems/hidden_37_visit_all/slack in order: the isolated trap, whose last
    * node loses its edges, and the amount added to the shortest length to make
    * the budget.
    */
  enum Slack:
    case Isolated
    case Added(amount: Int)

  /** The slack a field writes, a constructor of
    * problems/hidden_37_visit_all/slack read by its position
    * (`ProblemData.alternative`), added's field its amount.
    */
  def slack(field: ProblemField): Slack =
    ProblemData.alternative(field, ProblemData.caseCount[Slack]) match
      case (0, Vector())       => Slack.Isolated
      case (1, Vector(amount)) => Slack.Added(ProblemData.small(amount))
      case (position, fields)  =>
        throw IllegalArgumentException(
          s"the slack of $family at position $position has ${fields.size} fields"
        )

  /** Under the lets of the nodes,
    * `(\walk. [walk v (insert none v) Budget k | v a node]) Walk`
    * (`visit_all_term/4`).
    */
  def visitAllTerm(
      attractors: Attractors,
      count: Int,
      edges: Vector[(Int, Int)],
      budget: Int
  ): ProblemTerm =
    Graphs.numeralLets(
      count,
      nodes =>
        λ(walk =>
          members(nodes.map(node =>
            val insert =
              attractors.functionSurface("bit_set_insert", Spelling.Direct)
            val none = CollectKeys.noneCollected(attractors, count)
            val difference =
              attractors.functionSurface("natural_difference", Spelling.Direct)
            walk(node)(insert(none)(node))(unary(budget))(
              λ(remaining => difference(unary(budget))(remaining))
            )
          ))
        )(walkFunction(attractors, nodes, edges))
    )

  /** `Y (\self. \node. \visited. \r. \k. full visited (k r) (case node))`, each
    * case the steps to the node's neighbours (`walk_function/3`).
    */
  private def walkFunction(
      attractors: Attractors,
      nodes: Vector[ProblemTerm],
      edges: Vector[(Int, Int)]
  ): ProblemTerm =
    val full = attractors.functionSurface("bit_set_full", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(node =>
          λ(visited =>
            λ(remaining =>
              λ(continuation =>
                full(visited)(continuation(remaining))(
                  Graphs.numeralCase(
                    nodes.indices.toVector.map(index =>
                      members(
                        adjacent(edges, index).distinct.sorted.map(neighbour =>
                          val insert = attractors.functionSurface(
                            "bit_set_insert",
                            Spelling.Direct
                          )
                          remaining(top)(
                            λ(predecessor =>
                              self(nodes(neighbour))(
                                insert(visited)(nodes(neighbour))
                              )(predecessor)(continuation)
                            )
                          )
                        )
                      )
                    ),
                    node
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The neighbours of a node, every edge either way (`adjacent/3`). */
  def adjacent(edges: Vector[(Int, Int)], node: Int): Vector[Int] =
    edges.flatMap((first, second) =>
      (if first == node then Vector(second)
       else
         Vector.empty
      ) ++ (if second == node then Vector(first) else Vector.empty)
    )

  /** The length of the shortest walk that visits every node, by breadth-first
    * search over the visited masks and the last node (`shortest_visit_all/3`);
    * throws when none does, where the Prolog fails.
    */
  def shortestVisitAll(count: Int, edges: Vector[(Int, Int)]): Int =
    val level = (0 until count).toVector.map(node => (1 << node, node))
    layers(level, edges, (1 << count) - 1, level.toSet, 0)

  @tailrec
  private def layers(
      level: Vector[(Int, Int)],
      edges: Vector[(Int, Int)],
      full: Int,
      seen: Set[(Int, Int)],
      depth: Int
  ): Int =
    if level.isEmpty then
      throw IllegalArgumentException("no walk visits every node")
    else if level.exists(_._1 == full) then depth
    else
      val candidates = level
        .flatMap((mask, node) =>
          adjacent(edges, node).map(neighbour =>
            (mask | (1 << neighbour), neighbour)
          )
        )
        .distinct
        .sorted
      val fresh = candidates.filterNot(seen.contains)
      layers(fresh, edges, full, seen ++ fresh, depth + 1)

  private def next(state: Long): Long = DynamicReferences.nextRandom(state)

  /** A random tree over the shuffled nodes and `extra` random edges more
    * (`random_graph/4`).
    */
  def randomGraph(count: Int, extra: Int, seed: Long): Vector[(Int, Int)] =
    val (order, afterShuffle) = (0 until count).foldLeft(
      (Vector.empty[Int], (0 until count).toVector, seed)
    ) { case ((shuffled, rest, state), _) =>
      val following = next(state)
      val node = rest(((following >> 16) % rest.size).toInt)
      (shuffled :+ node, rest.filterNot(_ == node), following)
    } match
      case (shuffled, _, state) => (shuffled, state)
    val (_, treeState, treeEdges) = order.tail.foldLeft(
      (List(order.head), afterShuffle, List.empty[(Int, Int)])
    ) { case ((before, state, edges), node) =>
      val following = next(state)
      val parent = before(((following >> 16) % before.size).toInt)
      (node :: before, following, orderedEdge(node, parent) :: edges)
    }
    extraEdges(extra, count, treeState, treeEdges).toVector

  @tailrec
  private def extraEdges(
      left: Int,
      count: Int,
      state: Long,
      edges: List[(Int, Int)]
  ): List[(Int, Int)] =
    if left == 0 then edges
    else
      val stateOne = next(state)
      val stateTwo = next(stateOne)
      val first = ((stateOne >> 16) % count).toInt
      val second = ((stateTwo >> 16) % count).toInt
      val edge = orderedEdge(first, second)
      if first == second || edges.contains(edge) then
        extraEdges(left, count, stateTwo, edges)
      else extraEdges(left - 1, count, stateTwo, edge :: edges)

  private def orderedEdge(first: Int, second: Int): (Int, Int) =
    (math.min(first, second), math.max(first, second))

  /** The graph of a point; the isolated trap drops every edge of its last node
    * (`point_graph/3`).
    */
  def pointGraph(
      group: ReductionGroup,
      point: String
  ): (Int, Vector[(Int, Int)]) =
    group.problems(family).keyed("visit_point").get(point) match
      case Some(Vector(count, extra, seed, slack)) =>
        val countValue = ProblemData.small(count)
        val edges = randomGraph(
          countValue,
          ProblemData.small(extra),
          ProblemData.small(seed)
        )
        val kept = this.slack(slack) match
          case Slack.Isolated =>
            edges.filterNot((first, second) =>
              first == countValue - 1 || second == countValue - 1
            )
          case Slack.Added(_) => edges
        (countValue, kept)
      case other =>
        throw IllegalArgumentException(s"no visit point $point: $other")

  /** The problems (`visit_point/5`): the isolated trap takes the budget of the
    * connected seven and expects no tree; the others the shortest length plus
    * the slack.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("visit_point").map {
      case Vector(point, _, _, _, slack) =>
        val name = ProblemData.text(point)
        val (count, edges) = pointGraph(group, name)
        val (budget, expected) = this.slack(slack) match
          case Slack.Isolated =>
            val (_, connected) = pointGraph(group, "hidden_37_visit_all_seven")
            (shortestVisitAll(count, connected), Expected.Trees(Vector.empty))
          case Slack.Added(amount) =>
            val shortest = shortestVisitAll(count, edges)
            if amount == 0 then
              (shortest, Expected.One(Scott.unaryTree(shortest)))
            else if amount < 0 then
              (shortest + amount, Expected.Trees(Vector.empty))
            else
              throw IllegalArgumentException(
                s"the Prolog expects nothing for a positive slack: $name"
              )
        ReductionProblem(
          name,
          visitAllTerm(group.attractors, count, edges, budget),
          "unary",
          expected,
          Reduction.hiddenLimits
        )
      case other => throw IllegalArgumentException(s"not a visit point: $other")
    }
