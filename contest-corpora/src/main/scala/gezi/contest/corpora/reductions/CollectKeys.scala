package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** Collecting keys on a grid within a budget, the port of
  * `problems/collect_keys`: the set of the totals of the walks
  * that collect every key in some order, each leg at most the number of
  * nodes long.
  */
object CollectKeys:

  private val family = "collect_keys"

  /** The grid graph, node `Row * Columns + Column`, an edge each way between
    * cells that share a side (`grid/4`).
    */
  def grid(rows: Int, columns: Int): (Int, Vector[(Int, Int)]) =
    val edges = for
      row <- (0 until rows).toVector
      column <- 0 until columns
      (rowStep, columnStep) <- Vector((0, 1), (1, 0), (0, -1), (-1, 0))
      nextRow = row + rowStep
      nextColumn = column + columnStep
      if nextRow >= 0 && nextRow < rows && nextColumn >= 0 && nextColumn < columns
    yield (row * columns + column, nextRow * columns + nextColumn)
    (rows * columns, edges)

  /** The bit set of `count` false elements (`none_collected/2`). */
  def noneCollected(attractors: Attractors, count: Int): Term =
    SetFree.booleanList(attractors, Vector.fill(count)(0))

  /** The program with each leg bounded by the number of nodes and the total
    * by the budget (`collect_keys_term/6`).
    */
  def collectKeysTerm(attractors: Attractors, count: Int, edges: Vector[(Int, Int)], keys: Vector[Int], start: Int, budget: Int): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    Graphs.numeralLets(
      count,
      nodes =>
        val lengthsFunction = lengthsFunctionTerm(attractors, count, edges, nodes)
        val none = noneCollected(attractors, keys.size)
        val difference = function("natural_difference")
        λ(lengths =>
          tourFunction(attractors, keys, nodes, count, lengths)(none)(nodes(start))(unary(budget))(λ(remaining =>
            difference(unary(budget))(remaining)
          ))
        )(lengthsFunction)
    )

  /** `Y (\self. \b. \v. \t. { equal v t (\k. k 0) top, b top (\p. walk) })`,
    * walk the numeral case of v over the boxes of its successors
    * (`lengths_function/4`).
    */
  private def lengthsFunctionTerm(attractors: Attractors, count: Int, edges: Vector[(Int, Int)], nodes: Vector[Term]): Term =
    val equal = attractors.functionSurface("natural_equal", Spelling.Direct)
    val zero = attractors.attractorSurface("zero", Spelling.Direct)
    attractors.fixpoint(
      λ(self =>
        λ(bound =>
          λ(vertex =>
            λ(target =>
              members(
                Vector(
                  equal(vertex)(target)(λ(continuation => continuation(zero)))(top),
                  bound(top)(λ(predecessor =>
                    Graphs.numeralCase(
                      (0 until count).toVector.map(index =>
                        members(edges.collect {
                          case (from, to) if from == index =>
                            val successor = attractors.functionSurface("successor", Spelling.Direct)
                            λ(continuation =>
                              self(predecessor)(nodes(to))(target)(λ(length => continuation(successor(length))))
                            )
                        })
                      ),
                      vertex
                    )
                  ))
                )
              )
            )
          )
        )
      )
    )

  /** `Y (\self. \c. \v. \r. \k. full c (k r) { branch_i | i a key })`
    * (`tour_function/5`).
    */
  private def tourFunction(attractors: Attractors, keys: Vector[Int], nodes: Vector[Term], count: Int, lengths: Term): Term =
    def function(name: String) = attractors.functionSurface(name, Spelling.Direct)
    val full = function("bit_set_full")
    attractors.fixpoint(
      λ(self =>
        λ(collected =>
          λ(vertex =>
            λ(remaining =>
              λ(continuation =>
                full(collected)(continuation(remaining))(members(keys.zipWithIndex.map((key, position) =>
                  val member = function("bit_set_member")
                  val insert = function("bit_set_insert")
                  val atLeast = function("natural_at_least")
                  val difference = function("natural_difference")
                  member(collected)(unary(position))(top)(lengths(unary(count))(vertex)(nodes(key))(λ(leg =>
                    atLeast(remaining)(leg)(self(insert(collected)(unary(position)))(nodes(key))(difference(remaining)(leg))(
                      continuation
                    ))(top)
                  )))
                )))
              )
            )
          )
        )
      )
    )

  /** The sorted totals of at most the budget of the walks from the start
    * that collect every key in some order (`collect_keys_totals/6`).
    */
  def collectKeysTotals(count: Int, edges: Vector[(Int, Int)], keys: Vector[Int], start: Int, budget: Int): Vector[Int] =
    keys.permutations.toVector
      .flatMap(order => orderTotals(order, start, count, edges, budget, 0))
      .distinct
      .sorted

  private def orderTotals(order: Vector[Int], from: Int, count: Int, edges: Vector[(Int, Int)], budget: Int, accumulated: Int): Vector[Int] =
    if order.isEmpty then Vector(accumulated)
    else
      PathLengths
        .walkLengths(edges, from, order.head, count)
        .map(accumulated + _)
        .filter(_ <= budget)
        .flatMap(next => orderTotals(order.tail, order.head, count, edges, budget, next))

  /** The least total over every order of the keys, each leg its
    * breadth-first distance (`shortest_total/5`).
    */
  def shortestTotal(count: Int, edges: Vector[(Int, Int)], keys: Vector[Int], start: Int): Int =
    keys.permutations.toVector
      .map(order =>
        order
          .foldLeft((start, 0)) { case ((from, sum), key) =>
            (key, sum + PathLengths.walkLengths(edges, from, key, count).head)
          }
          ._2
      )
      .min

  /** The problems (`collect_keys_point/5`), the start the corner 0 and the
    * budget the least total plus the slack.
    */
  def problems(group: ReductionGroup): Vector[ReductionProblem] =
    group.problems(family).rows("collect_keys_point").map {
      case Vector(point, rows, columns, keys, slack) =>
        val (count, edges) = grid(ProblemData.small(rows), ProblemData.small(columns))
        val keyNodes = ProblemData.smalls(keys)
        val budget = shortestTotal(count, edges, keyNodes, 0) + ProblemData.small(slack)
        ReductionProblem(
          ProblemData.text(point),
          collectKeysTerm(group.attractors, count, edges, keyNodes, 0, budget),
          "unary",
          Reduction.expectedOf(collectKeysTotals(count, edges, keyNodes, 0, budget).map(Scott.unaryTree)),
          Reduction.defaultLimits
        )
      case other => throw IllegalArgumentException(s"not a collect keys point: $other")
    }
