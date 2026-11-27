package gezi.contest.corpora.reductions

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.reductions.Encodings.*
import gezi.frontend.Term
import gezi.frontend.Term.*

/** A graph of an empty-set reachability point: a cyclic graph of a shape and
  * size, or the infinite binary tree searched for a target node. Its cases are
  * the constructors of problems/empty_set_reachability/graph in order
  * (`EmptySetReachability.graphOf`).
  */
enum ReachabilityGraph:

  /** `cyclic(Shape, Size)`, the shape a constructor of
    * problems/schema/graph_shape.
    */
  case Cyclic(shape: GraphShape, size: Int)

  /** `tree(Order, Branches, TargetBits)`: the order of the branches, and the
    * bit whose branch is dropped (`without(Bit)`), or none (`both`).
    */
  case Tree(order: TreeOrder, branches: Option[Int], targetBits: Vector[Int])

/** The order of a tree's branches, the constructors of
  * problems/empty_set_reachability/order in order: the branch of bit 0 first,
  * and the branch of bit 1 first. `written` is the order's name as the claims
  * print the tree, `Tree(one_first,None,Vector(1))` for instance
  * (`HardCorpus.emptySetReachabilityFacts`); it is not a key of the data.
  */
enum TreeOrder(val written: String):
  case ZeroFirst extends TreeOrder("zero_first")
  case OneFirst extends TreeOrder("one_first")

/** Reachability with the empty set at the unreached nodes, the port of
  * `problems/empty_set_reachability`: the programs of its `contest_hard`
  * points, the cut graphs and the infinite tree.
  */
object EmptySetReachability:

  private val family = "empty_set_reachability"

  /** `cons` as a function, `\h. \t. \_. \c. c h t` (`cons_term/1`). */
  private def consTerm: ProblemTerm =
    λ(head => λ(tail => λ(_ => λ(consCase => consCase(head)(tail)))))

  /** `\n. \_. n` (`nil_term/1`). */
  private def nilTerm: ProblemTerm = λ(nilCase => λ(_ => nilCase))

  /** The program of `reach Count Start` on the graph, the Church true at the
    * target and top at every other node, under the lets of true, the nodes,
    * is_target and reach, a step budget of the node count
    * (`Graphs.budgetedReachBody`).
    */
  def cyclicGraphTerm(
      count: Int,
      edges: Vector[(Int, Int)],
      start: Int,
      target: Int
  ): ProblemTerm =
    λ(trueValue =>
      Graphs.numeralLets(
        count,
        nodes =>
          λ(isTarget =>
            λ(reach => reach(unary(count))(nodes(start)))(
              Graphs.budgetedReachBody(count, edges, nodes, isTarget)(
                Graphs.budgetedReachBody(count, edges, nodes, isTarget)
              )
            )
          )(
            λ(vertex =>
              Graphs.numeralCase(
                (0 until count).toVector.map(index =>
                  if index == target then trueValue else top
                ),
                vertex
              )
            )
          )
      )
    )(trueTerm)

  /** The graph of the shape and size with the one edge taken out after which
    * the target is not reachable from the start (`cut_graph/7`).
    */
  def cutGraph(shape: GraphShape, size: Int): (Graph, (Int, Int)) =
    val whole = Graphs.graph(shape, size)
    val removed = shape match
      case GraphShape.TwoRings  => (size - 1, size)
      case GraphShape.ChordRing => (whole.target - 1, whole.target)
    val index = whole.edges.indexOf(removed)
    if index < 0 then
      throw IllegalArgumentException(s"the graph has no edge $removed")
    val edges = whole.edges.patch(index, Vector.empty, 1)
    if Graphs.reachable(edges, whole.start, whole.target) then
      throw IllegalArgumentException(
        s"the target stays reachable without $removed"
      )
    (whole.copy(edges = edges), removed)

  private def orderedBits(order: TreeOrder): Vector[Int] = order match
    case TreeOrder.ZeroFirst => Vector(0, 1)
    case TreeOrder.OneFirst  => Vector(1, 0)

  /** The bits kept: both, or all but the first occurrence of the dropped one
    * (`kept_bits/3`).
    */
  private def keptBits(bits: Vector[Int], branches: Option[Int]): Vector[Int] =
    branches match
      case None          => bits
      case Some(dropped) =>
        val index = bits.indexOf(dropped)
        if index < 0 then
          throw IllegalArgumentException(s"no bit $dropped to drop")
        bits.patch(index, Vector.empty, 1)

  private def bitsList(bits: Vector[Int]): ProblemTerm =
    bits.foldRight(nilTerm)((bit, rest) => consTerm(bitBoolean(bit))(rest))

  /** The Boolean equality of two Scott lists of Booleans (`equality/1`). */
  private def equality(attractors: Attractors): ProblemTerm =
    attractors.fixpoint(
      λ(self =>
        λ(left =>
          λ(right =>
            left(right(trueTerm)(λ(_ => λ(_ => falseTerm))))(
              λ(leftBit =>
                λ(leftTail =>
                  right(falseTerm)(
                    λ(rightBit =>
                      λ(rightTail =>
                        leftBit(rightBit)(rightBit(falseTerm)(trueTerm))(
                          self(leftTail)(rightTail)
                        )(falseTerm)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )

  /** The program of `reach Depth nil` on the infinite binary tree, a depth
    * budget of the target's depth, top once it is spent
    * (`infinite_tree_term/4`), so that each reference answer has its proof.
    * Without the budget a branch that never meets the target reads ⊥ in
    * DdLP96's reading, the whole choice with it, and the program is below every
    * closed βη normal form in ⊑_O; with it the search is finite, so the target
    * is reached exactly when its bits are kept branches (`treeReachable`), and
    * a dropped branch is a trap whose answer set is empty.
    */
  def infiniteTreeTerm(
      attractors: Attractors,
      order: TreeOrder,
      branches: Option[Int],
      targetBits: Vector[Int]
  ): ProblemTerm =
    val kept = keptBits(orderedBits(order), branches)
    val equal = equality(attractors)
    val target = bitsList(targetBits)
    attractors.fixpoint(
      λ(self =>
        λ(budget =>
          λ(node =>
            members(
              Vector(
                equal(node)(target)(trueTerm)(top),
                budget(top)(
                  λ(predecessor =>
                    members(
                      kept.map(bit =>
                        self(predecessor)(consTerm(bitBoolean(bit))(node))
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )(unary(targetBits.size))(nilTerm)

  /** The depth of the target node when every bit it holds is a kept branch
    * (`tree_reachable/3`).
    */
  def treeReachable(
      branches: Option[Int],
      targetBits: Vector[Int]
  ): Option[Int] =
    val kept = keptBits(orderedBits(TreeOrder.ZeroFirst), branches)
    if targetBits.forall(kept.contains) then Some(targetBits.size) else None

  /** The number of nodes a breadth-first search of the tree expands before it
    * meets the target, level by level (`breadth_first_expansions/4`). Throws
    * when the target is not reachable, where the Prolog fails.
    */
  def breadthFirstExpansions(
      order: TreeOrder,
      branches: Option[Int],
      targetBits: Vector[Int]
  ): Int =
    if treeReachable(branches, targetBits).isEmpty then
      throw IllegalArgumentException(s"the target $targetBits is not reachable")
    val kept = keptBits(orderedBits(order), branches)
    expansionsUntil(Vector(Vector.empty), kept, targetBits, 0)

  @scala.annotation.tailrec
  private def expansionsUntil(
      level: Vector[Vector[Int]],
      kept: Vector[Int],
      targetBits: Vector[Int],
      count: Int
  ): Int =
    if level.contains(targetBits) then count
    else
      expansionsUntil(
        level.flatMap(node => kept.map(_ +: node)),
        kept,
        targetBits,
        count + level.size
      )

  /** The graph a fact's field writes, a constructor of
    * problems/empty_set_reachability/graph read by its position
    * (`ProblemData.alternative`): cyclic with its shape and size, or tree with
    * its order, branches and target bits.
    */
  def graphOf(field: ProblemField): ReachabilityGraph =
    ProblemData.alternative(
      field,
      ProblemData.caseCount[ReachabilityGraph]
    ) match
      case (0, Vector(shape, size)) =>
        ReachabilityGraph.Cyclic(Graphs.shape(shape), ProblemData.small(size))
      case (1, Vector(order, branches, bits)) =>
        ReachabilityGraph.Tree(
          treeOrder(order),
          this.branches(branches),
          ProblemData.smalls(bits)
        )
      case (position, fields) =>
        throw IllegalArgumentException(
          s"the graph of $family at position $position has ${fields.size} fields"
        )

  /** The order a field writes, a constructor of
    * problems/empty_set_reachability/order read by its position
    * (`ProblemData.alternative`).
    */
  def treeOrder(field: ProblemField): TreeOrder =
    ProblemData.alternative(field, TreeOrder.values.size) match
      case (position, Vector()) => TreeOrder.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"the order of $family has ${fields.size} fields"
        )

  /** The number of constructors of problems/empty_set_reachability/branches:
    * both, then without with its bit.
    */
  private val branchesCount: Int = 2

  /** The bit whose branch a tree drops, a constructor of
    * problems/empty_set_reachability/branches read by its position
    * (`ProblemData.alternative`): none for both, the bit for without.
    */
  def branches(field: ProblemField): Option[Int] =
    ProblemData.alternative(field, branchesCount) match
      case (0, Vector())      => None
      case (1, Vector(bit))   => Some(ProblemData.small(bit))
      case (position, fields) =>
        throw IllegalArgumentException(
          s"the branches of $family at position $position have ${fields.size} fields"
        )

  /** The public points and their graphs (`point/2`). */
  def points(group: ReductionGroup): Vector[(String, ReachabilityGraph)] =
    group.problems(family).rows("point").map {
      case Vector(point, graph) => (ProblemData.text(point), graphOf(graph))
      case other => throw IllegalArgumentException(s"not a point: $other")
    }

  /** The program of a point's graph (`graph_term/2`). */
  def graphTerm(attractors: Attractors, graph: ReachabilityGraph): ProblemTerm =
    graph match
      case ReachabilityGraph.Cyclic(shape, size) =>
        val built = Graphs.graph(shape, size)
        cyclicGraphTerm(built.count, built.edges, built.start, built.target)
      case ReachabilityGraph.Tree(order, branches, targetBits) =>
        infiniteTreeTerm(attractors, order, branches, targetBits)

  /** Whether the point's target is reachable (`graph_reachable/1`), the
    * condition of its scored claim.
    */
  def graphReachable(graph: ReachabilityGraph): Boolean = graph match
    case ReachabilityGraph.Cyclic(shape, size) =>
      val built = Graphs.graph(shape, size)
      Graphs.reachable(built.edges, built.start, built.target)
    case ReachabilityGraph.Tree(_, branches, targetBits) =>
      treeReachable(branches, targetBits).nonEmpty
