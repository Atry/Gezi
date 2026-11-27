package gezi.contest.corpora.merges

import gezi.contest.corpora.common.ProblemData
import gezi.contest.corpora.common.ProblemFamilies
import gezi.contest.corpora.common.ProblemField

import gezi.contest.corpora.merges.ClaimFact.ScoredFiniteHead
import gezi.frontend.Term
import gezi.frontend.Term.*
import scala.annotation.tailrec

/** A directed graph of the merge family: its node count, its edges From to To
  * in their order, its start and its target (`graph/6`).
  */
final case class MergeGraphShape(
    count: Int,
    edges: Vector[(Int, Int)],
    start: Int,
    target: Int
)

/** The port of the deleted Prolog file (`git show
  * 91b3f11e1^:lambda_jit/corpora/contest_merge_graph.pl`; its data are
  * `problems/merge_graph`): reachability in lambda plus choice, the nodes unary
  * numerals let bound once, `reach` a self-applied walk that merges the calls
  * on a node's successors, and the Church Boolean of "the target is reachable
  * from the start". The Booleans and the table of points are read from the
  * family's directory, `gezi/problems/merge_graph`.
  */
final class MergeGraph(problems: ProblemFamilies):

  private val file = problems("merge_graph")

  private def trueTerm: ProblemTerm = file.program("true_term")

  private def falseTerm: ProblemTerm = file.program("false_term")

  import MergeGraph.{graph, reachBody}

  /** The Church Boolean of "target is reachable from start", under the lets of
    * the Booleans, the nodes, `is_target` and `reach` (`graph_term/5`).
    */
  def graphTerm(
      count: Int,
      edges: Vector[(Int, Int)],
      start: Int,
      target: Int
  ): ProblemTerm =
    λ(trueValue =>
      λ(falseValue =>
        MergeGraph.numeralLets(
          count,
          nodes =>
            λ(isTarget =>
              λ(reach => reach(nodes(start)))(
                reachBody(count, edges, nodes, isTarget)(
                  reachBody(count, edges, nodes, isTarget)
                )
              )
            )(
              λ(v =>
                MergeGraph.numeralCase(
                  (0 until count).toVector.map(index =>
                    if index == target then trueValue else falseValue
                  ),
                  v
                )
              )
            )
        )
      )(falseTerm)
    )(trueTerm)

  /** The points, each with its shape and size (`graph_point/3`), the shape a
    * constructor of problems/schema/graph_shape (`MergeGraph.shape`).
    */
  val points: Vector[(String, MergeGraph.GraphShape, Int)] =
    file
      .rows("graph_point")
      .map(arguments =>
        (
          ProblemData.text(arguments(0)),
          MergeGraph.shape(arguments(1)),
          ProblemData.small(arguments(2))
        )
      )

  /** The point's program. */
  def program(name: String): ProblemTerm =
    points
      .find(_._1 == name)
      .map((_, shape, size) =>
        val shown = graph(shape, size)
        graphTerm(shown.count, shown.edges, shown.start, shown.target)
      )
      .getOrElse(
        throw IllegalArgumentException(
          s"$name is no point of contest_merge_graph"
        )
      )

  /** The claim facts of the file's points. */
  def claims: Vector[ClaimFact] =
    points.flatMap((name, shape, size) =>
      val shown = graph(shape, size)
      assert(
        MergeGraph.reachable(shown.edges, shown.start, shown.target),
        s"the target of $name is reachable"
      )
      ClaimFact.headPoint(name, ClaimFact.boolean(true)) :+ ScoredFiniteHead(
        name,
        Vector(ClaimFact.boolean(true)),
        s"node ${shown.target} is reachable from node ${shown.start} in the ${shape.written} of size $size (breadth-first search); choosing at each merge the successor on a shortest path yields is_target of node ${shown.target}, the Church true, in finitely many head reductions"
      )
    )

/** The pieces the former `contest_merge_graph` module exported to the other
  * files of the merge family and to the reduction group's graph families.
  */
object MergeGraph:

  /** The shape of a graph, the constructors of problems/schema/graph_shape in
    * order: two rings joined by one edge, then a ring whose every node also
    * points back to the one before it. `written` is the shape's name in the
    * claims' prose and in the tests' names of their cases, the name the data
    * wrote as a text before its options became Scott data; it is not a key of
    * the data, and every site that prints a shape calls it explicitly.
    */
  enum GraphShape(val written: String):
    case TwoRings extends GraphShape("two_rings")
    case ChordRing extends GraphShape("chord_ring")

  /** The shape a field writes, a constructor of problems/schema/graph_shape
    * read by its position (`ProblemData.alternative`).
    */
  def shape(field: ProblemField): GraphShape =
    ProblemData.alternative(field, GraphShape.values.size) match
      case (position, Vector()) => GraphShape.fromOrdinal(position)
      case (_, fields)          =>
        throw IllegalArgumentException(
          s"a shape of problems/schema/graph_shape has ${fields.size} fields"
        )

  /** The graph of a shape and a size: two rings of `size` nodes joined by one
    * edge, or a ring of `size` nodes each also pointing back to the one before
    * it (`graph/6`).
    */
  def graph(shape: GraphShape, size: Int): MergeGraphShape = shape match
    case GraphShape.TwoRings =>
      val count = 2 * size
      MergeGraphShape(
        count,
        ringEdges(0, size - 1) ++ Vector((size - 1, size)) ++ ringEdges(
          size,
          count - 1
        ),
        0,
        count - 1
      )
    case GraphShape.ChordRing =>
      MergeGraphShape(size, chordEdges(size - 1), 0, size - 1)

  /** For each node, the choice of `self self` applied to each of its
    * successors, in the edges' order (`successor_merges/6`).
    */
  private def successorMerges(
      count: Int,
      edges: Vector[(Int, Int)],
      nodes: Vector[ProblemTerm],
      self: ProblemTerm
  ): Vector[ProblemTerm] =
    (0 until count).toVector.map(index =>
      choice(edges.collect {
        case (from, to) if from == index => self(self)(nodes(to))
      }*)
    )

  /** `\self. \v. [is_target v, successors v]` (`reach_body/5`): see the comment
    * of `numeralCase` on why the encoding is sound.
    */
  def reachBody(
      count: Int,
      edges: Vector[(Int, Int)],
      nodes: Vector[ProblemTerm],
      isTarget: ProblemTerm
  ): ProblemTerm =
    λ(self =>
      λ(v =>
        choice(
          isTarget(v),
          numeralCase(successorMerges(count, edges, nodes, self), v)
        )
      )
    )

  /** `\self. \budget. \v. [is_target v, budget top (\p. successors p v)]`: the
    * reach body with a step budget, a unary numeral that each step takes the
    * predecessor of, top once it is spent. The recursion terminates, so the
    * program has a normal form with its choices as constructors and its
    * answers, the closed βη normal forms N with program ⊑_O N, are those of its
    * selections, so that each reference answer has its proof. Without the
    * budget a walk round a cycle reads ⊥ in DdLP96's reading, the whole choice
    * with it, and the program is below every closed βη normal form in ⊑_O. A
    * budget of the node count reaches every reachable node: each is reached by
    * a path of fewer steps.
    */
  def budgetedReachBody(
      count: Int,
      edges: Vector[(Int, Int)],
      nodes: Vector[ProblemTerm],
      isTarget: ProblemTerm
  ): ProblemTerm =
    λ(self =>
      λ(budget =>
        λ(v =>
          choice(
            isTarget(v),
            budget(top)(
              λ(predecessor =>
                numeralCase(
                  budgetedSuccessorMerges(
                    count,
                    edges,
                    nodes,
                    self,
                    predecessor
                  ),
                  v
                )
              )
            )
          )
        )
      )
    )

  /** For each node, the choice of `self self p` applied to each of its
    * successors, in the edges' order, p the budget left.
    */
  private def budgetedSuccessorMerges(
      count: Int,
      edges: Vector[(Int, Int)],
      nodes: Vector[ProblemTerm],
      self: ProblemTerm,
      predecessor: ProblemTerm
  ): Vector[ProblemTerm] =
    (0 until count).toVector.map(index =>
      choice(edges.collect {
        case (from, to) if from == index => self(self)(predecessor)(nodes(to))
      }*)
    )

  /** The case of `node` among `cases`, a nested case on the unary numeral node;
    * beyond the last case, top, the term for no answer (`numeral_case/3`; the
    * empty choice before the IR lost it).
    *
    * FIXME (carried from the deleted Prolog file, `numeral_case/3`,
    * https://github.com/Atry/private-overlay/issues/1989
    * `git show 91b3f11e1^:lambda_jit/corpora/contest_merge_graph.pl`): the
    * proofs of the families built on `reach_body/5` depend on that top, which
    * is a by-product of the encoding, not a design. A case table without it,
    * one whose last case is its own default, would make the walk-only generator
    * pure: replacing the pair by walk and every successor choice by one call,
    * inside the generator, gives a pure knot whose yield has no head normal
    * form, and such a yield can be consistent with every Boolean (the infinite
    * tree of the empty-set reachability's `without(Bit)`, the FIXME at
    * `gezi.contest.corpora.reductions.EmptySetReachability`'s `keptBits`, is
    * the witness). Keep the top, or make the families' soundness rest on
    * something explicit.
    *
    * Why the encoding is sound against choices inside the generator (the
    * comment of `reach_body/5`): rule 36's set clause lets one member
    * replacement act on a set occurrence inside the abstraction, before any
    * unfolding, and every unfolding of that copy shares it. The copy passed as
    * self stands in the term while any call of reach does; whatever is chosen
    * inside it, it keeps walk, a numeral case on the bound v with top beyond
    * the last case, or `is_target` applied to the bound
    *   v. In the Boolean families `is_target` is a numeral case with the same
    *      top, and no beta step erases it while v is bound, so a term that
    *      still holds a copy of self is not pure, and a yield is made only by a
    *      finite path of choices that ends in `is_target` at a node. The proofs
    *      of `problems/reachable_set` and `problems/empty_set_reachability`
    *      rest on this.
    */
  def numeralCase(cases: Vector[ProblemTerm], node: ProblemTerm): ProblemTerm =
    if cases.isEmpty then top
    else
      node(cases.head)(λ(predecessor => numeralCase(cases.tail, predecessor)))

  /** The lets of `count` nodes around the body, which refers to them by the
    * variables it is given: node 0 is zero, each next node the successor of the
    * one before it (`numeral_lets/4`).
    */
  def numeralLets(
      count: Int,
      body: Vector[ProblemTerm] => ProblemTerm
  ): ProblemTerm =
    def bound(
        index: Int,
        previous: Option[ProblemTerm],
        nodes: Vector[ProblemTerm]
    ): ProblemTerm =
      if index == count then body(nodes)
      else
        val value = previous match
          case None              => λ(zero => λ(_ => zero))
          case Some(predecessor) =>
            λ(_ => λ(successor => successor(predecessor)))
        λ(node => bound(index + 1, Some(node), nodes :+ node))(value)
    bound(0, None, Vector.empty)

  /** first -> first + 1 -> ... -> last, and last back to first, listed node by
    * node (`ring_edges/3`).
    */
  def ringEdges(first: Int, last: Int): Vector[(Int, Int)] =
    (first until last).toVector.map(node => (node, node + 1)) :+ (last, first)

  /** Each node first back to the one before it (not node 0), then on to the
    * next, and last back to 0 (`chord_edges/3`).
    */
  def chordEdges(last: Int): Vector[(Int, Int)] =
    (0 to last).toVector.flatMap(node =>
      (if node > 0 then Vector((node, node - 1)) else Vector.empty) ++
        (if node == last then Vector((last, 0)) else Vector((node, node + 1)))
    )

  /** Breadth-first reachability, each node expanded once
    * (`reference_reachable/4`).
    */
  def reachable(edges: Vector[(Int, Int)], start: Int, target: Int): Boolean =
    val adjacency = edges.groupMap(_._1)(_._2)
    @tailrec
    def search(frontier: Vector[Int], seen: Set[Int]): Boolean =
      if frontier.contains(target) then true
      else if frontier.isEmpty then false
      else
        val next = frontier
          .flatMap(node => adjacency.getOrElse(node, Vector.empty))
          .distinct
          .filterNot(seen)
        search(next, seen ++ next)
    search(Vector(start), Set(start))
