package com.yang_bo.gezi.proofs

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.Thunk
import com.yang_bo.gezi.ir.{NativeSpecializer}

/** One step of a path in the forest: the union, from one node to the other.
  */
final case class PathStep(union: Int, from: Int, to: Int)

/** The nodes of a proof and the forest its unions make. A NODE is a node of the
  * proof, by its number, the order the search made them; its TERM is the
  * article's term of it (`ProofTerms.nodeTerm`). The matcher and the writer
  * name nodes by their terms, a term standing for the first node whose term it
  * is (`ProofTerms.node`).
  *
  * @param terms
  *   the article's terms, each node's among them
  * @param unions
  *   the unions, the one numbered `i` at position `i - 1`
  * @param adjacency
  *   each node to its `(neighbor, union)` pairs, one per union that names the
  *   node, the latest union first
  * @param parents
  *   each node to its parent and the union between them, in the forest rooted
  *   at the earliest node of each tree; a root has none
  * @param depths
  *   each node to its depth in that rooted forest
  * @param thunks
  *   each code and holes to the terms of the nodes whose layer is a thunk of
  *   them, in creation order
  */
final case class ProofForest[C <: NativeSpecializer & Singleton](
    terms: ProofTerms[C],
    unions: Vector[ProofUnion],
    adjacency: Map[Int, List[(Int, Int)]],
    parents: Map[Int, (Int, Int)],
    depths: Map[Int, Int],
    thunks: Map[(Code, Vector[Hole]), Vector[TermId]]
):

  /** One more than the last union's number: the time by which every union was
    * made.
    */
  def finalTime: Int = unions.size + 1

  /** The terms of the nodes, by the nodes' numbers. */
  def nodes: Vector[TermId] = Vector.tabulate(terms.nodeCount)(terms.nodeTerm)

  def isNode(term: TermId): Boolean = terms.node(term).isDefined

  /** The node of a term. Throws `OpentheoryArticleError` with `NotANode` for a
    * term that is no node's.
    */
  def index(term: TermId): Int =
    terms
      .node(term)
      .getOrElse(
        throw OpentheoryArticleError(ArticleErrorReason.NotANode(term))
      )

  /** The union numbered `number`. */
  def union(number: Int): ProofUnion = unions(number - 1)

  /** The path from the node of one term to the node of the other in the forest,
    * or nothing when the two are in two trees. Throws as `index` does.
    */
  def pathSteps(first: TermId, second: TermId): Option[Vector[PathStep]] =
    val firstIndex = index(first)
    val secondIndex = index(second)
    climbed(
      firstIndex,
      depths(firstIndex),
      secondIndex,
      depths(secondIndex),
      Vector.empty,
      Vector.empty
    )
      .map((up, otherUp) =>
        up ++ otherUp.reverse.map(step =>
          PathStep(step.union, step.to, step.from)
        )
      )

  @tailrec
  private def climbed(
      first: Int,
      firstDepth: Int,
      second: Int,
      secondDepth: Int,
      up: Vector[PathStep],
      otherUp: Vector[PathStep]
  ): Option[(Vector[PathStep], Vector[PathStep])] =
    if first == second then Some((up, otherUp))
    else if firstDepth > secondDepth then
      val (parent, union) = parents(first)
      climbed(
        parent,
        firstDepth - 1,
        second,
        secondDepth,
        up :+ PathStep(union, first, parent),
        otherUp
      )
    else if secondDepth > firstDepth then
      val (parent, union) = parents(second)
      climbed(
        first,
        firstDepth,
        parent,
        secondDepth - 1,
        up,
        otherUp :+ PathStep(union, second, parent)
      )
    else if firstDepth > 0 then
      val (firstParent, firstUnion) = parents(first)
      val (secondParent, secondUnion) = parents(second)
      climbed(
        firstParent,
        firstDepth - 1,
        secondParent,
        secondDepth - 1,
        up :+ PathStep(firstUnion, first, firstParent),
        otherUp :+ PathStep(secondUnion, second, secondParent)
      )
    else None

  /** The nodes of the two terms were one class before the union `time` was
    * made: one term, or the path between them has only unions below `time`.
    */
  def connectedBefore(first: TermId, second: TermId, time: Int): Boolean =
    first == second ||
      (isNode(first) && isNode(second) &&
        pathSteps(first, second).exists(_.forall(_.union < time)))

  /** The terms of the nodes of the target's class before the union `time`, the
    * target first and the others in creation order. Throws as `index` does.
    */
  def candidatesBefore(target: TermId, time: Int): Vector[TermId] =
    val targetIndex = index(target)
    val visited = classVisited(List(targetIndex), time, Set(targetIndex))
    target +: (visited - targetIndex).toVector.sorted.map(terms.nodeTerm)

  @tailrec
  private def classVisited(
      stack: List[Int],
      time: Int,
      visited: Set[Int]
  ): Set[Int] = stack match
    case Nil             => visited
    case current :: rest =>
      val neighbors = adjacency.getOrElse(current, Nil).collect {
        case (neighbor, union) if union < time => neighbor
      }
      val (nextStack, nextVisited) = neighbors.foldLeft((rest, visited)) {
        case ((pending, seen), neighbor) =>
          if seen.contains(neighbor) then (pending, seen)
          else (neighbor :: pending, seen + neighbor)
      }
      classVisited(nextStack, time, nextVisited)

/** The forest of a proof. */
object ProofForest:

  /** The forest of the proof's nodes and unions, the nodes' terms those given.
    * Throws `OpentheoryArticleError` with `UnionsOutOfOrder` when the unions
    * are not numbered from 1 in order, `NotANode` for a union that names no
    * node, and `UnionWithinAClass` for a union between two nodes of one tree, a
    * defect of the search.
    */
  def of[C <: NativeSpecializer & Singleton](
      proof: StrategyProof[C],
      terms: ProofTerms[C]
  ): ProofForest[C] =
    // An opaque term (an eigenvariable a body was opened at) has no layer
    // and is no thunk.
    val thunks = (0 until terms.nodeCount)
      .map(terms.nodeTerm)
      .foldLeft(Map.empty[(Code, Vector[Hole]), Vector[TermId]]) {
        (filed, term) =>
          terms.key(term) match
            case TermKey.Layered(Thunk(code, holes, _)) =>
              filed.updated(
                (code, holes),
                filed.getOrElse((code, holes), Vector.empty) :+ term
              )
            case _ => filed
      }
    val adjacency =
      proof.unions.zipWithIndex.foldLeft(Map.empty[Int, List[(Int, Int)]]) {
        case (edges, (union, position)) =>
          if union.index != position + 1 then
            throw OpentheoryArticleError(
              ArticleErrorReason.UnionsOutOfOrder(position + 1, union.index)
            )
          def nodeIndex(node: Int) =
            if node < 0 || node >= terms.nodeCount then
              throw OpentheoryArticleError(
                ArticleErrorReason.NotANodeNumber(node)
              )
            node
          val first = nodeIndex(union.first)
          val second = nodeIndex(union.second)
          edges
            .updated(
              first,
              (second, union.index) :: edges.getOrElse(first, Nil)
            )
            .updated(
              second,
              (first, union.index) :: edges.getOrElse(second, Nil)
            )
      }
    val (parents, depths) = (0 until terms.nodeCount).foldLeft(
      (Map.empty[Int, (Int, Int)], Map.empty[Int, Int])
    ) { case ((parentsSoFar, depthsSoFar), index) =>
      if depthsSoFar.contains(index) then (parentsSoFar, depthsSoFar)
      else
        descended(
          List(index),
          adjacency,
          parentsSoFar,
          depthsSoFar.updated(index, 0)
        )
    }
    ProofForest(terms, proof.unions, adjacency, parents, depths, thunks)

  /** The tree of the nodes on the stack, rooted: each neighbor met for the
    * first time gets its parent and depth and is pushed; a neighbor met again
    * must be the node's parent through the same union.
    */
  @tailrec
  private def descended(
      stack: List[Int],
      adjacency: Map[Int, List[(Int, Int)]],
      parents: Map[Int, (Int, Int)],
      depths: Map[Int, Int]
  ): (Map[Int, (Int, Int)], Map[Int, Int]) = stack match
    case Nil             => (parents, depths)
    case current :: rest =>
      val deeper = depths(current) + 1
      val (nextStack, nextParents, nextDepths) =
        adjacency.getOrElse(current, Nil).foldLeft((rest, parents, depths)) {
          case ((pending, parentsSoFar, depthsSoFar), (neighbor, union)) =>
            if depthsSoFar.contains(neighbor) then
              if parentsSoFar.get(current).contains((neighbor, union)) then
                (pending, parentsSoFar, depthsSoFar)
              else
                throw OpentheoryArticleError(
                  ArticleErrorReason.UnionWithinAClass(union)
                )
            else
              (
                neighbor :: pending,
                parentsSoFar.updated(neighbor, (current, union)),
                depthsSoFar.updated(neighbor, deeper)
              )
        }
      descended(nextStack, adjacency, nextParents, nextDepths)
