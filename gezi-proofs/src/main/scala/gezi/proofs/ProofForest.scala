package gezi.proofs

import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import scala.annotation.tailrec
import gezi.ir.Thunk

/** One step of a path in the forest: the union, from the node of one index
  * to the node of the other.
  */
final case class PathStep(union: Int, from: Int, to: Int)

/** The terms of a proof and the forest its unions make. A NODE is a term of
  * the proof; its index is its place in the proof's terms, the order the
  * search made them.
  *
  * @param indexes
  *   each node's index
  * @param nodes
  *   each index's node
  * @param unions
  *   the unions, the one numbered `i` at position `i - 1`
  * @param adjacency
  *   each node's index to its `(neighbor index, union)` pairs, one per union
  *   that names the node, the latest union first
  * @param parents
  *   each node's index to its parent's index and the union between them, in
  *   the forest rooted at the earliest node of each tree; a root has none
  * @param depths
  *   each node's index to its depth in that rooted forest
  * @param thunks
  *   each code and holes to the nodes whose layer is a thunk of them, in
  *   creation order
  */
final case class ProofForest(
    indexes: Map[Instruction, Int],
    nodes: Vector[Instruction],
    unions: Vector[ProofUnion],
    adjacency: Map[Int, List[(Int, Int)]],
    parents: Map[Int, (Int, Int)],
    depths: Map[Int, Int],
    thunks: Map[(Code, Vector[Hole]), Vector[Instruction]]
):

  /** One more than the last union's number: the time by which every union
    * was made.
    */
  def finalTime: Int = unions.size + 1

  def isNode(instruction: Instruction): Boolean = indexes.contains(instruction)

  /** The index of a node. Throws `OpentheoryArticleError` with `NotANode`
    * for an instruction that is no term of the proof.
    */
  def index(instruction: Instruction): Int =
    indexes.getOrElse(instruction, throw OpentheoryArticleError(ArticleErrorReason.NotANode(instruction)))

  /** The union numbered `number`. */
  def union(number: Int): ProofUnion = unions(number - 1)

  /** The path from one node to the other in the forest, or nothing when the
    * two are in two trees. Throws as `index` does.
    */
  def pathSteps(first: Instruction, second: Instruction): Option[Vector[PathStep]] =
    val firstIndex = index(first)
    val secondIndex = index(second)
    climbed(firstIndex, depths(firstIndex), secondIndex, depths(secondIndex), Vector.empty, Vector.empty)
      .map((up, otherUp) => up ++ otherUp.reverse.map(step => PathStep(step.union, step.to, step.from)))

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
      climbed(parent, firstDepth - 1, second, secondDepth, up :+ PathStep(union, first, parent), otherUp)
    else if secondDepth > firstDepth then
      val (parent, union) = parents(second)
      climbed(first, firstDepth, parent, secondDepth - 1, up, otherUp :+ PathStep(union, second, parent))
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

  /** The two nodes were one class before the union `time` was made: the
    * path between them has only unions below `time`.
    */
  def connectedBefore(first: Instruction, second: Instruction, time: Int): Boolean =
    first == second ||
      (isNode(first) && isNode(second) &&
        pathSteps(first, second).exists(_.forall(_.union < time)))

  /** The nodes of the target's class before the union `time`, the target
    * first and the others in creation order. Throws as `index` does.
    */
  def candidatesBefore(target: Instruction, time: Int): Vector[Instruction] =
    val targetIndex = index(target)
    val visited = classVisited(List(targetIndex), time, Set(targetIndex))
    target +: (visited - targetIndex).toVector.sorted.map(nodes)

  @tailrec
  private def classVisited(stack: List[Int], time: Int, visited: Set[Int]): Set[Int] = stack match
    case Nil => visited
    case current :: rest =>
      val neighbors = adjacency.getOrElse(current, Nil).collect {
        case (neighbor, union) if union < time => neighbor
      }
      val (nextStack, nextVisited) = neighbors.foldLeft((rest, visited)) {
        case ((pending, seen), neighbor) =>
          if seen.contains(neighbor) then (pending, seen) else (neighbor :: pending, seen + neighbor)
      }
      classVisited(nextStack, time, nextVisited)

/** The forest of a proof. */
object ProofForest:

  /** The forest of the proof's terms and unions, the layers read from the
    * store. Throws `OpentheoryArticleError` with `TermTwice` for a term
    * named twice, `UnionsOutOfOrder` when the unions are not numbered from 1
    * in order, `NotANode` for a union that names no term, and
    * `UnionWithinAClass` for a union between two nodes of one tree, a defect
    * of the search.
    */
  def of(proof: StrategyProof, store: ArticleStore): ProofForest =
    val indexes = proof.terms.zipWithIndex.foldLeft(Map.empty[Instruction, Int]) { case (found, (term, index)) =>
      if found.contains(term) then throw OpentheoryArticleError(ArticleErrorReason.TermTwice(term))
      found.updated(term, index)
    }
    // An opaque term (an eigenvariable a body was opened at) has no layer
    // and is no thunk.
    val thunks = proof.terms.filterNot(_.opaque).foldLeft(Map.empty[(Code, Vector[Hole]), Vector[Instruction]]) {
      (filed, term) =>
        store.layer(term) match
          case Thunk(code, holes, _) =>
            filed.updated((code, holes), filed.getOrElse((code, holes), Vector.empty) :+ term)
          case _ => filed
    }
    val adjacency = proof.unions.zipWithIndex.foldLeft(Map.empty[Int, List[(Int, Int)]]) {
      case (edges, (union, position)) =>
        if union.index != position + 1 then
          throw OpentheoryArticleError(ArticleErrorReason.UnionsOutOfOrder(position + 1, union.index))
        def nodeIndex(instruction: Instruction) =
          indexes.getOrElse(instruction, throw OpentheoryArticleError(ArticleErrorReason.NotANode(instruction)))
        val first = nodeIndex(union.first)
        val second = nodeIndex(union.second)
        edges
          .updated(first, (second, union.index) :: edges.getOrElse(first, Nil))
          .updated(second, (first, union.index) :: edges.getOrElse(second, Nil))
    }
    val (parents, depths) = proof.terms.indices.foldLeft((Map.empty[Int, (Int, Int)], Map.empty[Int, Int])) {
      case ((parentsSoFar, depthsSoFar), index) =>
        if depthsSoFar.contains(index) then (parentsSoFar, depthsSoFar)
        else descended(List(index), adjacency, parentsSoFar, depthsSoFar.updated(index, 0))
    }
    ProofForest(indexes, proof.terms, proof.unions, adjacency, parents, depths, thunks)

  /** The tree of the nodes on the stack, rooted: each neighbor met for the
    * first time gets its parent and depth and is pushed; a neighbor met
    * again must be the node's parent through the same union.
    */
  @tailrec
  private def descended(
      stack: List[Int],
      adjacency: Map[Int, List[(Int, Int)]],
      parents: Map[Int, (Int, Int)],
      depths: Map[Int, Int]
  ): (Map[Int, (Int, Int)], Map[Int, Int]) = stack match
    case Nil => (parents, depths)
    case current :: rest =>
      val deeper = depths(current) + 1
      val (nextStack, nextParents, nextDepths) =
        adjacency.getOrElse(current, Nil).foldLeft((rest, parents, depths)) {
          case ((pending, parentsSoFar, depthsSoFar), (neighbor, union)) =>
            if depthsSoFar.contains(neighbor) then
              if parentsSoFar.get(current).contains((neighbor, union)) then (pending, parentsSoFar, depthsSoFar)
              else throw OpentheoryArticleError(ArticleErrorReason.UnionWithinAClass(union))
            else
              (
                neighbor :: pending,
                parentsSoFar.updated(neighbor, (current, union)),
                depthsSoFar.updated(neighbor, deeper)
              )
        }
      descended(nextStack, adjacency, nextParents, nextDepths)
