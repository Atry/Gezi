package com.yang_bo.gezi.saturation

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.GraphView
import com.yang_bo.gezi.egraph.Head
import com.yang_bo.gezi.egraph.MemberShape
import com.yang_bo.gezi.egraph.PositionRole
import com.yang_bo.gezi.egraph.PositionUser
import com.yang_bo.gezi.egraph.UserRole
import com.yang_bo.gezi.ir.{Configured, LayerWith, NativeSpecializer}

/** The platform-independent round stop of lemma matching at classes holding a native storage
  * of constant size (`com.yang_bo.gezi.ir.NativeStorage.constantSize`), when the round
  * chose it (`EGraph.constantStorageStop`): such a class is taken as usually
  * optimal, so no lemma is matched below it. The matchers see of such a class
  * its pattern views only (`EGraph.patternViews`, `Parallel(the class, T)`), so
  * that `?x ∥ ?T` still matches the storage, and a pattern that binds the class
  * as a metavariable reads no member at all; every other member of the class,
  * the leaf among them, is hidden. An instruction reference matches no stopped
  * class, though it reads no structure: the instruction's node is a hidden
  * member, and a closed subterm has one answer whether a lemma spells it as a
  * reference or as a compound pattern, which reads the node's layer. Only lemma
  * matching stops: the graph's own readers (congruence, the construction and
  * folding, β, body opening, reverse β) read the real graph. No answer here but
  * `root` and `layer` names a hidden node (a layer's children may be one, as
  * `double s` is of `g (double s)`), and a node reached that way is read only
  * as its class, through `root`, never by its layer.
  *
  * The stop loses instances only, never adds one. No reading of an ambiguous
  * typing is lost by it: the other readings of a value come from its consumer's
  * side, `g (c ∥ T)` binding c as a metavariable; the lemmas that read `?x ∥ T`
  * read it through the pattern view; and HM's constant schemes are rooted at a
  * value's bare node, which no stop hides, a storage built in the graph keeping
  * its one-layer view `Parallel(c, K)` with c outside the class. A delta
  * skipped here is matched again by a later round that does not stop: a round
  * begun on a shared graph redoes every node (`EGraph.everyNodeRedone`), which
  * is why that redo must stay.
  */
object ConstantStorageStop:

  /** Whether the round stops at the class: it chose the stop, and the class
    * holds a storage leaf of constant size (`StorageLeafAnalysis`).
    */
  def stopped[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      root: Int
  ): Boolean =
    graph.constantStorageStop &&
      graph
        .analysisValue(graph.storageLeaves, graph.root(root))
        .exists(_.storages.exists(_.constantSize))

  /** Whether the node is hidden from the matchers: a member of a class the
    * round stops at other than one of its pattern views.
    */
  def hidden[C <: NativeSpecializer & Singleton](
      graph: EGraph[C],
      node: Int
  ): Boolean =
    stopped(graph, node) && !graph.patternViews.contains(node)

  /** The view the matchers read: the graph, or, when the round stops, the graph
    * with the hidden members left out of every answer.
    */
  def view[C <: NativeSpecializer & Singleton](graph: EGraph[C]): GraphView[C] =
    if graph.constantStorageStop then Stopped(graph) else graph

  /** The graph as the matchers read it when the round stops: a stopped class's
    * members are its pattern views, no user is a hidden member, a lookup or an
    * instruction that finds a hidden node finds none, and a stopped class holds
    * no closure the matchers can read. `layer`, `root` and `live` are the
    * graph's: every node whose layer a step reads comes from an answer filtered
    * here or from a delta, and a hidden delta is skipped
    * (`Saturation.deltaMatched`); `root` may name a hidden node, the class's
    * root, whose layer no step reads.
    */
  private final class Stopped[C <: NativeSpecializer & Singleton](
      graph: EGraph[C]
  ) extends GraphView[C]:
    def layer(node: Int): LayerWith[Int, Configured[C]] = graph.layer(node)
    def root(node: Int): Int = graph.root(node)
    def live(node: Int): Boolean = graph.live(node)
    def members(root: Int, shape: MemberShape): Vector[Int] =
      graph.members(root, shape).filterNot(hidden(graph, _))
    def headMembers(root: Int, head: Head[C]): Vector[Int] =
      graph.headMembers(root, head).filterNot(hidden(graph, _))
    def users(root: Int, role: UserRole): Vector[Int] =
      graph.users(root, role).filterNot(hidden(graph, _))
    def positionUsers(root: Int, role: PositionRole): Vector[PositionUser] =
      graph
        .positionUsers(root, role)
        .filterNot(user => hidden(graph, user.user))
    def instructionNode(instruction: Configured[C]): Option[Int] =
      graph.instructionNode(instruction).filterNot(hidden(graph, _))
    def layerNode(layer: LayerWith[Int, Configured[C]]): Option[Int] =
      graph.layerNode(layer).filterNot(hidden(graph, _))
    def hasClosure(root: Int): Boolean =
      !stopped(graph, root) && graph.hasClosure(root)
