package gezi.egraph

import hedgehog.Result
import gezi.ir.BindingNormalForm
import gezi.ir.LayerWith
import gezi.ir.Store
import gezi.ir.Thunk
import gezi.generatedinputs.StandInStorages
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StoreGenerators

/** The law that adding a store's instructions to an empty graph gives each
  * instruction the node of its layer in the front end's spelling over the nodes
  * of that layer's children, one node per distinct such layer, on generated
  * stores (`StoreGenerators.store`). An instruction's layer in the front end's
  * spelling is its layer, except for a thunk with holes that the front end
  * spells otherwise, whose layer is its respelling
  * (`BindingNormalForm.respelled`, `gezi.egraph.Respelling`), the respelled
  * fillings over the instruction's fillings. The nodes of the children are
  * those adding them to the final graph finds, without making a node.
  *
  * Purpose: catch `instructionAdded` filing a child's node in the wrong
  * position, a noinline instruction expanded, a thunk held in a spelling other
  * than the front end's, or two terms given one node.
  */
class InstructionAddedLawTest extends GeneratedProperties:

  private type Term = StandInStorages.Term

  /** The instruction's layer in the front end's spelling: the terms it is over,
    * and the layer over the nodes those terms are given. A respelled thunk's
    * fillings are the instances of the respelling's codes over the
    * instruction's fillings (`NativeSpecializer.instance`).
    */
  private final case class SpelledLayer(
      children: Vector[Term],
      over: (Term => Int) => LayerWith[Int, Term]
  )

  private def spelledLayer(
      store: Store[StandInStorages.type],
      instruction: Term
  ): SpelledLayer =
    def unrespelled: SpelledLayer =
      val layer = store.expanded(instruction)
      SpelledLayer(layer.children, nodeOf => layer.map(nodeOf))
    store.expanded(instruction) match
      case Thunk(code, holes, fillings) if holes.nonEmpty =>
        BindingNormalForm.respelled(code, holes, fillings.size) match
          case Some((spelledCode, spelledHoles, spelledFillings)) =>
            val children =
              spelledFillings.map(StandInStorages.instance(_, fillings))
            SpelledLayer(
              children,
              nodeOf => Thunk(spelledCode, spelledHoles, children.map(nodeOf))
            )
          case None => unrespelled
      case _ => unrespelled

  property(
    "each instruction's node holds its layer in the front end's spelling over its children's nodes, one node per layer"
  ) {
    for generated <- StoreGenerators.store.forAll
    yield
      val store = generated.store
      val instructions = generated.instructions
      val (graph, nodes) = instructions.foldLeft(
        (
          EGraph.empty(store, Map.empty, explained = false),
          Map.empty[Term, Int]
        )
      ) { case ((current, found), instruction) =>
        val (next, node) = current.instructionAdded(instruction)
        (next, found.updated(instruction, node))
      }
      val childNodes = instructions
        .flatMap(instruction => spelledLayer(store, instruction).children)
        .distinct
        .map(child =>
          val (again, node) = graph.instructionAdded(child)
          (child, node, again.nodeCount == graph.nodeCount)
        )
      val nodeOf = childNodes.map((child, node, _) => child -> node).toMap
      val found = Result
        .assert(childNodes.forall(_._3))
        .log(s"a child made a node: ${childNodes.filterNot(_._3)}")
      val layersOverNodes = instructions.map(instruction =>
        gezi.ir.Interned.canonicalLayer(
          spelledLayer(store, instruction).over(nodeOf)
        )
      )
      val layerHeld = Result.all(
        instructions.toList.map(instruction =>
          Result.diff(
            graph.layer(nodes(instruction)),
            gezi.ir.Interned.canonicalLayer(
              spelledLayer(store, instruction).over(nodeOf)
            )
          )(_ eq _)
        )
      )
      val sharing =
        Result.diff(nodes.values.toSet.size, layersOverNodes.distinct.size)(
          _ == _
        )
      found.and(layerHeld).and(sharing)
  }
