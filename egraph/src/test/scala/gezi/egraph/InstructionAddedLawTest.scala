package gezi.egraph

import hedgehog.Result
import gezi.ir.BindingNormalForm
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.Store
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Thunk}
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StoreGenerators

/** The law that adding a store's instructions to an empty graph gives each instruction
  * the node of its layer in the front end's spelling over the nodes of that
  * layer's children, one node per distinct such layer, on generated stores
  * (`StoreGenerators.store`). An instruction's layer in the front end's spelling
  * is its layer, except for a thunk with holes that the front end spells
  * otherwise, whose layer is its respelling (`BindingNormalForm.respelled`,
  * `gezi.egraph.Respelling`), the respelled
  * fillings over the instruction's fillings. The nodes of the children are those
  * adding them to the final graph finds, without making a node.
  *
  * Purpose: catch `instructionAdded` filing a child's node in the wrong position,
  * a noinline instruction expanded, a thunk held in a spelling other than the
  * front end's, or two terms given one node.
  */
class InstructionAddedLawTest extends GeneratedProperties:

  /** The instruction's layer in the front end's spelling. */
  private def spelledLayer(store: Store, instruction: Instruction): Layer[Instruction] = store.expanded(instruction) match
    case thunk @ Thunk(code, holes, fillings) if holes.nonEmpty =>
      BindingNormalForm.respelled(code, holes, fillings.size) match
        case Some((spelledCode, spelledHoles, spelledFillings)) =>
          Thunk(spelledCode, spelledHoles, spelledFillings.map(BindingNormalForm.placeholdersMapped(_, fillings)(instructionOf)))
        case None => thunk
    case other => other

  /** The instruction of a layer of a respelled filling, which is never a
    * noinline leaf.
    */
  private def instructionOf(layer: Layer[Instruction]): Instruction = layer match
    case application @ Apply(_, _) => Instruction(application)
    case parallel @ Parallel(_, _) => Instruction(parallel)
    case choice @ Choice(_, _)     => Instruction(choice)
    case thunk @ Thunk(_, _, _)    => Instruction(thunk)
    case leaf @ NoinlineLeaf(_)    => throw IllegalStateException(s"a respelled filling's layer is the leaf $leaf")

  property("each instruction's node holds its layer in the front end's spelling over its children's nodes, one node per layer") {
    for generated <- StoreGenerators.store.forAll
    yield
      val store = generated.store
      val instructions = generated.instructions
      val (graph, nodes) = instructions.foldLeft((EGraph.empty(store, Map.empty, explained = false), Map.empty[Instruction, Int])) {
        case ((current, found), instruction) =>
          val (next, node) = current.instructionAdded(instruction)
          (next, found.updated(instruction, node))
      }
      val childNodes = instructions.flatMap(instruction => spelledLayer(store, instruction).children).distinct.map(child =>
        val (again, node) = graph.instructionAdded(child)
        (child, node, again.nodeCount == graph.nodeCount)
      )
      val nodeOf = childNodes.map((child, node, _) => child -> node).toMap
      val found = Result.assert(childNodes.forall(_._3)).log(s"a child made a node: ${childNodes.filterNot(_._3)}")
      val layersOverNodes = instructions.map(instruction => spelledLayer(store, instruction).map(nodeOf))
      val layerHeld = Result.all(
        instructions.toList.map(instruction =>
          Result.diff(graph.layer(nodes(instruction)), spelledLayer(store, instruction).map(nodeOf))(_ == _)
        )
      )
      val sharing = Result.diff(nodes.values.toSet.size, layersOverNodes.distinct.size)(_ == _)
      found.and(layerHeld).and(sharing)
  }
