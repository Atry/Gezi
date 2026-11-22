package gezi.backendcomparison

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import gezi.ematching.closures.ClosureCompilation
import gezi.egraph.EGraph
import gezi.ematching.indexing.Indexing
import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.saturation.Saturation
import gezi.ir.BuiltInRule
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.GeneratedStore
import gezi.generatedinputs.OrientationGenerators
import gezi.generatedinputs.StoreGenerators
import gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The matches the index's program finds, against a naive matching that
  * tries every pattern at every class.
  */
class IndexedMatchingTest extends gezi.generatedinputs.FailFastSuite with GeneratedProperties:

  /** Catches a seed, a witness, a shared step of a tree or a signature
    * lookup that loses a match or finds a false one:
    * on a saturated graph, the instances (orientation, root class, classes of
    * the essential metavariables) the program finds from every node under
    * every key are those the naive matching finds, as sets.
    */
  stoppableProperty(
    "the program finds exactly the instances a naive matching finds",
    // Determined subpatterns below a seed's delta that match are rare in the
    // generated inputs: a lookup of them with its children reversed was caught
    // after 51 to 90 passing inputs in five runs (2026-10-31), so the
    // property runs 300.
    _.copy(testLimit = SuccessCount(300))
  ) { stopped =>
    for
      generated <- StoreGenerators.store.forAll
      orientations <- OrientationGenerators.orientationsOver(generated).forAll
    yield instancesAgree(generated, orientations, StopSignal.completedWith(stopped))
  }

  /** On the graph saturated from every instruction of the store, the instances
    * (orientation, root class, classes of the essential metavariables) the
    * program finds from every node under every key are those the naive
    * matching finds, as sets.
    */
  private def instancesAgree(generated: GeneratedStore, orientations: Vector[Orientation], stop: StopSignal): Result =
    val store = generated.store
    val program = Indexing.program(orientations, generated.codes)
    val instructions = generated.instructions
    val initial = Saturation.initialGraph(store, Orientations.headArityBounds(orientations), Vector.empty, explained = false)
    val (withInstructions, _) = Saturation.inputsAdded(initial, instructions)
    val compiled = ClosureCompilation.compiled(program)
    val (graph, _) = Saturation.saturated(program, compiled, BuiltInRule.all, withInstructions, budget = 40, stop)
    val nodes = graph.liveNodes
    val found = (for
      (kind, key) <- program.seeds.keySet.toVector
      node <- nodes
      matched <- compiled.matches(kind, key, graph, node.node).found
    yield (
      matched.orientation,
      graph.root(matched.root),
      orientations(matched.orientation).essential.map(index =>
        matched.bindings(index).map(graph.root)
      )
    )).toSet
    val naive = (for
      orientation <- orientations
      root <- nodes.map(_.root).distinct
      bindings <- naiveMatches(graph, orientation.matched, root, Map.empty)
    yield (orientation.index, root, orientation.essential.map(bindings.get))).toSet
    Result.diff(found, naive)(_ == _)

  /** The bindings of the metavariables, extending the given ones, under
    * which the class has the pattern: a metavariable is its class, a lambda
    * pattern a class with a closure state, an instruction the class of its node,
    * and a layer a live node of the class with that layer over classes that
    * have the children's patterns.
    */
  private def naiveMatches(
      graph: EGraph,
      pattern: Pattern,
      root: Int,
      bindings: Map[Int, Int]
  ): Vector[Map[Int, Int]] = pattern match
    case Pattern.Metavariable(index) =>
      bindings.get(index) match
        case Some(bound) => if bound == root then Vector(bindings) else Vector.empty
        case None        => Vector(bindings.updated(index, root))
    case Pattern.Closure(index) =>
      if graph.hasClosure(root) then
        naiveMatches(graph, Pattern.Metavariable(index), root, bindings)
      else Vector.empty
    case Pattern.InstructionReference(instruction) =>
      if graph.instructionNode(instruction).exists(graph.root(_) == root) then Vector(bindings)
      else Vector.empty
    case compound =>
      graph.liveNodes
        .filter(node => node.root == root && sameShape(compound, node.layer))
        .flatMap(node =>
          compound.children.zip(node.layer.children).foldLeft(Vector(bindings)) {
            case (gathered, (child, childRoot)) =>
              gathered.flatMap(naiveMatches(graph, child, childRoot, _))
          }
        )

  private def sameShape(pattern: Pattern, layer: Layer[Int]): Boolean =
    (pattern, layer) match
      case (Pattern.Apply(_, _), Apply(_, _))       => true
      case (Pattern.Parallel(_, _), Parallel(_, _)) => true
      case (Pattern.Choice(_, _), Choice(_, _))     => true
      case (Pattern.Thunk(code, holes, fillings), Thunk(layerCode, layerHoles, nodes)) =>
        code == layerCode && holes == layerHoles && fillings.size == nodes.size
      case _ => false
