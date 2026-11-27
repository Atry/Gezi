package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.GeneratedStore
import com.yang_bo.gezi.generatedinputs.OrientationGenerators
import com.yang_bo.gezi.generatedinputs.StoreGenerators
import com.yang_bo.gezi.ir.{Apply, Choice, Parallel, Thunk}

/** The matches the index's program finds, against a naive matching that tries
  * every pattern at every class.
  */
class IndexedMatchingTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with GeneratedProperties:

  private type C = StandInStorages.type

  private given StandInStorages.type = StandInStorages

  /** Catches a seed, a witness, a shared step of a tree or a signature lookup
    * that loses a match or finds a false one: on a saturated graph, the
    * instances (orientation, root class, classes of the essential
    * metavariables) the program finds from every node under every key are those
    * the naive matching finds, as sets.
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
    yield instancesAgree(
      generated,
      orientations,
      StopSignal.completedWith(stopped)
    )
  }

  /** On the graph saturated from every instruction of the store, the instances
    * (orientation, root class, classes of the essential metavariables) the
    * program finds from every node under every key are those the naive matching
    * finds, as sets.
    */
  private def instancesAgree(
      generated: GeneratedStore,
      orientations: Vector[Orientation[C]],
      stop: StopSignal
  ): Result =
    val store = generated.store
    val program = Indexing.program(orientations, generated.codes)
    val instructions = generated.instructions
    val initial = Saturation.initialGraph(
      store,
      Orientations.headArityBounds(orientations),
      Vector.empty,
      explained = false
    )
    val (withInstructions, _) = Saturation.inputsAdded(initial, instructions)
    val compiled = ClosureCompilation.compiled(program)
    val (graph, _) = Saturation.saturated(
      program,
      compiled,
      BuiltInRule.beforeOptIn,
      withInstructions,
      budget = 40,
      stop
    )
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
      bindings <- NaiveMatching.matches(
        graph,
        orientation.matched,
        root,
        Map.empty
      )
    yield (
      orientation.index,
      root,
      orientation.essential.map(bindings.get)
    )).toSet
    Result.diff(found, naive)(_ == _)
