package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.saturation.StopSignal
import hedgehog.Result
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.OrientationGenerators
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.generatedinputs.StoreGenerators

/** The tree of a key's seeds (`Program.trees`) as the closure backend runs it,
  * against the seeds run one by one.
  */
class SeedTreeTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with GeneratedProperties:

  private given StandInStorages.type = StandInStorages

  /** Catches a tree that loses, adds or reorders a match by sharing steps
    * between seeds, or that reads more than the seeds alone do: on a saturated
    * graph, for every key and every node as the delta, the matches of the key
    * are those of its seeds, each compiled alone, concatenated in the seeds'
    * order, and the entries read are at most theirs summed.
    */
  stoppableProperty(
    "a key's tree finds exactly the matches of its seeds run one by one, in their order, reading no more"
  ) { stopped =>
    for
      generated <- StoreGenerators.store.forAll
      orientations <- OrientationGenerators.orientationsOver(generated).forAll
    yield
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
        StopSignal.completedWith(stopped)
      )
      val nodes = (0 until graph.nodeCount).filter(graph.live)
      Result.all(
        program.seeds.toList.flatMap { case ((kind, key), seeds) =>
          val alone = seeds.map(seed =>
            ClosureCompilation.compiled(
              program.copy(seeds = Map((kind, key) -> Vector(seed)))
            )
          )
          nodes.map { node =>
            val together = compiled.matches(kind, key, graph, node)
            val separately = alone.map(_.matches(kind, key, graph, node))
            Result
              .diff(together.found, separately.flatMap(_.found))(_ == _)
              .and(
                Result.diff(
                  together.entriesRead,
                  separately.map(_.entriesRead).sum
                )(_ <= _)
              )
          }
        }
      )
  }
