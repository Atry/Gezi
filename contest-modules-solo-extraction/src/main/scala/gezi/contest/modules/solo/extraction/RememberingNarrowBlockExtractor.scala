package gezi.contest.modules.solo.extraction

import gezi.egraph.EGraph
import gezi.extraction.CountedExtraction
import gezi.ir.{Configured, NativeSpecializer}
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.Extractor
import gezi.strategies.FixpointEgraph
import gezi.strategies.JointReading
import gezi.strategies.ModuleCost
import gezi.strategies.ModuleCostModel
import gezi.strategies.NormalityModule
import gezi.strategies.TermOrder
import gezi.strategies.TermReading

/** The framework's narrow blocks' extraction (`NarrowBlockExtractor`) with
  * its cost model's candidates remembered within each extraction
  * (`RememberingCostModel` over the same `ModuleCostModel`): the same
  * productions, the same model and the same spelling of each input's class,
  * so the same outputs, its candidates computed once for each call's
  * arguments.
  */
final case class RememberingNarrowBlockExtractor[C <: NativeSpecializer & Singleton](modules: Vector[NormalityModule[C]], jointReading: JointReading)
    extends Extractor[C]:

  TermOrder.extractionModulesChecked(modules)

  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]] =
    val model = RememberingCostModel[C, ModuleCost](ModuleCostModel(modules, TermReading(index), stop, jointReading), stop)
    CountedExtraction.fixed(graph, NarrowBlockExtractor.productionNames(index), model, stop)(using index.specializer) match
      case Some(extracted) => FixpointEgraph.outputsSpelled(extracted, inputNodes.map(graph.root), inputs, graph.store.construction)(using index.specializer)
      case None            => inputs
