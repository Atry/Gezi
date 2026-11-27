package com.yang_bo.gezi.contest.modules.solo.extraction

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.extraction.CountedExtraction
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.narrowblocks.NarrowBlockExtractor
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.Extractor
import com.yang_bo.gezi.strategies.FixpointEgraph
import com.yang_bo.gezi.strategies.JointReading
import com.yang_bo.gezi.strategies.ModuleCost
import com.yang_bo.gezi.strategies.ModuleCostModel
import com.yang_bo.gezi.strategies.NormalityModule
import com.yang_bo.gezi.strategies.TermOrder
import com.yang_bo.gezi.strategies.TermReading

/** The framework's narrow blocks' extraction (`NarrowBlockExtractor`) with its
  * cost model's candidates remembered within each extraction
  * (`RememberingCostModel` over the same `ModuleCostModel`): the same
  * productions, the same model and the same spelling of each input's class, so
  * the same outputs, its candidates computed once for each call's arguments.
  */
final case class RememberingNarrowBlockExtractor[
    C <: NativeSpecializer & Singleton
](modules: Vector[NormalityModule[C]], jointReading: JointReading)
    extends Extractor[C]:

  TermOrder.extractionModulesChecked(modules)

  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]] =
    val model = RememberingCostModel[C, ModuleCost](
      ModuleCostModel(modules, TermReading(index), stop, jointReading),
      stop
    )
    CountedExtraction.fixed(
      graph,
      NarrowBlockExtractor.productionNames(index),
      model,
      stop
    )(using index.specializer) match
      case Some(extracted) =>
        FixpointEgraph.outputsSpelled(
          extracted,
          inputNodes.map(graph.root),
          inputs,
          graph.store.construction
        )(using index.specializer)
      case None => inputs
