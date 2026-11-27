package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.extraction.CountedExtraction
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex

/** The retired baseline extractor (`StandardExtractor`, which reads back with
  * `git show c33817721:lambda_jit/strategies/src/main/scala/lambdajit/strategies/FixpointSearch.scala`)
  * with its fixed point reached by `CountedExtraction`: the same cost model
  * under the ordering modules the options name, the same productions, the same
  * spelling of each input's class (`FixpointEgraph.outputsSpelled`), so the
  * same outputs. The names are checked when the extractor is made, so that an
  * unknown or repeated name throws `TermOrderError` before any saturation. It
  * depends on the framework's interfaces only, so any entry may use it. It
  * began in the module contest-modules-counted-extraction and was moved into
  * the framework on retirement.
  */
final case class CountedExtractor[C <: NativeSpecializer & Singleton](
    options: ExtractionOptions,
    moduleTable: Vector[NormalityModule[C]]
) extends Extractor[C]:

  private val modules = TermOrder.extractionModulesChecked(
    TermOrder.modulesChecked(moduleTable, options.modules)
  )

  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]] =
    given C = graph.store.construction.specializer
    val model = ModuleCostModel[C](modules, TermReading(index), stop)
    CountedExtraction.fixed(
      graph,
      FixpointEgraph.productionNames(index),
      model,
      stop
    ) match
      case Some(extracted) =>
        FixpointEgraph.outputsSpelled(
          extracted,
          inputNodes.map(graph.root),
          inputs,
          graph.store.construction
        )
      case None => inputs
