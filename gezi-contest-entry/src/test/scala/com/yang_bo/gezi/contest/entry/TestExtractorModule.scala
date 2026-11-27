package com.yang_bo.gezi.contest.entry

import java.nio.file.Path
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.jit.NativeBackend
import com.yang_bo.gezi.narrowblocks.LemmaRoundsResult
import com.yang_bo.gezi.narrowblocks.LemmaRoute
import com.yang_bo.gezi.narrowblocks.NarrowBlockExtractor
import com.yang_bo.gezi.narrowblocks.NarrowBlockRoute
import com.yang_bo.gezi.narrowblocks.PreparedLemmaCompilation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.strategies.Extractor
import com.yang_bo.gezi.strategies.JointReading
import com.yang_bo.gezi.strategies.NormalityModule

/** The extractor module of contest-entry's tests (`ExtractorModuleLawTest`),
  * registered with `java.util.ServiceLoader` in the tests' resources: its
  * selector is the one field of tests/extractor_module_fixtures/test_extractor,
  * and its extraction and route are the framework's narrow blocks
  * (`NarrowBlockExtractor` of `LemmaRoute`'s modules, with the measured bounds
  * `JointReading.measured`, and `LemmaRoute`), each carrying the parameter the
  * entry wrote, a tuple of one integer the module reads by structure, and the
  * inputs the framework gave, so that a test sees which parameters and inputs
  * reached each.
  */
final class TestExtractorModule extends ExtractorModule:

  def selectorFile: Path = Path.of(
    "tests",
    "extractor_module_fixtures",
    "test_extractor.lambdalattice"
  )

  /** The framework's narrow blocks' extraction over the inputs' natives,
    * carrying the integer the parameters' one field holds and the inputs.
    * Throws `EntryDataError` for parameters that are no tuple of one integer.
    */
  def extractor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExtractorModuleInputs[C]
  ): Extractor[C] =
    ParameterCarryingExtractor(
      TestModuleParameters.integer("extractor", parameters)(using NoFacts),
      inputs,
      NarrowBlockExtractor(
        LemmaRoute.extractorModules(inputs.natives, inputs.configuration),
        JointReading.measured
      )
    )

  /** The framework's route, carrying the integer the parameters' one field
    * holds. Throws `EntryDataError` for parameters that are no tuple of one
    * integer.
    */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute =
    ParameterCarryingRoute(
      TestModuleParameters.integer("extractor", parameters)(using NoFacts),
      LemmaRoute
    )

/** The framework's extraction with the parameter a module read and the inputs
  * the framework gave it: every call is the framework extraction's.
  */
final case class ParameterCarryingExtractor[C <: NativeSpecializer & Singleton](
    parameter: BigInt,
    inputs: ExtractorModuleInputs[C],
    framework: Extractor[C]
) extends Extractor[C]:

  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]] =
    framework.extracted(index, graph, inputNodes, inputs, stop)

/** The framework's route with the parameter a module read: every call is the
  * framework route's.
  */
final case class ParameterCarryingRoute(
    parameter: BigInt,
    framework: NarrowBlockRoute
) extends NarrowBlockRoute:

  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: com.yang_bo.gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] =
    framework.extractorModules(natives, configuration)

  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: com.yang_bo.gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C] =
    framework.compiledRounds(
      index,
      rounds,
      natives,
      encoding,
      program,
      explained,
      stop
    )
