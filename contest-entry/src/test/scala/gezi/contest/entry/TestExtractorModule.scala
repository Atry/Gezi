package gezi.contest.entry

import java.nio.file.Path
import gezi.egraph.EGraph
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.jit.NativeBackend
import gezi.narrowblocks.LemmaRoundsResult
import gezi.narrowblocks.LemmaRoute
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.narrowblocks.NarrowBlockRoute
import gezi.narrowblocks.PreparedLemmaCompilation
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.Extractor
import gezi.strategies.JointReading
import gezi.strategies.NormalityModule

/** The extractor module of contest-entry's tests (`ExtractorModuleLawTest`),
  * registered with `java.util.ServiceLoader` in the tests' resources: its
  * selector is the one field of tests/extractor_module_fixtures/test_extractor,
  * and its extraction and route are the framework's narrow blocks
  * (`NarrowBlockExtractor` of `LemmaRoute`'s modules, with the measured
  * bounds `JointReading.measured`, and `LemmaRoute`), each carrying the
  * parameter the entry wrote, a tuple of one integer the module reads by
  * structure, and the inputs the framework gave, so that a test sees which
  * parameters and inputs reached each.
  */
final class TestExtractorModule extends ExtractorModule:

  def selectorFile: Path = Path.of("tests", "extractor_module_fixtures", "test_extractor.lambdalattice")

  /** The framework's narrow blocks' extraction over the inputs' natives,
    * carrying the integer the parameters' one field holds and the inputs.
    * Throws `EntryDataError` for parameters that are no tuple of one integer.
    */
  def extractor[C <: NativeSpecializer & Singleton](parameters: Configured[NoFacts.type], inputs: ExtractorModuleInputs[C]): Extractor[C] =
    ParameterCarryingExtractor(
      TestModuleParameters.integer("extractor", parameters)(using NoFacts),
      inputs,
      NarrowBlockExtractor(LemmaRoute.extractorModules(inputs.natives, inputs.configuration), JointReading.measured)
    )

  /** The framework's route, carrying the integer the parameters' one field
    * holds. Throws `EntryDataError` for parameters that are no tuple of one
    * integer.
    */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute =
    ParameterCarryingRoute(TestModuleParameters.integer("extractor", parameters)(using NoFacts), LemmaRoute)

/** The framework's extraction with the parameter a module read and the
  * inputs the framework gave it: every call is the framework extraction's.
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

/** The framework's route with the parameter a module read: every call is the framework route's. */
final case class ParameterCarryingRoute(parameter: BigInt, framework: NarrowBlockRoute) extends NarrowBlockRoute:

  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] = framework.extractorModules(natives, configuration)

  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C] =
    framework.compiledRounds(index, rounds, natives, encoding, program, explained, stop)
