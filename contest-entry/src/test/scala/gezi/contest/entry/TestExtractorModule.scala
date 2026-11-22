package gezi.contest.entry

import java.nio.file.Path
import gezi.egraph.EGraph
import gezi.ir.Instruction
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
  def extractor(parameters: Instruction, inputs: ExtractorModuleInputs): Extractor =
    ParameterCarryingExtractor(
      TestModuleParameters.integer("extractor", parameters),
      inputs,
      NarrowBlockExtractor(LemmaRoute.extractorModules(inputs.natives), JointReading.measured)
    )

  /** The framework's route, carrying the integer the parameters' one field
    * holds and the inputs. Throws `EntryDataError` for parameters that are no
    * tuple of one integer.
    */
  def route(parameters: Instruction, inputs: ExtractorModuleInputs): NarrowBlockRoute =
    ParameterCarryingRoute(TestModuleParameters.integer("extractor", parameters), inputs, LemmaRoute)

/** The framework's extraction with the parameter a module read and the
  * inputs the framework gave it: every call is the framework extraction's.
  */
final case class ParameterCarryingExtractor(parameter: BigInt, inputs: ExtractorModuleInputs, framework: Extractor) extends Extractor:

  def extracted(
      index: StandardLibraryIndex,
      graph: EGraph,
      inputNodes: Vector[Int],
      inputs: Vector[Instruction],
      stop: StopSignal
  ): Vector[Instruction] =
    framework.extracted(index, graph, inputNodes, inputs, stop)

/** The framework's route with the parameter a module read and the inputs the
  * framework gave it: every call is the framework route's.
  */
final case class ParameterCarryingRoute(parameter: BigInt, inputs: ExtractorModuleInputs, framework: NarrowBlockRoute)
    extends NarrowBlockRoute:

  def extractorModules(natives: NativeBackend): Vector[NormalityModule] = framework.extractorModules(natives)

  def compiledRounds(
      index: StandardLibraryIndex,
      rounds: Vector[PreparedLemmaCompilation],
      natives: NativeBackend,
      program: Instruction,
      explained: Boolean,
      stop: StopSignal
  ): LemmaRoundsResult =
    framework.compiledRounds(index, rounds, natives, program, explained, stop)
