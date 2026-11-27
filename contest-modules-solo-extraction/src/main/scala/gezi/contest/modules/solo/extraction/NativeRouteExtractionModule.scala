package gezi.contest.modules.solo.extraction

import java.nio.file.Path

import scala.util.chaining.scalaUtilChainingOps

import gezi.contest.entry.EntryDataError
import gezi.contest.entry.ExtractorModule
import gezi.contest.entry.ExtractorModuleInputs
import gezi.jit.NativeBackend
import gezi.jit.StandardRefinement
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.narrowblocks.LemmaRoundsResult
import gezi.narrowblocks.LemmaRoute
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.narrowblocks.NarrowBlockRoute
import gezi.narrowblocks.PreparedLemmaCompilation
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.Compression
import gezi.strategies.Extractor
import gezi.strategies.JointReading
import gezi.strategies.NormalityModule
import gezi.strategies.SpecializationAttraction
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Value}
import gezi.weakhead.ReadingConfiguration

/** The extractor module of the native route's extraction: the lemma rounds of
  * `gezi.narrowblocks.LemmaRoute`, their last round extracted by the native
  * route's modules (`SpecializationAttraction`, then `Compression`, the modules
  * `gezi.strategies.NativeRouteCompilation.extraction` names), and the
  * extracted program refined as the JIT's native route refines a schedule's
  * output (`gezi.jit.StandardRefinement`). The refinement writes each
  * specialization choice the type check put in the program, `f (x ∥ T) ∥ S + f
  * x`, as the application of f to a fallback point, `f (x + (x ∥ T))`, which
  * the JIT reads by checking x's domain at run time and calling the native
  * bound to f where x is decoded (`gezi.jit.Jit`, fallback points). The route's
  * narrow blocks extraction keeps no typed version: its modules
  * (`gezi.narrowblocks.LemmaCompilation.extractorModules`) do not attract
  * specializations, and the absorbing choices of the judgments are dropped. The
  * parameters are a tuple of two fields, `λs. s enumeration whole`, the joint
  * enumeration's bound and the whole fold's bound of the thunks' candidates
  * (`JointReading`), a positive and a non-negative integer of 64 bits, the
  * fields the framework's `narrow_block` takes.
  */
final class NativeRouteExtractionModule extends ExtractorModule:

  def selectorFile: Path =
    Path.of("corpora", "modules", "solo_native_route_extraction.lambdalattice")

  /** The narrow blocks' extractor over the native route's modules. Throws
    * `EntryDataError` for other parameters.
    */
  def extractor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExtractorModuleInputs[C]
  ): Extractor[C] =
    NarrowBlockExtractor(
      NativeRoute.extractorModules(inputs.natives, inputs.configuration),
      NativeRouteExtractionModule.read(parameters)
    )

  /** The native route. Throws `EntryDataError` for other parameters. */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute =
    NativeRouteExtractionModule.read(parameters).pipe(_ => NativeRoute)

object NativeRouteExtractionModule:

  /** The evaluator steps reading the parameters may take: a tuple of two
    * integers of at most 64 bits, the limit `RememberingExtractionModule` reads
    * its parameters within.
    */
  val parametersReadingLimit: Long =
    RememberingExtractionModule.parametersReadingLimit

  /** The bounds of the joint reading the parameters give. Throws
    * `EntryDataError` for other parameters.
    */
  def read(parameters: Configured[NoFacts.type]): JointReading =
    given NoFacts.type = NoFacts
    val (enumeration, whole) =
      try
        KnowledgeReading.run(
          KnowledgeReading.fields(Value.of(parameters), 2).flatMap {
            case Vector(enumeration, whole) =>
              for
                enumerationRead <- KnowledgeReading.integer(enumeration)
                wholeRead <- KnowledgeReading.integer(whole)
              yield (enumerationRead, wholeRead)
            case fields =>
              throw EntryDataError(
                s"the native route extraction's parameters have ${fields.size} fields, not 2"
              )
          },
          parametersReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          throw EntryDataError(
            s"the native route extraction's parameters: $reason"
          )
    if enumeration <= 0 || !enumeration.isValidLong || whole < 0 || !whole.isValidLong
    then
      throw EntryDataError(
        s"the native route extraction's bounds are $enumeration and $whole, not a positive and a non-negative integer of 64 bits"
      )
    JointReading(enumeration.toLong, whole.toLong)

/** The native route: `LemmaRoute`'s rounds and blocks, the last round extracted
  * by the native route's modules, and the program it gives refined under the
  * library's backend facts.
  */
object NativeRoute extends NarrowBlockRoute:

  /** The native route's extraction modules: specializations first, then the
    * size. The natives are `NarrowBlockRoute`'s parameter, which the narrow
    * blocks' order reads; these modules read none.
    */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] =
    Vector(SpecializationAttraction.at[C], Compression.at[C])

  def compiledRounds[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      rounds: Vector[PreparedLemmaCompilation[C]],
      natives: NativeBackend,
      encoding: gezi.jit.StorageEncoding & C,
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): LemmaRoundsResult[C] =
    val result = LemmaRoute.compiledRounds(
      index,
      rounds,
      natives,
      encoding,
      program,
      explained,
      stop
    )
    // The capability the rounds wrote back with: the refinement builds under the same configuration, the encoding's.
    given gezi.ir.StorageAccess = rounds.lastOption
      .map(_.saturator.options.construction.storageAccess)
      .getOrElse(
        throw IllegalStateException("the native route compiles no round")
      )
    result.copy(
      program = result.program.map(StandardRefinement.refined(encoding, _)),
      extracted = result.extracted.map(StandardRefinement.refined(encoding, _))
    )
