package gezi.contest.modules.plover.families

import java.nio.file.Path
import gezi.contest.entry.EntryDataError
import gezi.contest.entry.ExtractorModule
import gezi.contest.entry.ExtractorModuleInputs
import gezi.knowledgereading.KnowledgeReading
import gezi.knowledgereading.KnowledgeReadingError
import gezi.narrowblocks.NarrowBlockExtractor
import gezi.narrowblocks.NarrowBlockRoute
import gezi.narrowblocks.lists.DeclaredFamilyRoute
import gezi.strategies.Extractor
import gezi.strategies.JointReading
import gezi.ir.{Configured, NativeSpecializer, NoFacts, Value}

/** The extractor module of the narrow blocks over declared data families: the
  * route `DeclaredFamilyRoute` and the framework's narrow blocks' extraction
  * of that route's modules. The parameters are a tuple of two fields,
  * `λs. s enumeration whole`, the joint enumeration's bound and the whole
  * fold's bound of the thunks' candidates (`JointReading`), a positive and a
  * non-negative integer of 64 bits, the fields `narrow_list_block` takes.
  */
final class DeclaredFamilyExtractionModule extends ExtractorModule:

  def selectorFile: Path = Path.of("corpora", "modules", "plover_declared_families.lambdalattice")

  /** The extraction over the route's modules. Throws `EntryDataError` for
    * other parameters.
    */
  def extractor[C <: NativeSpecializer & Singleton](parameters: Configured[NoFacts.type], inputs: ExtractorModuleInputs[C]): Extractor[C] =
    NarrowBlockExtractor(
      DeclaredFamilyRoute.extractorModules(inputs.natives, inputs.configuration),
      DeclaredFamilyExtractionModule.read(parameters)
    )

  /** The route. Throws `EntryDataError` for other parameters. */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute =
    DeclaredFamilyExtractionModule.read(parameters)
    DeclaredFamilyRoute

object DeclaredFamilyExtractionModule:

  /** The evaluator steps reading the parameters may take: a tuple of two
    * integers of at most 64 bits, a handful of steps a bit, the limit the
    * framework's test modules read theirs within
    * (`TestModuleParameters.readingLimit`).
    */
  val parametersReadingLimit: Long = 10000L

  /** The parameters read. Throws `EntryDataError` for other parameters. */
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
            case fields => throw EntryDataError(s"the declared families' parameters have ${fields.size} fields, not 2")
          },
          parametersReadingLimit
        )
      catch case KnowledgeReadingError(reason) => throw EntryDataError(s"the declared families' parameters: $reason")
    if enumeration <= 0 || !enumeration.isValidLong || whole < 0 || !whole.isValidLong then
      throw EntryDataError(s"the declared families' bounds are $enumeration and $whole, not a positive and a non-negative integer of 64 bits")
    JointReading(enumeration.toLong, whole.toLong)
