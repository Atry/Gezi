package com.yang_bo.gezi.contest.modules.solo.extraction

import java.nio.file.Path
import com.yang_bo.gezi.contest.entry.EntryDataError
import com.yang_bo.gezi.contest.entry.ExtractorModule
import com.yang_bo.gezi.contest.entry.ExtractorModuleInputs
import com.yang_bo.gezi.knowledgereading.KnowledgeReading
import com.yang_bo.gezi.knowledgereading.KnowledgeReadingError
import com.yang_bo.gezi.narrowblocks.LemmaRoute
import com.yang_bo.gezi.narrowblocks.NarrowBlockRoute
import com.yang_bo.gezi.strategies.Extractor
import com.yang_bo.gezi.strategies.JointReading
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, NoFacts, Value}

/** The extractor module of the remembering extraction: the framework's narrow
  * blocks' route the entry chooses, the plain one
  * (`com.yang_bo.gezi.narrowblocks.LemmaRoute`) or the lists' one
  * (`com.yang_bo.gezi.narrowblocks.lists.LemmaRoute`), and its extraction with the
  * candidates remembered within each extraction
  * (`RememberingNarrowBlockExtractor` of that route's modules). The parameters
  * are a tuple of three fields, `λs. s lists enumeration whole`: whether the
  * route is the lists' one, a Scott boolean, and the joint enumeration's bound
  * and the whole fold's bound of the thunks' candidates (`JointReading`), a
  * positive and a non-negative integer of 64 bits, the fields the framework's
  * `narrow_block` and `narrow_list_block` take.
  */
final class RememberingExtractionModule extends ExtractorModule:

  def selectorFile: Path =
    Path.of("corpora", "modules", "solo_remembering_extraction.lambdalattice")

  /** The remembering extraction over the chosen route's modules. Throws
    * `EntryDataError` for other parameters.
    */
  def extractor[C <: NativeSpecializer & Singleton](
      parameters: Configured[NoFacts.type],
      inputs: ExtractorModuleInputs[C]
  ): Extractor[C] =
    val chosen = RememberingExtractionModule.read(parameters)
    RememberingNarrowBlockExtractor(
      chosen.route.extractorModules(inputs.natives, inputs.configuration),
      chosen.jointReading
    )

  /** The chosen route. Throws `EntryDataError` for other parameters. */
  def route(parameters: Configured[NoFacts.type]): NarrowBlockRoute =
    RememberingExtractionModule.read(parameters).route

object RememberingExtractionModule:

  /** The evaluator steps reading the parameters may take: a tuple of a boolean
    * and two integers of at most 64 bits, a handful of steps a bit, the limit
    * the framework's test modules read theirs within
    * (`TestModuleParameters.readingLimit`).
    */
  val parametersReadingLimit: Long = 10000L

  /** What the parameters choose: the route and the bounds of the joint reading.
    */
  final case class Chosen(route: NarrowBlockRoute, jointReading: JointReading)

  /** The parameters read. Throws `EntryDataError` for other parameters. */
  def read(parameters: Configured[NoFacts.type]): Chosen =
    given NoFacts.type = NoFacts
    val (lists, enumeration, whole) =
      try
        KnowledgeReading.run(
          KnowledgeReading.fields(Value.of(parameters), 3).flatMap {
            case Vector(lists, enumeration, whole) =>
              for
                listsRead <- KnowledgeReading.truth(lists)
                enumerationRead <- KnowledgeReading.integer(enumeration)
                wholeRead <- KnowledgeReading.integer(whole)
              yield (listsRead, enumerationRead, wholeRead)
            case fields =>
              throw EntryDataError(
                s"solo's remembering extraction's parameters have ${fields.size} fields, not 3"
              )
          },
          parametersReadingLimit
        )
      catch
        case KnowledgeReadingError(reason) =>
          throw EntryDataError(
            s"solo's remembering extraction's parameters: $reason"
          )
    if enumeration <= 0 || !enumeration.isValidLong || whole < 0 || !whole.isValidLong
    then
      throw EntryDataError(
        s"solo's remembering extraction's bounds are $enumeration and $whole, not a positive and a non-negative integer of 64 bits"
      )
    Chosen(
      if lists then com.yang_bo.gezi.narrowblocks.lists.LemmaRoute else LemmaRoute,
      JointReading(enumeration.toLong, whole.toLong)
    )
