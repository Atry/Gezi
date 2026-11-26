package gezi.programfamilies

import gezi.ir.{Configured, NoFacts}
import java.nio.file.Path
import gezi.standardlibrary.StandardLibrary
import gezi.lemmaencoding.baseline.BaselineLemmaEncoding
import gezi.frontend.Defunctionalization
import gezi.frontend.Occurrences
import gezi.frontend.OccurrenceMarkers
import gezi.backendcomparison.Compiled
import gezi.backendcomparison.FixedPoint
import gezi.backendcomparison.FixedPointForm
import gezi.backendcomparison.RunInput
import gezi.orientation.CompiledOrientations
import gezi.orientation.LemmaSides
import gezi.orientation.OrientationCompilation
import gezi.saturation.End
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.knowledgereading.KnowledgeReading
import gezi.ir.Value

/** The configuration of the terms here: no facts. */
private given fixedPointRunsNoFacts: NoFacts.type = NoFacts

/** A configuration compiled once for all its items: the library of its
  * knowledge, the lemmas its knowledge `enabled` writes, the orientations
  * compiled from them, and the markers of the occurrence tagging when the
  * library declares the roles of `occurrence(Role)`.
  */
final case class CompiledConfiguration(
    configuration: Configuration,
    library: StandardLibrary,
    enabledLemmas: Vector[LemmaIdentifier],
    orientations: CompiledOrientations[NoFacts.type],
    occurrenceMarkers: Option[OccurrenceMarkers]
)

/** An item's input: the program's instruction, and the run's input with the
  * numbering of the fixtures (`ExportedNumbering`).
  */
final case class ItemInput(inputInstruction: Configured[NoFacts.type], exported: ExportedInput):
  def runInput: RunInput[NoFacts.type] = exported.runInput

/** An item's run to its fixed point: how it ended and the form of the
  * fixed point.
  */
final case class ItemRun(item: Item, end: End, form: FixedPointForm):

  /** The item's line in a file of fixed points (`FixedPoint.line`). */
  def line(configuration: String): String = FixedPoint.line(configuration, item.name, end, form)

/** The runs of the configurations' items, as the Prolog exporter of the
  * fixtures ran them in its mode
  * `fixtures`: the library compiled (`saturation_runs:library_compiled/1`),
  * the orientations of the enabled lemmas compiled (`orientations_compiled/2`),
  * the program put through the front end with the occurrence tagging
  * (`saturation_runs:program_instruction/2`) and interned
  * (`instruction_interned/2`), the graph of the pattern instructions and the
  * input built and saturated with the configuration's budget, and the form
  * of the fixed point computed. It names no lemma and no combinator: the
  * names it reads are the items' programs' and the knowledge modules'.
  */
object FixedPointRuns:

  /** The configuration's library compiled from the first field, the
    * knowledge, of its fixture file's tuple (`Configuration.knowledgeFile`,
    * `λs. s knowledge enabled`), with no backend, and the orientations of the
    * lemmas its second field, the enabled knowledge, writes: the file read by
    * projection off Gezi's directory, the root of the build, under the
    * compilation's reading state, then the library and the lemmas threaded
    * after it.
    */
  def compiled(configuration: Configuration, buildRoot: Path): CompiledConfiguration =
    val (group, afterEntry) = StandardLibrary.entryGroup(
      StandardLibrary.entryTerm(buildRoot, buildRoot.resolve(configuration.knowledgeFile), KnowledgeReading.compilationState)
    )
    val (fields, afterFields) = KnowledgeReading.run(KnowledgeReading.fields(group, 2), StandardLibrary.memberReadingLimit, afterEntry)
    val Vector(knowledge, enabledKnowledge) = (fields.map(KnowledgeReading.term(_, Set.empty)): @unchecked)
    val (library, afterLibrary) = StandardLibrary.compiled(knowledge, Vector.empty, afterFields)
    val (enabled, _) = library.lemmas(enabledKnowledge, afterLibrary)
    val lemmas = library.index
      .enabledEquations(enabled)
      .map(BaselineLemmaEncoding.encoded(library.index, _))
    val orientations = OrientationCompilation.compiled(
      lemmas.map(lemma => LemmaSides(lemma.lemma, lemma.metavariables, lemma.left, lemma.right)),
      Store(library.index.noinline, gezi.ir.TermConstruction(gezi.ir.NoFacts))
    )
    CompiledConfiguration(
      configuration,
      library,
      enabled,
      orientations,
      library.index.occurrenceMarkers
    )

  /** The item's program through the front end: its de Bruijn term, tagged
    * when the library declares the occurrence roles, defunctionalized and
    * interned; and the run's input in the numbering of the fixtures.
    */
  def input(compiled: CompiledConfiguration, item: Item): ItemInput =
    val term = item.program.deBruijnTerm(Map.empty)
    val tagged = compiled.occurrenceMarkers match
      case None          => term
      case Some(markers) => Occurrences.tagged[NoFacts.type](term, markers)
    val inputInstruction = Defunctionalization.thunkInstruction(tagged)(using gezi.ir.NoFacts)
    val exported = ExportedNumbering.renumbered(
      compiled.library.index.noinline,
      compiled.orientations.orientations,
      compiled.orientations.patternInstructions,
      Vector(inputInstruction),
      compiled.configuration.budget
    )
    ItemInput(inputInstruction, exported)

  /** The item saturated and the form of its fixed point, its constants in
    * the numbering of the fixtures.
    */
  def run(compiled: CompiledConfiguration, item: Item): ItemRun =
    val exported = input(compiled, item).exported
    val (projection, end) = FixedPoint.saturatedProjection(Compiled.of(exported.runInput))
    ItemRun(item, end, FixedPoint.form(projection, exported.constantNumbers(projection)))
