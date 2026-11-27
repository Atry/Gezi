package com.yang_bo.gezi.programfamilies

import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.saturation.StopSignal
import java.nio.file.Path
import com.yang_bo.gezi.strategies.BaselineModules
import com.yang_bo.gezi.strategies.ExtractedOutputs
import com.yang_bo.gezi.strategies.FixpointEgraph
import com.yang_bo.gezi.strategies.ModuleCostModel
import com.yang_bo.gezi.strategies.NativeRouteCompilation
import com.yang_bo.gezi.strategies.NormalityModule
import com.yang_bo.gezi.strategies.TermOrder
import com.yang_bo.gezi.strategies.TermReading
import com.yang_bo.gezi.frontend.DeBruijnTerm
import com.yang_bo.gezi.frontend.DeBruijnTermOf
import com.yang_bo.gezi.frontend.Defunctionalization
import com.yang_bo.gezi.frontend.Occurrences
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.extraction.CountedExtraction
import com.yang_bo.gezi.extraction.Extraction
import com.yang_bo.gezi.backendcomparison.Compiled
import com.yang_bo.gezi.backendcomparison.RunInput
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.ir.Reachability
import com.yang_bo.gezi.ir.Store
import scala.annotation.tailrec
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer, NoFacts}

/** The configuration of the terms here: no facts. */
private given pipelineNoFacts: NoFacts.type = NoFacts

/** A size family of the two configurations: its configuration and its name.
  */
final case class SizeFamily(configuration: Configuration, family: String):

  /** The family's item of the size. Throws `IllegalArgumentException` for a
    * size the configuration does not build.
    */
  def item(size: Int): Item =
    configuration.items
      .find(item => item.family == family && item.size == size.toString)
      .getOrElse(
        throw IllegalArgumentException(
          s"the family $family has no item of size $size"
        )
      )

/** The program after the front end: the de Bruijn term of its HOAS, the term
  * after the occurrence tagging, and the program's instruction.
  */
final case class FrontEnd(
    untagged: DeBruijnTermOf[Configured[NoFacts.type]],
    tagged: DeBruijnTermOf[Configured[NoFacts.type]],
    inputInstruction: Configured[NoFacts.type]
)

/** An item's saturation: the graph at the End, the End, the nodes the input
  * made when it was added, and the input's node.
  */
final case class Saturated(
    graph: EGraph[NoFacts.type],
    end: End,
    inputNodesMade: Int,
    inputNodes: Vector[Int]
)

/** The deterministic counts of each stage of the pipeline on one item, for the
  * migration's criterion 4 (`CriterionFourTest`). Every count is read off the
  * values the stages return; none is kept in a counter.
  *
  * @param programNodesRead
  *   reading: the nodes of the HOAS program as the conversion reads them, which
  *   are the nodes of its de Bruijn term before the tagging
  * @param deBruijnNodes
  *   front end: the nodes of the de Bruijn term after the occurrence tagging
  * @param layersInterned
  *   front end: the instructions under the program's instruction
  *   (`Reachability.instructionsUnder`) that are not under the library's
  * @param codesInterned
  *   front end: the codes under the program's instruction that are not under
  *   the library's
  * @param libraryLayers
  *   library compilation: the instructions under the orientations' pattern
  *   instructions, where the library's terms a program meets stand
  * @param libraryCodes
  *   library compilation: the codes under those instructions and of the
  *   orientations' patterns (`Indexing.codesMet`)
  * @param orientations
  *   library compilation: the orientations compiled from the enabled lemmas
  * @param seeds
  *   the index: the seeds of the program the index compiled
  * @param programCodes
  *   the index: the codes of that program, the library's and the input's
  * @param betaSteps
  *   saturation: the β steps taken
  * @param entriesRead
  *   saturation: the entries the matching read, R
  * @param instances
  *   saturation: the instances that changed the graph
  * @param matches
  *   saturation: the matches found
  * @param productions
  *   extraction: the productions the extraction reads, the graph's live nodes
  *   but the absorbed choices and the round's leaves whose node is live
  *   (`Extraction.productions`)
  * @param classesEntered
  *   extraction: the classes that have a best entry at the extraction's fixed
  *   point
  * @param productionReads
  *   extraction: the child positions of the productions, each a production
  *   filed as a reader of the class at that position, which the extraction
  *   reads again when that class gains a better entry
  * @param layersSpelled
  *   extraction: the instructions under the output that are not under the
  *   program's instruction or the library's
  */
final case class StageCounts(
    programNodesRead: Long,
    deBruijnNodes: Long,
    layersInterned: Long,
    codesInterned: Long,
    libraryLayers: Long,
    libraryCodes: Long,
    orientations: Long,
    seeds: Long,
    programCodes: Long,
    betaSteps: Long,
    entriesRead: Long,
    instances: Long,
    matches: Long,
    productions: Long,
    classesEntered: Long,
    productionReads: Long,
    layersSpelled: Long
):

  /** Each count with its stage and its name, in the order of the fields. */
  def named: Vector[(String, String, Long)] = Vector(
    ("reading", "program_nodes_read", programNodesRead),
    ("front_end", "de_bruijn_nodes", deBruijnNodes),
    ("front_end", "layers_interned", layersInterned),
    ("front_end", "codes_interned", codesInterned),
    ("library_compilation", "library_layers", libraryLayers),
    ("library_compilation", "library_codes", libraryCodes),
    ("library_compilation", "orientations", orientations),
    ("index", "seeds", seeds),
    ("index", "program_codes", programCodes),
    ("saturation", "beta_steps", betaSteps),
    ("saturation", "entries_read", entriesRead),
    ("saturation", "instances", instances),
    ("saturation", "matches", matches),
    ("extraction", "productions", productions),
    ("extraction", "classes_entered", classesEntered),
    ("extraction", "production_reads", productionReads),
    ("extraction", "layers_spelled", layersSpelled)
  )

/** Gezi's pipeline as the benchmarks run it, split into its stages: the
  * knowledge files read and the library compiled with the orientations of its
  * enabled lemmas (`FixedPointRuns.compiled`), the program through the front
  * end (its HOAS to de Bruijn, the occurrence tagging, the defunctionalization
  * and the interning), the index and the backend compiled over the orientations
  * and the store's codes, the graph saturated to its End, and the output
  * extracted from the graph as a round of the baseline's search strategy
  * extracts it after its saturation (`CountedExtractor`, over
  * `CountedExtraction.fixed`, one round being a saturation followed by an
  * extraction): the cost model of the ordering modules of every round of the
  * native route (`NativeRouteCompilation.extraction`) over the baseline's table
  * of modules, for both configurations. Unlike `FixedPointRuns.input`, the
  * run's input is not numbered: the exporter's numbering only serves the
  * comparison with the fixtures.
  */
object Pipeline:

  /** The eight size families of the two configurations, in the order of the
    * record's tables.
    */
  val sizeFamilies: Vector[SizeFamily] =
    Vector("numeral", "list", "chain", "nested", "tuple").map(
      SizeFamily(Configurations.hindleyMilnerBaseline, _)
    ) ++
      Vector("numerals", "lists", "folds").map(
        SizeFamily(Configurations.costComparison, _)
      )

  /** The sizes of the timing. */
  val timedSizes: Vector[Int] = Vector(64, 128, 256, 512, 1024)

  /** The sizes of the migration's criterion 4. */
  val countedSizes: Vector[Int] = Vector(64, 128, 512, 1024)

  /** The configuration's fixture file read off the build's root and its library
    * and orientations compiled.
    */
  def libraryCompiled(
      configuration: Configuration,
      buildRoot: Path
  ): CompiledConfiguration =
    FixedPointRuns.compiled(configuration, buildRoot)

  /** The closed program through the front end. */
  def frontEnd(
      compiled: CompiledConfiguration,
      program: ProgramTerm
  ): FrontEnd =
    val untagged = program.deBruijnTerm(Map.empty)
    val tagged = compiled.occurrenceMarkers match
      case None          => untagged
      case Some(markers) => Occurrences.tagged[NoFacts.type](untagged, markers)
    FrontEnd(
      untagged,
      tagged,
      Defunctionalization.thunkInstruction(tagged)(using com.yang_bo.gezi.ir.NoFacts)
    )

  /** The run's input, compiled by the index and the closure backend. */
  def indexCompiled(
      compiled: CompiledConfiguration,
      frontEnd: FrontEnd
  ): Compiled[NoFacts.type] =
    Compiled.of(
      RunInput(
        Store(
          compiled.library.index.noinline,
          com.yang_bo.gezi.ir.TermConstruction(com.yang_bo.gezi.ir.NoFacts)
        ),
        compiled.orientations.orientations,
        compiled.orientations.patternInstructions,
        Vector(frontEnd.inputInstruction),
        compiled.configuration.budget
      )
    )

  /** The graph of the pattern instructions built, the input added and the graph
    * saturated to its End.
    */
  def saturated(item: Compiled[NoFacts.type]): Saturated =
    val input = item.input
    val initial = Saturation.initialGraph(
      input.store,
      item.headArityBounds,
      input.patternInstructions,
      explained = false
    )
    val (withInputs, inputNodes) = Saturation.inputsAdded(initial, input.inputs)
    val (graph, end) =
      Saturation.saturated(
        item.program,
        item.compiled,
        BuiltInRule.beforeOptIn,
        withInputs,
        input.budget,
        StopSignal.NeverStopped
      )
    Saturated(
      graph,
      end,
      withInputs.canonicalNodeCount - initial.canonicalNodeCount,
      inputNodes
    )

  /** The ordering modules of the extraction of every round of the native route,
    * from the baseline's table, checked once.
    */
  val extractionModules: Vector[NormalityModule[NoFacts.type]] =
    TermOrder.extractionModulesChecked(
      TermOrder.modulesChecked(
        BaselineModules.table,
        NativeRouteCompilation.extraction.modules
      )
    )

  /** The output of the saturated graph extracted as the baseline's round
    * extracts it, the program's instruction the one input.
    */
  def extracted(
      compiled: CompiledConfiguration,
      frontEnd: FrontEnd,
      run: Saturated
  ): ExtractedOutputs[NoFacts.type] =
    val index = compiled.library.index
    val model = ModuleCostModel(
      extractionModules,
      TermReading(index),
      StopSignal.NeverStopped
    )
    val extraction = CountedExtraction
      .fixed(
        run.graph,
        FixpointEgraph.productionNames(index),
        model,
        StopSignal.NeverStopped
      )
      .getOrElse(
        throw IllegalStateException(
          "an extraction under NeverStopped was stopped"
        )
      )
    ExtractedOutputs(
      extraction,
      FixpointEgraph.outputsSpelled(
        extraction,
        run.inputNodes.map(run.graph.root),
        Vector(frontEnd.inputInstruction),
        run.graph.store.construction
      )
    )

  /** The counts of every stage on the item, the library compiled once for its
    * configuration.
    */
  def counts(compiled: CompiledConfiguration, item: Item): StageCounts =
    val afterFrontEnd = frontEnd(compiled, item.program)
    val indexed = indexCompiled(compiled, afterFrontEnd)
    val run = saturated(indexed)
    val libraryRoots = compiled.orientations.patternInstructions
    val libraryInstructions = Reachability.instructionsUnder(libraryRoots)
    val libraryCodes =
      Indexing.codesMet(compiled.orientations.orientations, libraryRoots)
    val programInstructions =
      Reachability.instructionsUnder(Vector(afterFrontEnd.inputInstruction))
    val programCodes = Reachability.codesUnder(
      Vector(afterFrontEnd.inputInstruction),
      Vector.empty
    )
    val extraction = extractionCounts(
      extracted(compiled, afterFrontEnd, run),
      programInstructions,
      libraryInstructions
    )
    val (productions, _) =
      Extraction.productions(
        run.graph,
        FixpointEgraph.productionNames(compiled.library.index)
      )
    StageCounts(
      programNodesRead = nodeCount(List(afterFrontEnd.untagged), 0),
      deBruijnNodes = nodeCount(List(afterFrontEnd.tagged), 0),
      layersInterned = programInstructions.diff(libraryInstructions).size,
      codesInterned = programCodes.diff(libraryCodes).size,
      libraryLayers = libraryInstructions.size,
      libraryCodes = libraryCodes.size,
      orientations = compiled.orientations.orientations.size,
      seeds = indexed.program.seeds.values.map(_.size).sum,
      programCodes = indexed.program.codes.size,
      betaSteps = run.graph.betaSteps,
      entriesRead = run.graph.entriesRead,
      instances = run.graph.instances,
      matches = run.graph.matchesFound,
      productions = productions.size,
      classesEntered = extraction.classesEntered,
      productionReads = extraction.productionReads,
      layersSpelled = extraction.layersSpelled
    )

  /** The counts `counts` reads off the extraction, so that the extraction
    * itself is not kept: `counts` then builds the productions again for their
    * number, and holding the extracted classes through that second build ran
    * out of a 352m heap on list at 1024 (curried-partial-function, 2026-11-13,
    * CriterionFourTest).
    */
  private final case class ExtractionCounts(
      classesEntered: Int,
      productionReads: Long,
      layersSpelled: Int
  )

  private def extractionCounts[C <: NativeSpecializer & Singleton](
      extraction: ExtractedOutputs[C],
      programInstructions: Set[Configured[C]],
      libraryInstructions: Set[Configured[C]]
  )(using C): ExtractionCounts =
    ExtractionCounts(
      extraction.extracted.classes.values.count(_.best.isDefined),
      extraction.extracted.classes.values.map(_.readers.size.toLong).sum,
      Reachability
        .instructionsUnder(extraction.outputs)
        .diff(programInstructions)
        .diff(libraryInstructions)
        .size
    )

  /** The nodes of the terms, counted with an explicit stack. */
  @tailrec
  private def nodeCount[Constant](
      pending: List[DeBruijnTermOf[Constant]],
      counted: Int
  ): Int = pending match
    case Nil          => counted
    case term :: rest =>
      val subterms = term match
        case DeBruijnTerm.Variable(_)               => Nil
        case DeBruijnTerm.Constant(_)               => Nil
        case DeBruijnTerm.Free(_)                   => Nil
        case DeBruijnTerm.Lambda(body)              => List(body)
        case DeBruijnTerm.Apply(function, argument) => List(function, argument)
        case DeBruijnTerm.Choice(left, right)       => List(left, right)
        case DeBruijnTerm.Parallel(left, right)     => List(left, right)
      nodeCount(subterms ::: rest, counted + 1)
