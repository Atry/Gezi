package gezi.narrowblocks

import gezi.ir.Instruction
import gezi.jit.DeclaredFamilies
import gezi.jit.NativeBackend
import gezi.standardlibrary.JvmTypeName
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.Codecs
import gezi.egraph.EGraph
import gezi.extraction.CountedExtraction
import gezi.egraph.MemoRetention
import gezi.strategies.Compression
import gezi.strategies.Extractor
import gezi.strategies.FixpointEgraph
import gezi.strategies.HigherOrderSaturator
import gezi.strategies.JointReading
import gezi.strategies.LocalExtraction
import gezi.strategies.ModuleCostModel
import gezi.strategies.NormalityModule
import gezi.strategies.TermOrder
import gezi.strategies.TermReading
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.Property
import gezi.strategies.SaturationOptions

/** The lemma compilation's round:
  * the round's program saturated by `saturator`, whose options hold the
  * round's lemmas, by identity (those of the round's knowledge term,
  * `StandardLibrary.lemmas`), its built-in rules and its budget, and the
  * program extracted by `extractor`. Both are the implementations the
  * entry's data chooses for the round, mapped by `gezi.contest.entry.Defaults`.
  * Every decision is
  * the lemmas' matching and the extractor's order. `route` is the narrow
  * blocks' implementation the round's extractor data chooses; the last
  * round's route runs the rounds (`ProgramCompiler.compiledProgram`).
  */
final case class LemmaCompilation(saturator: HigherOrderSaturator, extractor: Extractor, route: NarrowBlockRoute):

  /** The instances the round's saturation may add, its options' budget. */
  def budget: Int = saturator.options.budget

  /** The round's saturation of the program, its graph recording the terms
    * made when `explained` (a run whose proof is wanted).
    */
  def saturated(index: StandardLibraryIndex, program: Instruction, explained: Boolean, stop: StopSignal): Run =
    saturator.saturated(index, Vector(program), explained, stop)

  /** The program extracted from the round's graph. */
  def extracted(index: StandardLibraryIndex, program: Instruction, run: Run, stop: StopSignal): Instruction =
    extractor.extracted(index, run.graph, run.inputNodes, Vector(program), stop) match
      case Vector(output) => output
      case outputs        => throw IllegalStateException(s"one output for one input, not ${outputs.size}")

  /** The compilation with its round compiled once for the index
    * (`HigherOrderSaturator.prepared`), to be kept by an entry and used for
    * every program it reads under that index.
    */
  def prepared(index: StandardLibraryIndex): PreparedLemmaCompilation =
    PreparedLemmaCompilation(this, index, saturator.prepared(index))

/** A lemma compilation whose round is compiled once for one index: the same
  * saturation and extraction as `compilation`'s, without compiling the
  * lemmas again for each program.
  */
final case class PreparedLemmaCompilation(
    compilation: LemmaCompilation,
    index: StandardLibraryIndex,
    saturator: HigherOrderSaturator
):

  /** The round's saturation of the program, its graph recording the terms
    * made when `explained` (a run whose proof is wanted).
    */
  def saturated(program: Instruction, explained: Boolean, stop: StopSignal): Run =
    saturator.saturated(index, Vector(program), explained, stop)

  /** The round's compiled lemmas and orientations, what `prepared` built. */
  def compiledRound: FixpointEgraph.CompiledRound =
    saturator.round.getOrElse(throw IllegalStateException("a prepared lemma compilation has its round compiled"))

  /** The round's saturation of the program on the graph the shared rounds
    * before it left (`HigherOrderSaturator.begunOn`): at most the
    * compilation's budget of instances beyond those the graph counts, to
    * the round's fixed point.
    */
  def saturatedOn(graph: EGraph, shared: Vector[FixpointEgraph.CompiledRound], program: Instruction, stop: StopSignal): Run =
    saturator.begunOn(index, graph, shared, Vector(program), compilation.budget, stop).run

  /** The program extracted from the round's graph. */
  def extracted(program: Instruction, run: Run, stop: StopSignal): Instruction =
    compilation.extracted(index, program, run, stop)

object LemmaCompilation:

  /** The modules of the round's extraction and of its write-backs: the
    * narrow blocks over the natives first, then the size.
    */
  def extractorModules(natives: NativeBackend): Vector[NormalityModule] = Vector(NarrowBlockOrder(natives), Compression)

  /** The saturation of the lemma compilation's round under the options,
    * `HigherOrderSaturator`; with `opening`, every closure a lemma may match
    * opened and its body written back, spelled by `modules` (a route's
    * `extractorModules`), the spellings of one pass kept from body to body
    * as `writeBackSpellings` says, the closures chosen by `openingChoice`
    * (`gezi.saturation.OpeningCriterionChoice`).
    */
  def higherOrderSaturator(
      options: SaturationOptions,
      opening: Boolean,
      writeBackSpellings: MemoRetention,
      modules: Vector[NormalityModule],
      openingChoice: gezi.saturation.OpeningCriterionChoice
  ): HigherOrderSaturator =
    HigherOrderSaturator(
      options,
      Option.when(opening)(LocalExtraction(modules, NarrowBlockExtractor.productionNames, writeBackSpellings)),
      None,
      openingChoice
    )

/** The baseline's extraction (`CountedExtractor`) under the modules given,
  * its productions the library's noinline defines and the names the narrow
  * blocks read as the backend's (`NarrowBlocks.nameKind`): the defines a
  * `native` declaration binds, those whose `combinator_property` is a
  * native specialization, and the fixed point
  * combinator by value. So a filter's criterion, `binary_set p`, is spelled
  * as its name and not as its body; which spelling a class takes is still
  * the modules' order. Its cost model reads a thunk's jointly read fillings
  * as `jointReading` says.
  */
final case class NarrowBlockExtractor(modules: Vector[NormalityModule], jointReading: JointReading) extends Extractor:

  TermOrder.extractionModulesChecked(modules)

  def extracted(
      index: StandardLibraryIndex,
      graph: EGraph,
      inputNodes: Vector[Int],
      inputs: Vector[Instruction],
      stop: StopSignal
  ): Vector[Instruction] =
    CountedExtraction.fixed(graph, NarrowBlockExtractor.productionNames(index), ModuleCostModel(modules, TermReading(index), stop, jointReading), stop) match
      case Some(extracted) => FixpointEgraph.outputsSpelled(extracted, inputNodes.map(graph.root), inputs)
      case None            => inputs

/** The productions of the narrow blocks' extraction. */
object NarrowBlockExtractor:

  /** The library terms bound to natives: by `native` declarations, and the
    * constructors the `data_family` of a type with a `native_specialization`
    * lists (`Codecs.declaredConstructors`) or of a family declared by facts
    * (`DeclaredFamilies.constructorTerms`).
    */
  def boundTerms(index: StandardLibraryIndex): Vector[Instruction] =
    index.nativeBound.map(_.instruction) ++ Codecs.declaredConstructors(index).flatMap(_._2) ++
      DeclaredFamilies.constructorTerms(index).flatMap(_._2)

  /** The library's noinline defines and the backend's names: the criteria
    * among them those with a `native_specialization` and those of the
    * families declared by facts (`jvm_type(generic)`), whose criterion is
    * their identity.
    */
  def productionNames(index: StandardLibraryIndex): Set[Instruction] =
    val backendNames = boundTerms(index) ++ index.combinatorProperties.collect {
      case CombinatorProperty(instruction, Property.NativeSpecialization(_))      => instruction
      case CombinatorProperty(instruction, Property.JvmType(JvmTypeName.Generic)) => instruction
    } :+ NarrowBlocks.fixpointByValue
    // TODO (https://github.com/Atry/private-overlay/issues/1517):
    // the backend's names become the round's `leaves`.
    FixpointEgraph.productionNames(index) ++ backendNames
