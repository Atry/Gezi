package gezi.narrowblocks

import scala.annotation.tailrec

import gezi.ir.Thunk
import gezi.ir.Apply
import gezi.ir.Parallel
import gezi.ir.Choice
import gezi.ir.Slot
import gezi.ir.Code
import gezi.jit.DeclaredFamilies
import gezi.jit.NativeBackend
import gezi.standardlibrary.JvmTypeName
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.Codecs
import gezi.egraph.EGraph
import gezi.extraction.CountedExtraction
import gezi.strategies.SpellingRetention
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
import gezi.ir.{Configured, NativeSpecializer, Pure}

/** The lemma compilation's round: the round's program saturated by `saturator`,
  * whose options hold the round's lemmas, by identity (those of the round's
  * knowledge term, `StandardLibrary.lemmas`), its built-in rules and its
  * budget, and the program extracted by `extractor`. Both are the
  * implementations the entry's data chooses for the round, mapped by
  * `gezi.contest.entry.Defaults`. Every decision is the lemmas' matching and
  * the extractor's order. `route` is the narrow blocks' implementation the
  * round's extractor data chooses; the last round's route runs the rounds
  * (`ProgramCompiler.compiledProgram`).
  */
final case class LemmaCompilation[C <: NativeSpecializer & Singleton](
    saturator: HigherOrderSaturator[C],
    extractor: Extractor[C],
    route: NarrowBlockRoute
):

  /** The instances the round's saturation may add, its options' budget. */
  def budget: Int = saturator.options.budget

  /** The round's saturation of the program, its graph recording the terms made
    * when `explained` (a run whose proof is wanted).
    */
  def saturated(
      index: StandardLibraryIndex[C],
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  ): Run[C] =
    saturator.saturated(index, Vector(program), explained, stop)

  /** The program extracted from the round's graph. */
  def extracted(
      index: StandardLibraryIndex[C],
      program: Configured[C],
      run: Run[C],
      stop: StopSignal
  ): Configured[C] =
    extractor.extracted(
      index,
      run.graph,
      run.inputNodes,
      Vector(program),
      stop
    ) match
      case Vector(output) => output
      case outputs        =>
        throw IllegalStateException(
          s"one output for one input, not ${outputs.size}"
        )

  /** The compilation whose round builds the terms it writes back by the
    * construction (`SaturationOptions.construction`): an entry gives every
    * round the one its configuration converts by, so that its rounds and its
    * executor give one term one object.
    */
  def constructedBy(
      construction: gezi.ir.TermConstruction[C]
  ): LemmaCompilation[C] =
    copy(saturator =
      saturator.copy(options =
        saturator.options.copy(construction = construction)
      )
    )

  /** The compilation with its round compiled once for the index
    * (`HigherOrderSaturator.prepared`), to be kept by an entry and used for
    * every program it reads under that index.
    */
  def prepared(index: StandardLibraryIndex[C]): PreparedLemmaCompilation[C] =
    PreparedLemmaCompilation(this, index, saturator.prepared(index))

/** A lemma compilation whose round is compiled once for one index: the same
  * saturation and extraction as `compilation`'s, without compiling the lemmas
  * again for each program.
  *
  * Its budget for a program (`budgetFor`) is the compilation's budget, or, when
  * `instancesPerNode` is given, that many instances for each node of the
  * program's IR graph (`PreparedLemmaCompilation.graphNodes`), never fewer than
  * the compilation's budget: a round that types a program walks it, adding
  * instances in proportion to its nodes, so a budget fixed whatever the program
  * cuts a large one's typing short. The budget stays a safety bound, not a
  * fuel: a round that reaches it ends with `End.BudgetExhausted`, which the
  * entry reports.
  */
final case class PreparedLemmaCompilation[C <: NativeSpecializer & Singleton](
    compilation: LemmaCompilation[C],
    index: StandardLibraryIndex[C],
    saturator: HigherOrderSaturator[C],
    instancesPerNode: Option[Int] = None
):
  instancesPerNode.foreach(instances =>
    require(
      instances > 0,
      s"a round's instances per node are positive: $instances"
    )
  )

  /** The compilation with its budget scaled to each program, `instances` for
    * each node of its IR graph.
    */
  def scaledBy(instances: Int): PreparedLemmaCompilation[C] =
    copy(instancesPerNode = Some(instances))

  /** The instances the round's saturation of the program may add: the
    * compilation's budget, or `instancesPerNode` for each node of the program's
    * IR graph when that is more, at most the largest `Int`.
    */
  def budgetFor(program: Configured[C]): Int =
    instancesPerNode.fold(compilation.budget)(instances =>
      (BigInt(instances) * BigInt(
        PreparedLemmaCompilation.graphNodes(program)(using index.specializer)
      )).max(BigInt(compilation.budget)).min(BigInt(Int.MaxValue)).toInt
    )

  /** The round's saturation of the program within its budget for it
    * (`budgetFor`), its graph recording the terms made when `explained` (a run
    * whose proof is wanted).
    */
  def saturated(
      program: Configured[C],
      explained: Boolean,
      stop: StopSignal
  ): Run[C] =
    saturator
      .begun(index, Vector(program), budgetFor(program), explained, stop)
      .run

  /** The round's compiled lemmas and orientations, what `prepared` built. */
  def compiledRound: FixpointEgraph.CompiledRound[C] =
    saturator.round.getOrElse(
      throw IllegalStateException(
        "a prepared lemma compilation has its round compiled"
      )
    )

  /** The round's saturation of the program on the graph the shared rounds
    * before it left (`HigherOrderSaturator.begunOn`): at most its budget for
    * the program (`budgetFor`) of instances beyond those the graph counts, to
    * the round's fixed point.
    */
  def saturatedOn(
      graph: EGraph[C],
      shared: Vector[FixpointEgraph.CompiledRound[C]],
      program: Configured[C],
      stop: StopSignal
  ): Run[C] =
    saturator
      .begunOn(index, graph, shared, Vector(program), budgetFor(program), stop)
      .run

  /** The program extracted from the round's graph. */
  def extracted(
      program: Configured[C],
      run: Run[C],
      stop: StopSignal
  ): Configured[C] =
    compilation.extracted(index, program, run, stop)

object PreparedLemmaCompilation:

  /** The size of the program's IR graph: its distinct instructions, the program
    * and every instruction under it, and the distinct nodes of the codes their
    * thunks hold, each counted once however often it is shared (codes are
    * interned). A thunk's children are its fillings (`gezi.ir.Apply.children`),
    * its body is its code, so a program whose content sits in one large closure
    * body counts that body's nodes here; an opaque instruction, a URI node
    * included, is a leaf; a native storage the e-graph keeps as a leaf
    * (`gezi.ir.NativeStorage.leafInEGraph`) counts two nodes, the leaf and its
    * pattern view, and its criterion's, its view not read.
    */
  def graphNodes[C <: NativeSpecializer & Singleton](program: Configured[C])(
      using specializer: C
  ): Int =
    @tailrec
    def counted(
        instructions: List[Configured[C]],
        codes: List[Code],
        seenInstructions: Set[Configured[C]],
        seenCodes: Set[Code],
        patternViews: Int
    ): Int = (instructions, codes) match
      case (Nil, Nil) => seenInstructions.size + seenCodes.size + patternViews
      case (current :: rest, _) if seenInstructions.contains(current) =>
        counted(rest, codes, seenInstructions, seenCodes, patternViews)
      case (current :: rest, _) if current.opaque =>
        counted(
          rest,
          codes,
          seenInstructions + current,
          seenCodes,
          patternViews
        )
      case (current :: rest, _) if current.heldAsLeaf =>
        // The leaf's criterion is a term of the configuration, read by the specializer from the storage alone.
        val criterion = (current.representation.layer: AnyRef) match
          case storage: gezi.ir.NativeStorage =>
            (specializer: C).criterionOf(storage)
          case other =>
            throw IllegalStateException(
              s"a leaf that is neither opaque nor a storage: $other"
            )
        counted(
          criterion :: rest,
          codes,
          seenInstructions + current,
          seenCodes,
          patternViews + 1
        )
      case (current :: rest, _) =>
        val held = current.layer match
          case Thunk(code, _, _) => code :: codes
          case _                 => codes
        counted(
          current.layer.children.toList ++ rest,
          held,
          seenInstructions + current,
          seenCodes,
          patternViews
        )
      case (Nil, code :: rest) if seenCodes.contains(code) =>
        counted(Nil, rest, seenInstructions, seenCodes, patternViews)
      case (Nil, code :: rest) =>
        val under = code.layer match
          case Thunk(inner, _, fillings) => inner :: fillings.toList
          case Apply(function, argument) => List(function, argument)
          case Parallel(left, right)     => List(left, right)
          case Choice(left, right)       => List(left, right)
          case Slot(_)                   => Nil
        counted(
          Nil,
          under ++ rest,
          seenInstructions,
          seenCodes + code,
          patternViews
        )
    counted(List(program), Nil, Set.empty, Set.empty, 0)

object LemmaCompilation:

  /** The modules of the round's extraction and of its write-backs: the narrow
    * blocks over the natives first, then the size.
    */
  def extractorModules[C <: NativeSpecializer & Singleton](
      natives: NativeBackend,
      configuration: gezi.weakhead.ReadingConfiguration[C]
  ): Vector[NormalityModule[C]] =
    Vector(NarrowBlockOrder(natives, configuration), Compression.at[C])

  /** The saturation of the lemma compilation's round under the options,
    * `HigherOrderSaturator`; with `opening`, every closure a lemma may match
    * opened and its body written back, spelled by `modules` (a route's
    * `extractorModules`), the spellings of one pass kept from body to body as
    * `writeBackSpellings` says, the closures chosen by `openingChoice`
    * (`gezi.saturation.OpeningCriterionChoice`).
    */
  def higherOrderSaturator[C <: NativeSpecializer & Singleton](
      options: SaturationOptions[C],
      opening: Boolean,
      writeBackSpellings: SpellingRetention,
      modules: Vector[NormalityModule[C]],
      openingChoice: gezi.saturation.OpeningCriterionChoice
  ): HigherOrderSaturator[C] =
    HigherOrderSaturator(
      options,
      Option.when(opening)(
        LocalExtraction(
          modules,
          NarrowBlockExtractor.productionNames,
          writeBackSpellings
        )
      ),
      None,
      openingChoice
    )

/** The baseline's extraction (`CountedExtractor`) under the modules given, its
  * productions the library's noinline defines and the names the narrow blocks
  * read as the backend's (`NarrowBlocks.nameKind`): the defines a `native`
  * declaration binds, those whose `combinator_property` is a native
  * specialization, and the fixed point combinator by value. So a filter's
  * criterion, `binary_set p`, is spelled as its name and not as its body; which
  * spelling a class takes is still the modules' order. Its cost model reads a
  * thunk's jointly read fillings as `jointReading` says.
  */
final case class NarrowBlockExtractor[C <: NativeSpecializer & Singleton](
    modules: Vector[NormalityModule[C]],
    jointReading: JointReading
) extends Extractor[C]:

  TermOrder.extractionModulesChecked(modules)

  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]] =
    CountedExtraction.fixed(
      graph,
      NarrowBlockExtractor.productionNames(index),
      ModuleCostModel(modules, TermReading(index), stop, jointReading),
      stop
    )(using index.specializer) match
      case Some(extracted) =>
        FixpointEgraph.outputsSpelled(
          extracted,
          inputNodes.map(graph.root),
          inputs,
          graph.store.construction
        )(using index.specializer)
      case None => inputs

/** The productions of the narrow blocks' extraction. */
object NarrowBlockExtractor:

  /** The library terms bound to natives: by `native` declarations, and the
    * constructors the `data_family` of a type with a `native_specialization`
    * lists (`Codecs.declaredConstructors`) or of a family declared by facts
    * (`DeclaredFamilies.constructorTerms`).
    */
  def boundKeys[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C]
  ): Vector[Pure] =
    index.nativeBound
      .map(_.instruction) ++ Codecs.declaredConstructors(index).flatMap(_._2) ++
      DeclaredFamilies.constructorTerms(index).flatMap(_._2)

  /** The library terms bound to natives, as terms of the index's configuration
    * (`boundKeys`).
    */
  def boundTerms[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C]
  ): Vector[Configured[C]] =
    boundKeys(index).map(Configured.fromPure(index.specializer))

  /** The library's noinline defines and the backend's names: the criteria among
    * them those with a `native_specialization` and those of the families
    * declared by facts (`jvm_type(generic)`), whose criterion is their
    * identity.
    */
  def productionNames[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C]
  ): Set[Configured[C]] =
    given C = index.specializer
    val backendNames = boundTerms(index) ++ index.combinatorProperties.collect {
      case CombinatorProperty(instruction, Property.NativeSpecialization(_)) =>
        Configured.fromPure[C](index.specializer)(instruction)
      case CombinatorProperty(
            instruction,
            Property.JvmType(JvmTypeName.Generic)
          ) =>
        Configured.fromPure[C](index.specializer)(instruction)
    } :+ Configured.fromPure[C](index.specializer)(NarrowBlocks.fixpointByValue)
    // TODO (https://github.com/Atry/private-overlay/issues/1517):
    // the backend's names become the round's `leaves`.
    FixpointEgraph.productionNames(index) ++ backendNames
