package com.yang_bo.gezi.strategies

import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex
import com.yang_bo.gezi.egraph.ClassAnalysis
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.MemoRetention
import com.yang_bo.gezi.egraph.LiveNode
import com.yang_bo.gezi.extraction.CostModel
import com.yang_bo.gezi.extraction.StatelessCostModel
import com.yang_bo.gezi.extraction.Extracted
import com.yang_bo.gezi.extraction.Extraction
import com.yang_bo.gezi.extraction.Shape
import com.yang_bo.gezi.extraction.Spelled
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.orientation.CompiledOrientations
import com.yang_bo.gezi.orientation.LemmaSides
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.orientation.OrientationCompiler
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.ematching.Backend
import com.yang_bo.gezi.ematching.CompiledProgram
import com.yang_bo.gezi.ematching.Program
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.saturation.Run
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.TermConstruction
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.DispatchPattern
import com.yang_bo.gezi.ir.SpecializationRange
import com.yang_bo.gezi.ir.Layer
import com.yang_bo.gezi.ir.LayerWith
import com.yang_bo.gezi.ir.NotTerm
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Reachability
import com.yang_bo.gezi.lemmaencoding.EncodedLemma
import com.yang_bo.gezi.lemmaencoding.LemmaEncoding
import com.yang_bo.gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel, Slot, Thunk}
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** The options of a saturation: the lemmas enabled, by identity, those the
  * round's knowledge term declares (`StandardLibrary.lemmas`), the built-in
  * rules enabled (`com.yang_bo.gezi.saturation.BuiltInRule`: a rule not listed is not
  * applied, so a round names every one it relies on, `BuiltInRule.beforeOptIn`
  * for the rules every round applied before they were opt-in), the budget, the
  * most instances that change the graph (`budget(Instances)`), and the backend
  * of the framework that runs the saturation's program. The backend is one of
  * `com.yang_bo.gezi.ematching.interpretation.Interpretation`,
  * `com.yang_bo.gezi.ematching.closures.ClosureCompilation` and
  * `com.yang_bo.gezi.ematching.bytecode.BytecodeCompilation`, or an entry's own `Backend`.
  * A backend runs a program the same way as every other (the same matches in
  * the same order, the same nodes built in the same order: the contract of
  * `com.yang_bo.gezi.ematching.Backend`, which an entry's own backend must keep), so the
  * choice changes the time a saturation takes, never its graph, its end or the
  * outputs extracted from it; for the framework's three,
  * `SaturationBackendsLawTest` checks it. The indexer compiles the round's
  * orientations and codes into that program, such as the framework's
  * `StandardIndexer`. The lemma encoding turns each enabled lemma's two closed
  * terms into the patterns its orientations are compiled from, an
  * implementation of the interface `com.yang_bo.gezi.lemmaencoding.LemmaEncoding`, such as
  * the baseline's `com.yang_bo.gezi.lemmaencoding.baseline.BaselineLemmaEncoding`. The
  * orientation compiler turns those patterns into the orientations the indexer
  * compiles, numbered (`com.yang_bo.gezi.orientation.OrientationCompiler`, such as the
  * framework's `com.yang_bo.gezi.orientation.StandardOrientationCompiler`). The backend,
  * the indexer, the lemma encoding and the orientation compiler are the
  * caller's choice; the framework's defaults are chosen in one place,
  * `com.yang_bo.gezi.contest.entry.Defaults`. The respellings say whether the round's graph
  * keeps the front end's spellings of the thunk layers it made
  * (`com.yang_bo.gezi.egraph.EGraph.respellingRetention`). The construction is how the
  * round's write-back and extraction build the terms they intern
  * (`com.yang_bo.gezi.ir.TermConstruction`, carried by the graph's store), through the
  * native specializer of the round's configuration. The constant storage stop
  * is whether the round matches no lemma below a class holding a storage of
  * constant size (`com.yang_bo.gezi.saturation.ConstantStorageStop`), off unless chosen; a
  * round that chooses it cannot also enable the expansion of storages' views
  * (`BuiltInRule.StorageView`), whose purpose is matching below a storage.
  */
final case class SaturationOptions[C <: NativeSpecializer & Singleton](
    lemmas: Vector[LemmaIdentifier],
    builtInRules: Set[BuiltInRule],
    budget: Int,
    lemmaEncoding: LemmaEncoding,
    backend: Backend,
    indexer: Indexer[C],
    orientationCompiler: OrientationCompiler,
    respellings: MemoRetention,
    // No default: a round under facts writes back through their native specializer, never as written by omission.
    construction: TermConstruction[C],
    constantStorageStop: Boolean = false
)

/** The options of an extraction: the names of its ordering modules, from the
  * highest priority to the lowest (`modules(Modules)`).
  */
final case class ExtractionOptions(modules: Vector[String])

/** How a round's orientations, numbered from 0 in order, and the codes of its
  * store become the program the backend runs: the inverted index of seeds by
  * kind and key, and the buildings of the added sides, the shared subterms and
  * the code bodies (`com.yang_bo.gezi.ematching.Program`). An indexer may file the seeds as
  * it likes; a backend then runs the program by the contract of
  * `com.yang_bo.gezi.ematching.Backend`, so the order the program gives the matches is the
  * saturation's order.
  */
trait Indexer[C <: NativeSpecializer & Singleton]:
  def program(orientations: Vector[Orientation[C]], codes: Set[Code])(using
      C
  ): Program[C]

/** The framework's index, `com.yang_bo.gezi.ematching.indexing.Indexing`. */
object StandardIndexer:

  /** The framework's indexer of the configuration `C`. */
  def of[C <: NativeSpecializer & Singleton]: Indexer[C] = new Indexer[C]:
    def program(orientations: Vector[Orientation[C]], codes: Set[Code])(using
        C
    ): Program[C] =
      Indexing.program(orientations, codes)

/** A round's saturation: the run of the inputs, and the lemmas it saturates
  * with as it encoded them into patterns. The run's graph is the framework's
  * e-graph, which the extraction and the proof read; the proof states each
  * lemma by its encoding.
  */
trait Saturator[C <: NativeSpecializer & Singleton]:

  /** The run of the inputs, its graph recording the terms made when
    * `explained`: a run whose proof or trace is wanted (`GraphProof` reads only
    * such a graph), and only such a run pays for it
    * (`com.yang_bo.gezi.egraph.EGraph.explained`).
    */
  def saturated(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      explained: Boolean,
      stop: StopSignal
  ): Run[C]
  def lemmas(index: StandardLibraryIndex[C]): Vector[EncodedLemma[C]]

  /** The run of the inputs begun with at most `budget` instances that change
    * the graph, in place of the saturator's own budget, and kept so that it can
    * go on (`SaturationProgress.resumed`). A caller begins with a small budget,
    * reads the end and the instances spent, and resumes or gives up by that
    * cost before paying for the whole saturation.
    */
  def begun(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  ): SaturationProgress[C]

/** A saturation that can go on: its run so far, the program and its compiled
  * form it matches with, and the built-in rules its round enables.
  */
final case class SaturationProgress[C <: NativeSpecializer & Singleton](
    run: Run[C],
    program: Program[C],
    compiled: CompiledProgram[C],
    builtInRules: Set[BuiltInRule]
):

  /** The saturation gone on by at most `more` instances beyond those its graph
    * counted (`Saturation.saturated` on the run's graph, which loses nothing at
    * the cut). A run at its fixed point stays there.
    */
  def resumed(more: Int, stop: StopSignal): SaturationProgress[C] =
    require(more > 0, s"a resumption adds at least one instance: $more")
    val (graph, end) =
      Saturation.saturated(
        program,
        compiled,
        builtInRules,
        run.graph,
        run.graph.instances + more,
        stop
      )
    copy(run = run.copy(graph = graph, end = end))

/** The baseline's saturation under the options (`FixpointEgraph.saturated`). */
final case class StandardSaturator[C <: NativeSpecializer & Singleton](
    options: SaturationOptions[C]
) extends Saturator[C]:
  def saturated(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      explained: Boolean,
      stop: StopSignal
  ): Run[C] =
    FixpointEgraph.saturated(index, inputs, options, explained, stop)(using
      index.specializer
    )
  def lemmas(index: StandardLibraryIndex[C]): Vector[EncodedLemma[C]] =
    FixpointEgraph.lemmas(index, options)
  def begun(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  ): SaturationProgress[C] =
    FixpointEgraph.begun(
      index,
      inputs,
      options.copy(budget = budget),
      explained,
      stop
    )(using index.specializer)

/** The baseline's saturation with the graph keeping a cost analysis
  * (`FixpointEgraph.analysedBegun`): the same run as `StandardSaturator`, its
  * classes priced for an `AnalysedCostModel`.
  */
final case class AnalysedSaturator[C <: NativeSpecializer & Singleton](
    options: SaturationOptions[C],
    analysis: ClassAnalysis[C, ?]
) extends Saturator[C]:
  def saturated(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      explained: Boolean,
      stop: StopSignal
  ): Run[C] =
    FixpointEgraph
      .analysedBegun(index, inputs, options, analysis, explained, stop)(using
        index.specializer
      )
      .run
  def lemmas(index: StandardLibraryIndex[C]): Vector[EncodedLemma[C]] =
    FixpointEgraph.lemmas(index, options)
  def begun(
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      explained: Boolean,
      stop: StopSignal
  ): SaturationProgress[C] =
    FixpointEgraph.analysedBegun(
      index,
      inputs,
      options.copy(budget = budget),
      analysis,
      explained,
      stop
    )(using index.specializer)

/** A round's extraction after its saturation: the output of each input, the
  * input's node given in the same order. When `stop` is requested the
  * extraction ends at its next check and gives the inputs as written (each
  * input is a member of its own class, so the output is sound).
  */
trait Extractor[C <: NativeSpecializer & Singleton]:
  def extracted(
      index: StandardLibraryIndex[C],
      graph: EGraph[C],
      inputNodes: Vector[Int],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  ): Vector[Configured[C]]

// TODO (https://github.com/Atry/private-overlay/issues/1530): the baseline's
// extractor is `CountedExtractor`, a module moved into this project
// (strategies/src/main/scala/gezi/strategies/CountedExtractor.scala).
// The retired `StandardExtractor` reads back with
// `git show c33817721:lambda_jit/strategies/src/main/scala/lambdajit/strategies/FixpointSearch.scala`.

/** The report of the strategy `fixpoint_egraph`: the saturation's end. */
final case class FixpointReport(end: End) extends StrategyReport

/** Why a saturation could not run (`fixpoint_egraph_error(Reason)`). */
enum FixpointEgraphErrorReason:
  case UnknownLemma(lemma: LemmaIdentifier)
  case NegativeBudget(budget: Int)

  /** The round at the position, from 0, has other leaves than the first. */
  case RoundsLeavesDiffer(round: Int)

  /** The round at the position, from 0, builds the terms it writes back
    * otherwise than the first (`SaturationOptions.construction`).
    */
  case RoundsConstructionsDiffer(round: Int)

  /** The round chooses both the constant storage stop and the expansion of
    * storages' views (`SaturationOptions.constantStorageStop`).
    */
  case StopWithStorageView

/** A saturation that could not run. */
final case class FixpointEgraphError(reason: FixpointEgraphErrorReason)
    extends RuntimeException(s"fixpoint e-graph error: $reason")

/** Why the search could not give an output or a proof
  * (`fixpoint_search_error(Reason)`).
  */
enum FixpointSearchErrorReason[C <: NativeSpecializer & Singleton]:
  case NoSpelling(input: Configured[C])
  case NotInTheGraph(side: Configured[C])

/** A search that could not give an output or a proof. */
final case class FixpointSearchError[C <: NativeSpecializer & Singleton](
    reason: FixpointSearchErrorReason[C]
) extends RuntimeException(s"fixpoint search error: $reason")

/** A round's extraction: the best entries of the graph's classes and the output
  * of each input.
  */
final case class ExtractedOutputs[C <: NativeSpecializer & Singleton](
    extracted: Extracted[C, ModuleCost],
    outputs: Vector[Configured[C]]
)

/** The cost of an entry under ordering modules: each module's fold state and
  * the rank read off it, in the order of the modules; and whether the entry's
  * spelling is λf. f as the refinement runs it
  * (`DispatchPattern.identityContractLayer`), part of the reading and of no
  * rank: a parent whose code applies the entry as a curried member's contract
  * is priced as the specialization the refinement dispatches only when it is
  * (`TermReading.identityContract`). And the classes of the domains the entry's
  * spelling checks its next arguments by, one for each argument in order, when
  * it is a contract (`DispatchPattern.contractChecks`) or a contract applied to
  * some of its arguments: part of the reading and of no rank too, so that a
  * function's class keeps its best contract beside its best entry of no
  * contract, and a call whose argument's filter by the next domain is repelled
  * reads the function by the other
  * (`com.yang_bo.gezi.extraction.Production.repelledDomains`).
  */
final case class ModuleCost(
    states: Vector[FoldState],
    ranks: Vector[OrderValue],
    identityContract: Boolean,
    contractDomains: Vector[Int] = Vector.empty
)

/** The cost model of the extraction under ordering modules: a production's fold
  * state at each module is read off the production's layer whose children are
  * leaves of the child entries' states at that module (`module_states/4`);
  * costs are compared by their lists of ranks in Prolog's standard order, and a
  * cost's reading is the list of the modules' readings
  * (`NormalityModule.reading`).
  *
  * ONE READING OF A LAYER FOR ALL THE MODULES (2026-11-12): a module that
  * prices a position another module ignores makes their lexicographic order
  * non-monotone (a criterion better under `specialization_attraction` and
  * larger under `compression` made the filter over it worse), so the model
  * reads every position as the extraction's choice reads it, for all the
  * modules alike. A parallel's criterion and a thunk's filling that the thunk's
  * code reads only in a criterion, or not at all, are `OrderTerm.Unpriced`, the
  * child's reading at the module and not its state (a filling read only as a
  * filter function's criterion, priced, made `λx. x ∥ T` worse over a better T
  * under the native route's combination, CostMonotonicityLawTest, 2026-11-12).
  * This changed what the modules prefer: the size of a criterion and an unused
  * filling are no longer priced, and ties among them go to the order of
  * content.
  *
  * THE PRICE OF A CHOICE (2026-11-13): a production costs what the run of its
  * spelling evaluates, so that the extraction's order is the order of the runs.
  * The refinement dispatches the patterns the dispatch recognizer reads
  * (`DispatchPattern`), and the extraction makes them productions of their own
  * (`Extraction.dispatchShapes`):
  *   - a specialization choice `F A + T` runs its typed member T, `F (A ∥ D)`
  *     under the range or the contract, the argument checked at a fallback
  *     point where the domain is a decoding criterion and taken as typed where
  *     it is not, so it costs the modules' fold of T over its parts' entries,
  *     the domain and the range unpriced as every criterion is;
  *   - a judgment `X + (X ∥ T)` is X by the absorption, law (6), and the
  *     refinement runs X, so it costs X's entry, its reading included;
  *   - any other choice runs both members, so each module folds both (the
  *     modules' own `Choice` rules: `Compression` counts the choice and its
  *     members, `SpecializationAttraction` sums the members' counts and reads a
  *     filter only when every member does).
  * Read as its least member, a choice ranked as the member it did not run:
  * `cons h (s + (s ∥ T))` ranked as a filtered argument and beat `cons h s` at
  * every tail of a list, the steps of list_ending_in_a_boolean doubling about
  * every two elements (1658 at size 4, 1,087,878 at 21, 2026-11-12); and a
  * specialization's untyped member, smaller under `Compression`, took the place
  * of the typed member the run evaluates.
  *
  * @param jointReading
  *   how a thunk's jointly read fillings are read (`ThunkCandidates`,
  *   `CodeCandidates`), a choice of the search the extractor that builds the
  *   model is given; `JointReading.measured` where nothing chooses it.
  */
final case class ModuleCostModel[C <: NativeSpecializer & Singleton](
    modules: Vector[NormalityModule[C]],
    reading: TermReading[C],
    stop: StopSignal,
    jointReading: JointReading = JointReading.measured
) extends StatelessCostModel[C, ModuleCost]:

  def cost(shape: Shape[C], childCosts: Vector[ModuleCost]): ModuleCost =
    shape match
      case Shape.Judged(_, _) =>
        val Vector(valueCost, _) = childCosts: @unchecked
        valueCost
      case _ =>
        val priced = CostModel.pricedUnder(this, shape, childCosts)
        val states = modules.zipWithIndex.map { (module, position) =>
          val children = childCosts
            .zip(priced)
            .map((cost, isPriced) =>
              if isPriced then
                OrderTerm
                  .Folded[C](cost.states(position), cost.identityContract)
              else OrderTerm.Unpriced[C](module.reading(cost.states(position)))
            )
          module.folded(layer(shape, children), reading)
        }
        ModuleCost(
          states,
          modules.zip(states).map((module, state) => module.rank(state)),
          identityContract(shape, childCosts),
          contractDomainsOf(shape, childCosts)
        )

  val ordering: Ordering[ModuleCost] =
    (left: ModuleCost, right: ModuleCost) =>
      OrderValue.ranksOrdering.compare(left.ranks, right.ranks)

  /** A thunk's candidates by the decomposition of its body (`ThunkCandidates`),
    * every other production's every combination.
    */
  override def candidates(
      shape: Shape[C],
      options: Vector[Vector[com.yang_bo.gezi.extraction.Entry[C, ModuleCost]]]
  ): Vector[com.yang_bo.gezi.extraction.Entry[C, ModuleCost]] = shape match
    case Shape.Node(_, thunk @ Thunk(_, _, _)) =>
      ThunkCandidates.candidates(this, shape, thunk, options)
    case _ => super.candidates(shape, options)

  /** A thunk's least candidates by the decomposition of its body ordered by
    * size and then content (`ThunkCandidates.leastCandidates`), every other
    * production's every combination.
    */
  override def leastCandidates(
      shape: Shape[C],
      options: Vector[Vector[com.yang_bo.gezi.extraction.Entry[C, ModuleCost]]]
  ): Vector[com.yang_bo.gezi.extraction.Entry[C, ModuleCost]] = shape match
    case Shape.Node(_, thunk @ Thunk(_, _, _)) =>
      ThunkCandidates.leastCandidates(this, shape, thunk, options)
    case _ => super.leastCandidates(shape, options)

  /** A thunk's fillings its candidates settle at the numbers of entries given
    * (`ThunkCandidates.settledFillings`); no other production's.
    */
  override def settledChildren(
      shape: Shape[C],
      entryCounts: Vector[Int]
  ): Vector[Boolean] = shape match
    case Shape.Node(_, thunk @ Thunk(_, _, _)) =>
      ThunkCandidates.settledFillings(this, thunk, entryCounts)
    case _ => shape.children.map(_ => false)

  override def contractDomain(cost: ModuleCost): Option[Int] =
    cost.contractDomains.headOption

  /** The domains' classes the production's spelling checks its next arguments
    * by: a thunk read as a contract, its domain and then those of its range's
    * contract (`DispatchPattern.contractChecks`, over its fillings' identity
    * contracts and costs); an application, its function's after the first; a
    * judgment, its value's (which the refinement runs); every other production
    * none.
    */
  private def contractDomainsOf(
      shape: Shape[C],
      childCosts: Vector[ModuleCost]
  ): Vector[Int] = shape match
    case Shape.Node(_, thunk @ Thunk(_, _, fillings)) =>
      val costs = fillings.zip(childCosts).toMap
      DispatchPattern
        .contractChecks(
          thunk: Layer[Int],
          (filling: Int) => costs.get(filling).exists(_.identityContract)
        )
        .fold(Vector.empty[Int])((domain, contract) =>
          domain +: contract
            .flatMap(costs.get)
            .fold(Vector.empty[Int])(_.contractDomains)
        )
    case Shape.Node(_, Apply(_, _)) =>
      val Vector(functionCost, _) = childCosts: @unchecked
      functionCost.contractDomains.drop(1)
    case Shape.Judged(_, _) =>
      val Vector(valueCost, _) = childCosts: @unchecked
      valueCost.contractDomains
    case _ => Vector.empty

  override def sameReading(left: ModuleCost, right: ModuleCost): Boolean =
    left.identityContract == right.identityContract &&
      left.contractDomains == right.contractDomains &&
      modules.zipWithIndex.forall((module, position) =>
        module.reading(left.states(position)) == module.reading(
          right.states(position)
        )
      )

  /** Whether the production's spelling over entries of the costs is λf. f as
    * the refinement runs it: a name by its layers, a thunk by its code over its
    * fillings' flags (`DispatchPattern.identityContractLayer`); a judgment as
    * its value, which the refinement runs; every other production none.
    */
  private def identityContract(
      shape: Shape[C],
      childCosts: Vector[ModuleCost]
  ): Boolean = shape match
    case Shape.Name(instruction) =>
      TermReading.identityContract(OrderTerm.Name(instruction))
    case Shape.Node(_, NoinlineLeaf(instruction)) =>
      TermReading.identityContract(OrderTerm.Name(instruction))
    case Shape.Node(_, thunk @ Thunk(_, _, _)) =>
      DispatchPattern.identityContractLayer(
        // The children are the costs' flags, no terms of the IR.
        (thunk: Layer[Int]).over(childCosts.map(_.identityContract))(using
          com.yang_bo.gezi.ir.NotTerm.granted[Boolean]
        ),
        (flag: Boolean) => flag
      )
    case Shape.Judged(_, _) =>
      val Vector(valueCost, _) = childCosts: @unchecked
      valueCost.identityContract
    case _ => false

  /** Whether each child of the shape is priced: not a parallel's criterion, not
    * a thunk's filling of a slot its code reads only in a criterion or not at
    * all, and not a specialization's domain or range. An unpriced child is read
    * as `OrderTerm.Unpriced` with its reading at each module, its reading alone
    * (and its identity contract) entering the production's.
    */
  /** A choice's members other than the one a module says the backend runs over
    * these members' readings (`NormalityModule.chosenChoiceMember`): every
    * module reads them as unpriced, by their readings, so that no module prices
    * a member the backend drops (a narrow choice ranking its chosen member
    * while compression counted the others broke the monotonicity of the lemma
    * compilation's extraction, NarrowBlockCostMonotonicityLawTest, seed
    * 150715495590311). Throws `IllegalStateException` when two modules name
    * different members. And an application's or a parallel's children some
    * module says the backend compiles whatever their spelling
    * (`NormalityModule.compiledChildren`): every module reads them as unpriced
    * too, so that no module prices a spelling the run does not read (a narrow
    * function inside a block).
    */
  override def droppedChildren(
      shape: Shape[C],
      childCosts: Vector[ModuleCost]
  ): Vector[Boolean] = shape match
    case Shape.Node(_, nodeLayer @ (Apply(_, _) | Parallel(_, _)))
        if compilingModules.nonEmpty =>
      compilingModules.foldLeft(childCosts.map(_ => false)) {
        case (dropped, (module, position)) =>
          val readings = childCosts.map(cost =>
            OrderTerm.Unpriced[C](module.reading(cost.states(position)))
          )
          val compiled = module.compiledChildren(
            ModuleCostModel.orderLayer(nodeLayer.over(readings)),
            reading
          )
          dropped.zip(compiled).map(_ || _)
      }
    case Shape.Node(_, Choice(_, _)) =>
      val named = modules.zipWithIndex.flatMap((module, position) =>
        module
          .chosenChoiceMember(
            childCosts.map(cost => module.reading(cost.states(position)))
          )
          .map(module.name -> _)
      )
      named.map(_._2).distinct match
        case Vector()       => childCosts.map(_ => false)
        case Vector(member) => childCosts.indices.toVector.map(_ != member)
        case _              =>
          throw IllegalStateException(
            s"the modules run different members of a choice: ${named.map((name, member) => s"$name runs member $member").mkString(", ")}"
          )
    case _ => childCosts.map(_ => false)

  /** A choice's members: a module may run one of them only; and an
    * application's or a parallel's children, when a module may say the backend
    * compiles them.
    */
  override def mayDropChildren(shape: Shape[C]): Vector[Boolean] = shape match
    case Shape.Node(_, Choice(_, _)) => Vector(true, true)
    case Shape.Node(_, Apply(_, _) | Parallel(_, _))
        if compilingModules.nonEmpty =>
      Vector(true, true)
    case _ => shape.children.map(_ => false)

  /** A name or a leaf the library declares `repeller`
    * (`TermReading.repellers`): a class that holds an application of it has no
    * entry.
    */
  override def repeller(shape: Shape[C]): Boolean = shape match
    case Shape.Name(instruction) => reading.repellers.contains(instruction)
    case Shape.Node(_, NoinlineLeaf(instruction)) =>
      reading.repellers.contains(instruction)
    case _ => false

  /** The modules that may name compiled children, with their positions. */
  private val compilingModules: Vector[(NormalityModule[C], Int)] =
    modules.zipWithIndex.filter(_._1.compilesChildren)

  def pricedChildren(shape: Shape[C]): Vector[Boolean] = shape match
    case Shape.Name(_)            => Vector.empty
    case Shape.Node(_, nodeLayer) =>
      nodeLayer match
        case Parallel(_, _)               => Vector(true, false)
        case Thunk(code, holes, fillings) =>
          Code.fillingsReadOutsideParallelRightOperands(
            code,
            holes,
            fillings.size
          )
        case other => other.children.map(_ => true)
    case Shape.Specialized(_, specialization) =>
      Vector(true, true, false) ++ (specialization.range match
        case SpecializationRange.Absent        => Vector.empty
        case SpecializationRange.Filtered(_)   => Vector(false)
        case SpecializationRange.Contracted(_) => Vector(true))
    case Shape.Judged(_, _) => Vector(true, false)

  /** The term the production is priced as over the children given
    * (`shape_layer/3`): its layer, and a specialization's typed member.
    */
  private def layer(
      shape: Shape[C],
      children: Vector[OrderTerm[C]]
  ): OrderTerm[C] = shape match
    case Shape.Name(instruction)  => OrderTerm.Name(instruction)
    case Shape.Node(_, nodeLayer) =>
      nodeLayer match
        case NoinlineLeaf(instruction) => OrderTerm.Name(instruction)
        case Choice(_, _)              => OrderTerm.Choice(children)
        case other => ModuleCostModel.orderLayer(other.over(children))
    case Shape.Specialized(_, specialization) =>
      TermReading.typedMember(Shape.partsOver(specialization, children))
    case Shape.Judged(_, _) =>
      val Vector(value, _) = children: @unchecked
      value

object ModuleCostModel:

  /** The order term of one layer over order terms. */
  def orderLayer[C <: NativeSpecializer & Singleton](
      layer: LayerWith[OrderTerm[C], Configured[C]]
  ): OrderTerm[C] = layer match
    case Apply(function, argument) => OrderTerm.Apply(function, argument)
    case Parallel(left, right)     =>
      OrderTerm.Parallel(left, right, specializationRange = false)
    case Choice(left, right)          => OrderTerm.Choice(Vector(left, right))
    case Thunk(code, holes, fillings) => OrderTerm.Thunk(code, holes, fillings)
    case NoinlineLeaf(instruction)    => OrderTerm.Name(instruction)
    case view: com.yang_bo.gezi.ir.StorageView[?] =>
      throw IllegalStateException(
        s"a node's layer is never a storage's view: $view"
      )

  /** The order term of a layer a dispatch pattern builds
    * (`DispatchPattern.typedMember`): an application, a parallel or a choice
    * over order terms, never a noinline leaf or a storage's view.
    */
  def orderPatternLayer[C <: NativeSpecializer & Singleton](
      layer: Layer[OrderTerm[C]]
  ): OrderTerm[C] = layer match
    case Apply(function, argument) => OrderTerm.Apply(function, argument)
    case Parallel(left, right)     =>
      OrderTerm.Parallel(left, right, specializationRange = false)
    case Choice(left, right)          => OrderTerm.Choice(Vector(left, right))
    case Thunk(code, holes, fillings) => OrderTerm.Thunk(code, holes, fillings)
    case other                        =>
      throw IllegalStateException(
        s"a dispatch pattern's layer holds no leaf or view: $other"
      )

/** The baseline's search strategy of the fixpoint e-graph, the port of
  * `gezi/prolog/gezi/baseline/fixpoint_search.pl`, whose module documentation
  * (THE EXTRACTION, THE PROOF) this follows: its saturator saturates every
  * input of a round to one graph and its extractor extracts the output of each
  * input from that graph. Each is a value an entry may replace while keeping
  * the other: the baseline's are `StandardSaturator`, one least fixed point
  * under the saturation options, and `CountedExtractor`, the extraction under
  * the ordering modules of the table given (`TermOrder`). Its report is the
  * saturation's end; when the round asks for the proof, the proof is the one of
  * the graph the run left. The strategy keeps no state from one search to the
  * next: the strategy after a search is itself.
  *
  * The extraction (`com.yang_bo.gezi.extraction.CountedExtraction`) keeps, for each class,
  * the entry of the least ranks, read greedily to its fixed point; the
  * productions of a class are its live nodes and the names of the library's
  * defines whose node is in the class. The output spells each class by its best
  * entry, each class it reads by its own best entry in turn, each class once
  * and interned, so that a class has one spelling in an output. Every input's
  * class has an entry, its own nodes spelling it; a class of an input with none
  * throws `FixpointSearchError` with `NoSpelling`.
  *
  * Nothing here reads a type or names a lemma (`CONTRIBUTING.md`, "Types live
  * only in the term"): the extraction reads the graph's layers and the ordering
  * modules' ranks. The extraction's data are immutable values.
  */
final case class FixpointEgraph[C <: NativeSpecializer & Singleton](
    index: StandardLibraryIndex[C],
    saturator: Saturator[C],
    extractor: Extractor[C]
) extends SearchStrategy[C]:

  def ran(
      inputs: Vector[Configured[C]],
      proofWanted: Boolean,
      stop: StopSignal
  ): Option[StrategyOutcome[C]] =
    Some(
      outcome(
        inputs,
        saturator.saturated(index, inputs, proofWanted, stop),
        proofWanted,
        stop
      )
    )

  /** The round begun on the inputs with at most `budget` instances, in place of
    * the saturator's own budget (`Saturator.begun`): a route reads the end and
    * the instances spent (`RoundProgress.end`), and goes on
    * (`RoundProgress.resumed`) or takes the outcome as the graph stands
    * (`RoundProgress.outcome`), choosing by that cost before paying for the
    * whole saturation. Its graph records the terms made when `proofWanted`, the
    * flag its outcome is then taken with.
    */
  def begun(
      inputs: Vector[Configured[C]],
      budget: Int,
      proofWanted: Boolean,
      stop: StopSignal
  ): RoundProgress[C] =
    RoundProgress(
      this,
      inputs,
      saturator.begun(index, inputs, budget, proofWanted, stop)
    )

  /** The outcome of the run: each input's output extracted from its graph, the
    * report of its end, and the proof when it is wanted.
    */
  private[strategies] def outcome(
      inputs: Vector[Configured[C]],
      run: Run[C],
      proofWanted: Boolean,
      stop: StopSignal
  ): StrategyOutcome[C] =
    val graph = run.graph
    val outputs =
      extractor.extracted(index, graph, run.inputNodes, inputs, stop)
    val proof = Option.when(proofWanted)(
      GraphProof.proof(graph, inputs.zip(outputs), saturator.lemmas(index))(
        using index.specializer
      )
    )
    StrategyOutcome[C](outputs, FixpointReport(run.end), proof, this)

/** A round of `FixpointEgraph` that can go on: its strategy, its inputs and its
  * saturation so far. Its outcome at any point is sound: every graph of a
  * saturation is equal to its inputs under the lemmas, so a cut graph gives
  * outputs only less refined (`Saturation.saturated`).
  */
final case class RoundProgress[C <: NativeSpecializer & Singleton](
    strategy: FixpointEgraph[C],
    inputs: Vector[Configured[C]],
    saturation: SaturationProgress[C]
):

  /** How the saturation so far ended, with the instances it spent. */
  def end: End = saturation.run.end

  /** The round gone on by at most `more` instances. */
  def resumed(more: Int, stop: StopSignal): RoundProgress[C] =
    copy(saturation = saturation.resumed(more, stop))

  /** The round's outcome on the graph as it stands, as `FixpointEgraph.ran`
    * gives it.
    */
  def outcome(proofWanted: Boolean, stop: StopSignal): StrategyOutcome[C] =
    strategy.outcome(inputs, saturation.run, proofWanted, stop)

/** The saturation, the extraction and the spellings of the strategy. */
object FixpointEgraph:

  /** The lemmas of direction `equation` among the options' lemmas, by ascending
    * identifier, as the options' lemma encoding encodes them.
    */
  def lemmas[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      options: SaturationOptions[C]
  ): Vector[EncodedLemma[C]] =
    index
      .enabledEquations(options.lemmas)
      .map(options.lemmaEncoding.encoded(index, _))

  /** The run of the inputs under the options: the options' lemmas compiled into
    * orientations, the graph of their pattern instructions and the inputs
    * saturated with the budget on the options' backend
    * (`fixpoint_egraph_run/3`), the stop signal read before each delta
    * (`Saturation.saturated`). Throws `FixpointEgraphError` with `UnknownLemma`
    * for a lemma the index holds no sides of and with `NegativeBudget` for a
    * negative budget.
    */
  def saturated[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      options: SaturationOptions[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): Run[C] =
    begun(index, inputs, options, explained, stop).run

  /** The run of `saturated`, kept with its program and compiled form so that it
    * can go on (`SaturationProgress.resumed`).
    */
  def begun[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      options: SaturationOptions[C],
      explained: Boolean,
      stop: StopSignal
  )(using C): SaturationProgress[C] =
    begunFrom(index, inputs, options, None, explained, stop)

  /** The run of `begun` with the graph keeping the cost analysis given from its
    * first node on (`EGraph.analysed`), for a cost model that reads it
    * (`com.yang_bo.gezi.extraction.AnalysedCostModel`). The analysis only prices classes:
    * the run's merges, instances and end are those of `begun`.
    */
  def analysedBegun[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      options: SaturationOptions[C],
      analysis: ClassAnalysis[C, ?],
      explained: Boolean,
      stop: StopSignal
  )(using C): SaturationProgress[C] =
    begunFrom(index, inputs, options, Some(analysis), explained, stop)

  private def begunFrom[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      options: SaturationOptions[C],
      analysis: Option[ClassAnalysis[C, ?]],
      explained: Boolean,
      stop: StopSignal
  )(using C): SaturationProgress[C] =
    begunIn(
      compiledRound(index, options),
      inputs,
      options.budget,
      analysis,
      explained,
      stop
    )

  /** What a round's saturation computes from the index and the options alone,
    * before any input: the lemmas encoded, their orientations compiled and the
    * graph of the instructions their matched sides mention. A caller that
    * saturates many inputs under one index and one set of options builds it
    * once and begins each input from it (`begunIn`), so that the round is not
    * compiled again for every input: on the hot ladder this was about 39% of a
    * point's saturation (a profile of 2026-11-07, 1419 of 3608 samples). It is
    * a value of the index and the options, keyed by nothing else
    * (`CONTRIBUTING.md`, "Tables", kind 2).
    */
  final case class CompiledRound[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      options: SaturationOptions[C],
      lemmas: Vector[EncodedLemma[C]],
      compiled: CompiledOrientations[C],
      patternGraph: EGraph[C]
  )

  /** The round of the index under the options. Throws `FixpointEgraphError`
    * with `UnknownLemma` for a lemma the index holds no sides of.
    */
  def compiledRound[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      options: SaturationOptions[C]
  ): CompiledRound[C] =
    given C = index.specializer
    if options.constantStorageStop && options.builtInRules.contains(
        BuiltInRule.StorageView
      )
    then
      throw FixpointEgraphError(FixpointEgraphErrorReason.StopWithStorageView)
    options.lemmas.foreach(lemma =>
      if index.sides(lemma).isEmpty then
        throw FixpointEgraphError(FixpointEgraphErrorReason.UnknownLemma(lemma))
    )
    val store = Store(index.noinline, options.construction)
    val encoded = lemmas(index, options)
    val compiled = options.orientationCompiler.compiled(
      encoded.map(lemma =>
        LemmaSides(lemma.lemma, lemma.metavariables, lemma.left, lemma.right)
      ),
      store
    )
    val patternGraph =
      Saturation
        .initialGraph(
          store,
          Orientations.headArityBounds(compiled.orientations),
          compiled.patternInstructions,
          explained = false
        )
        .withRespellingRetention(options.respellings)
    CompiledRound(index, options, encoded, compiled, patternGraph)

  /** `begun` from a compiled round, with `budget` in place of the round's
    * options' budget and the graph keeping the cost analysis given, if any.
    * Throws `FixpointEgraphError` with `NegativeBudget` for a negative budget.
    */
  def begunIn[C <: NativeSpecializer & Singleton](
      round: CompiledRound[C],
      inputs: Vector[Configured[C]],
      budget: Int,
      analysis: Option[ClassAnalysis[C, ?]],
      explained: Boolean,
      stop: StopSignal
  )(using C): SaturationProgress[C] =
    if budget < 0 then
      throw FixpointEgraphError(
        FixpointEgraphErrorReason.NegativeBudget(budget)
      )
    val program = round.options.indexer.program(
      round.compiled.orientations,
      Indexing.codesMet(
        round.compiled.orientations,
        round.compiled.patternInstructions ++ inputs
      )
    )
    val compiledProgram = round.options.backend.compiled(program)
    // The round's graph of pattern instructions is shared by every run of the
    // round and records no terms made; a run whose proof is wanted turns it
    // on before any union.
    val patternGraph =
      if explained then round.patternGraph.explaining else round.patternGraph
    val initial = analysis
      .fold(patternGraph)(costAnalysis => patternGraph.analysed(costAnalysis))
      .withConstantStorageStop(round.options.constantStorageStop)
    val run = Saturation.runFrom(
      program,
      compiledProgram,
      round.options.builtInRules,
      initial,
      inputs,
      budget,
      stop
    )
    SaturationProgress(
      run,
      program,
      compiledProgram,
      round.options.builtInRules
    )

  /** The graph the rounds share: the instructions every round's matched sides
    * mention, and the heads filed up to the largest arity any round's
    * orientations apply them to, so that a later round's index finds the nodes
    * an earlier round made under its own heads. Its leaves are the rounds'
    * leaves, which must be one set, and so must their constructions, the
    * graph's store holding one. Throws `FixpointEgraphError` with
    * `RoundsLeavesDiffer` for rounds whose leaves differ, and with
    * `RoundsConstructionsDiffer` for rounds whose constructions differ.
    *
    * FIXME: a round's https://github.com/Atry/private-overlay/issues/2047
    * leaves are the round's own configuration, and rounds whose leaves differ
    * cannot share one graph as this does: a term that is a leaf in one round
    * and unfolded in another has one representation in the graph. Until this is
    * designed (the graph rebuilt between two rounds, or leaves that only go
    * from round to round), such rounds are refused here instead of run on the
    * first round's leaves, which is what this function did before the leaves
    * were the rounds'.
    */
  def sharedGraph[C <: NativeSpecializer & Singleton](
      rounds: Vector[CompiledRound[C]],
      explained: Boolean
  ): EGraph[C] =
    require(rounds.nonEmpty, "a shared graph is of one round or more")
    given C = rounds.head.options.construction.specializer
    rounds.zipWithIndex
      .find((round, _) => round.index.noinline != rounds.head.index.noinline)
      .foreach((_, position) =>
        throw FixpointEgraphError(
          FixpointEgraphErrorReason.RoundsLeavesDiffer(position)
        )
      )
    rounds.zipWithIndex
      .find((round, _) =>
        round.options.construction != rounds.head.options.construction
      )
      .foreach((_, position) =>
        throw FixpointEgraphError(
          FixpointEgraphErrorReason.RoundsConstructionsDiffer(position)
        )
      )
    val bounds = rounds
      .map(round => Orientations.headArityBounds(round.compiled.orientations))
      .foldLeft(Map.empty[Configured[C], Int])((merged, more) =>
        more.foldLeft(merged) { case (current, (instruction, arity)) =>
          current.updated(
            instruction,
            current.get(instruction).fold(arity)(_ max arity)
          )
        }
      )
    Saturation.initialGraph(
      Store(rounds.head.index.noinline, rounds.head.options.construction),
      bounds,
      rounds.flatMap(_.compiled.patternInstructions).distinct,
      explained
    )

  /** `begunIn` of one of the shared rounds on the graph the rounds before it
    * left: the round's program, its codes met over every shared round's
    * orientations and the inputs, matched against every live node again
    * (`EGraph.everyNodeRedone`), and no instance added yet; the caller goes on
    * with `SaturationProgress.resumed`. The graph is `sharedGraph`'s or a later
    * state of it.
    */
  def begunOn[C <: NativeSpecializer & Singleton](
      round: CompiledRound[C],
      shared: Vector[CompiledRound[C]],
      graph: EGraph[C],
      inputs: Vector[Configured[C]],
      stop: StopSignal
  )(using C): SaturationProgress[C] =
    // The graph's own codes too: the earlier rounds wrote thunks whose codes
    // no orientation and no input of this round reaches (reverse beta's
    // abstractions, the bodies of instances built from their roots), and
    // the β worker compiles only the codes the program holds.
    val graphCodes = graph.liveNodes.collect {
      case LiveNode(_, _, Thunk(code, _, _)) => code
    }
    val program = round.options.indexer.program(
      round.compiled.orientations,
      Indexing.codesMet(
        shared.flatMap(_.compiled.orientations),
        shared.flatMap(_.compiled.patternInstructions) ++ inputs
      ) ++
        Reachability.codesUnder(graphCodes)
    )
    val compiledProgram = round.options.backend.compiled(program)
    val run = Saturation.runFrom(
      program,
      compiledProgram,
      round.options.builtInRules,
      graph.everyNodeRedone.withConstantStorageStop(
        round.options.constantStorageStop
      ),
      inputs,
      graph.instances,
      stop
    )
    SaturationProgress(
      run,
      program,
      compiledProgram,
      round.options.builtInRules
    )

  /** The names that are productions of the extraction: the instructions of the
    * library's noinline defines, each a production of the class its node is in:
    * after hash consing a define's instruction is no name of its own, and
    * noinline is what keeps a term unexpanded.
    */
  def productionNames[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C]
  )(using C): Set[Configured[C]] =
    index.noinline

  // TODO (https://github.com/Atry/private-overlay/issues/1530): a round's
  // extraction is `CountedExtractor.extracted`, over `CountedExtraction.fixed`.
  // The retired `outputsExtracted` reads back with
  // `git show c33817721:lambda_jit/strategies/src/main/scala/lambdajit/strategies/FixpointSearch.scala`.

  /** The output of each input, the spelling of its class, built by the
    * construction (the graph's `Store.construction`, so that a configuration
    * that converts terms into native storages writes back no plain twin of one)
    * and interned; the memo of the classes spelled shared by the outputs
    * (`output_extracted/4`).
    */
  def outputsSpelled[C <: NativeSpecializer & Singleton](
      extracted: Extracted[C, ModuleCost],
      roots: Vector[Int],
      inputs: Vector[Configured[C]],
      construction: TermConstruction[C]
  )(using C): Vector[Configured[C]] =
    val (_, outputs) =
      roots
        .zip(inputs)
        .foldLeft(
          (
            Spelled[Configured[C], Unit]((), Map.empty),
            Vector.empty[Configured[C]]
          )
        ) { case ((state, done), (root, input)) =>
          if !extracted.hasEntry(root) then
            throw FixpointSearchError(
              FixpointSearchErrorReason.NoSpelling(input)
            )
          val (after, output) =
            Extraction.spelled(extracted, root, state)(spell(construction))
          (after, done :+ output)
        }
    outputs

  /** The layer with its children replaced, in child order. Throws
    * `IllegalArgumentException` when their number is not the layer's.
    */
  def layerOver[C <: NativeSpecializer & Singleton, Child, Leaf](
      layer: LayerWith[Any, Leaf],
      children: Vector[Child]
  )(using NotTerm[Child]): LayerWith[Child, Leaf] = layer.over(children)

  /** The term of a production's shape over its children's spellings: a name or
    * a leaf its instruction, any other layer, and each layer of a dispatch
    * pattern, built through the construction's specializer
    * (`Shape.spelledTerm`, `entry_respelled/5`).
    */
  private def spell[C <: NativeSpecializer & Singleton](
      construction: TermConstruction[C]
  )(unit: Unit, shape: Shape[C], children: Vector[Configured[C]])(using
      C
  ): (Unit, Configured[C]) =
    (unit, Shape.spelledTerm(shape, children)(using construction.specializer))
