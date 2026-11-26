package gezi.interfacelaws

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.MemoRetention
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.BuiltInRule
import gezi.ir.Closed
import gezi.ir.Configured
import gezi.ir.LayerWith
import gezi.ir.LemmaIdentifier
import gezi.ir.NativeSpecializer
import gezi.ir.NativeStorage
import gezi.ir.NoFacts
import gezi.ir.NoinlineLeaf
import gezi.ir.ScottReading
import gezi.ir.StorageAccess
import gezi.ir.StorageView
import gezi.ir.TermConstruction
import gezi.jit.DeBruijnTermAsTerm
import gezi.jit.JitTesting
import gezi.saturation.Run
import gezi.saturation.StopSignal
import gezi.standardlibrary.SplitMix
import gezi.standardlibrary.StandardLibraryIndex
import gezi.strategies.BaselineRounds
import gezi.strategies.Extractor
import gezi.strategies.SaturationOptions
import gezi.strategies.StandardIndexer
import gezi.strategies.StandardSaturator
import gezi.strategies.StrategyTesting

private given extractorLawsNoFacts: NoFacts.type = NoFacts

/** A native storage of the laws kept as a leaf of constant size, holding its
  * criterion alone as a constant storage does, whose view throws when it is
  * read: an extractor reads a storage leaf as a leaf. Equal to itself only.
  */
final class LawStorage(name: String, val criterion: Configured[LawNativeSpecializer.type]) extends NativeStorage:
  val closed: Boolean = true
  val suspensionFree: Boolean = true
  val handedOverWhole: Boolean = false
  protected val termChildren: IArray[AnyRef] = IArray(criterion.representation)
  protected val constructorIndex: Int = 0
  val leafInEGraph: Boolean = true
  val constantSize: Boolean = true
  def precedes(other: NativeStorage): Boolean = false
  def contentHash: Int = System.identityHashCode(this)
  def sameContent(other: NativeStorage): Boolean = this eq other
  override def toString: String = s"LawStorage($name)"

/** The native specializer of the laws' stand-in storages: it converts no parallel, and makes a `LawStorage`'s term, the
  * only way a storage enters the pool. A storage's view and Scott reading are never read here, and its criterion is the
  * one it holds.
  */
object LawNativeSpecializer extends NativeSpecializer:
  protected def specialized(left: Closed[this.type], right: Closed[this.type]): Option[Closed[this.type]] = None

  protected def storageCriterion(storage: NativeStorage): Configured[this.type] = storage match
    case law: LawStorage => law.criterion
    case other           => throw IllegalStateException(s"a storage that is no law's has no criterion here: $other")

  protected def storageView(storage: NativeStorage)(using StorageAccess): StorageView[Configured[this.type]] =
    throw IllegalStateException(s"the view of the storage $storage was read")

  protected def storageScottReading(storage: NativeStorage)(using StorageAccess): ScottReading[Configured[this.type]] =
    throw IllegalStateException(s"the Scott reading of the storage $storage was read")

  def stored(storage: LawStorage): Configured[this.type] = storedTerm(storage)


/** The laws of the extraction interface `Extractor`, run on any
  * implementation: a suite that extends this class with the extractor checks
  * it ([[gezi.interfacelaws]]). The graphs are the baseline saturator's runs of
  * generated closed terms with choices and parallels, put through the front
  * end with the occurrence tagging, under the native route's library, the
  * Prolog backend's preset with closure_application and occurrence_erasure
  * (`ExtractorLaws.knowledgeFile`), and a generated budget. The tagging is what
  * makes the runs merge: MEASURED 2026-11-03 on 200 single terms of about
  * 12 nodes at budget 200, untagged terms under closure_application merged
  * no class in any run, and tagged ones under the native route's knowledge
  * of that date (its six knowledge files, before the backend's preset)
  * merged classes in all 200. (1) Each input has one output, and each
  * output is spelled in its input's class (`ExtractorLaws.spelledIn`): the
  * extractor answers a term the graph proves equal to its input, which makes a
  * round sound. (2) On a run with no knowledge module, where no lemma
  * instance merges two classes, each output is its input. A run of budget 0
  * is not such a run: the saturation adds one instance before it reads the
  * budget (MEASURED 2026-11-03: every tagged term above ended
  * `BudgetExhausted(1)` at budget 0, its graph one class merged). Their
  * purpose is to catch an extractor that answers a term of another class (an
  * unsound rewrite), drops or reorders an output, or changes a term the
  * saturation left alone. (3) Law (1) holds too on a run's graph with two
  * native storage leaves of constant size, by construction one united with an
  * input's class and one with the class of a child of a member of an input's
  * class, the unions then worked so that each leaf's class also holds its
  * pattern view `Parallel(the class, T)`, as the fold and the conversion leave
  * a storage in a class: its purpose is to catch an extractor that reads a
  * storage leaf's view, which throws here, that spells a class through its
  * own pattern view, or that answers a term of another class where a storage
  * leaf is a member.
  */
abstract class ExtractorLaws(
    extractor: Extractor[NoFacts.type],
    // The extractor of the second law, whose graph holds storages and so is a graph of `LawNativeSpecializer`.
    storageExtractor: Extractor[LawNativeSpecializer.type]
) extends GeneratedProperties:

  private given LawNativeSpecializer.type = LawNativeSpecializer

  private lazy val library = StrategyTesting.compiled(ExtractorLaws.knowledgeFile)

  private lazy val storageIndex: StandardLibraryIndex[LawNativeSpecializer.type] =
    StandardLibraryIndex.crossed(library.index, LawNativeSpecializer)

  private def inputs: Gen[Vector[Configured[NoFacts.type]]] =
    Gen
      .long(Range.linear(0L, Long.MaxValue))
      .list(Range.linear(1, 4))
      .map(_.toVector.map(seed =>
        StrategyTesting.programInput(library, DeBruijnTermAsTerm.term(JitTesting.randomLatticeApplication(12, SplitMix(seed))._1))
      ))

  private lazy val knowledgeLemmas: Vector[LemmaIdentifier] =
    library.index.lemmaSides.map(_.lemma).distinct.sortBy(_.number)

  private def run[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      inputs: Vector[Configured[C]],
      lemmas: Vector[LemmaIdentifier],
      budget: Int,
      stop: StopSignal
  )(using specializer: C): Run[C] =
    StandardSaturator[C](
      SaturationOptions(
        lemmas,
        BuiltInRule.beforeOptIn,
        budget,
        BaselineRounds.modules.lemmaEncoding,
        BaselineRounds.modules.backend,
        StandardIndexer.of[C],
        BaselineRounds.modules.orientationCompiler,
        MemoRetention.Kept,
        TermConstruction(specializer)
      )
    ).saturated(index, inputs, explained = false, stop)

  stoppableProperty("each input has one output, in the input's class") { stopped =>
    for
      written <- inputs.forAll
      budget <- Gen.int(Range.linear(0, ExtractorLaws.largestBudget)).forAll
    yield
      val saturated = run(library.index, written, knowledgeLemmas, budget, StopSignal.completedWith(stopped))
      val outputs = extractor.extracted(library.index, saturated.graph, saturated.inputNodes, written, StopSignal.completedWith(stopped))
      Result.all(
        Result.diff(outputs.length, written.length)(_ == _) ::
          outputs.zip(saturated.inputNodes).toList.map((output, inputNode) =>
            Result.assert(ExtractorLaws.spelledIn(saturated.graph, output, saturated.graph.root(inputNode)))
              .log(s"output $output, run ended ${saturated.end}")
          )
      )
  }

  // Five iterations, each with both placements by construction: each runs a
  // whole saturation for its graph (twenty took 20.6 s, 2026-11-25).
  stoppableProperty(
    "with storage leaves united into classes, each input has one output, in the input's class",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) { stopped =>
    for
      written <- inputs.forAll
      budget <- Gen.int(Range.linear(0, ExtractorLaws.largestBudget)).forAll
      picks <- Gen.int(Range.linear(0, Int.MaxValue)).list(Range.singleton(3)).forAll
    yield
      // The whole graph is of `LawNativeSpecializer`, the configuration of the storages it holds: the generated inputs and
      // the library cross into it (`NativeSpecializer.crossedAllFromNoFacts`).
      val crossed = LawNativeSpecializer.crossedAllFromNoFacts(written)
      val lawInputs = written.map(crossed)
      val saturated = run(storageIndex, lawInputs, knowledgeLemmas, budget, StopSignal.completedWith(stopped))
      val start = saturated.graph
      val inputRoot = start.root(saturated.inputNodes(picks(0) % saturated.inputNodes.size))
      // A child of a member of the input's class: under a layer, the class an
      // output is spelled through; the input's own class when no member has a
      // child.
      val childRoots = start.liveNodes.filter(_.root == inputRoot).flatMap(_.layer.children).map(start.root).distinct
      val childRoot = if childRoots.isEmpty then inputRoot else childRoots(picks(1) % childRoots.size)
      val graph = ExtractorLaws.agendaWorked(Vector(inputRoot, childRoot).zipWithIndex.foldLeft(start) { case (current, (target, index)) =>
        // The criterion an input, a term the graph already holds: an opaque
        // instruction outside the store has no layer to add.
        val criterion = lawInputs((picks(2) + index) % lawInputs.size)
        val storage = LawNativeSpecializer.stored(LawStorage(s"$index", criterion))
        val (withStorage, storageNode) = current.instructionAdded(storage)
        // A test assumption that the storage is the class's value, not a proof.
        withStorage.unionQueued(target, storageNode, ExtractorLaws.assumed, None)
      })
      val outputs = storageExtractor.extracted(storageIndex, graph, saturated.inputNodes, lawInputs, StopSignal.completedWith(stopped))
      Result.all(
        Result.diff(outputs.length, lawInputs.length)(_ == _) ::
          outputs.zip(saturated.inputNodes).toList.map((output, inputNode) =>
            Result.assert(ExtractorLaws.spelledIn(graph, output, graph.root(inputNode))).log(s"output $output")
          )
      )
  }

  stoppableProperty("on a run with no knowledge module each output is its input") { stopped =>
    for written <- inputs.forAll
    yield
      val saturated = run(library.index, written, Vector.empty, ExtractorLaws.largestBudget, StopSignal.completedWith(stopped))
      val outputs = extractor.extracted(library.index, saturated.graph, saturated.inputNodes, written, StopSignal.completedWith(stopped))
      Result.all(
        Result.diff(outputs.length, written.length)(_ == _) ::
          outputs.zip(written).toList.map((output, input) => Result.assert(Configured.same(output, input)).log(s"output $output, input $input"))
      )
  }

object ExtractorLaws:

  val knowledgeFile: String = "tests/library_fixtures/presets.lambdalattice"

  val assumed: Justification = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  @scala.annotation.tailrec
  def agendaWorked[C <: NativeSpecializer & Singleton](graph: EGraph[C]): EGraph[C] = graph.unionTaken match
    case Some((pending, rest)) => agendaWorked(rest.unionWorked(pending.first, pending.second, pending.justification, pending.made))
    case None                  => graph

  val largestBudget: Int = 200

  /** Whether the term is spelled in the class: it is a term of the class, or its layer is the shape of a member's with
    * each child spelled in the member's child's class. A layer is compared by its kind, a thunk's code, holes and number
    * of fillings, and a leaf by identity.
    */
  def spelledIn[C <: NativeSpecializer & Singleton](graph: EGraph[C], term: Configured[C], classRoot: Int)(using C): Boolean =
    val nodesByRoot = graph.liveNodes.groupBy(_.root)
    def layers(term: Configured[C]): Vector[LayerWith[Configured[C], Configured[C]]] =
      // A storage kept as a leaf is read as its leaf, its view not read.
      if term.heldAsLeaf && !graph.store.noinline.contains(term) then Vector(NoinlineLeaf(term))
      else
        val leaf = if graph.store.noinline.contains(term) then Vector(NoinlineLeaf(term)) else Vector.empty
        if term.opaque then leaf
        else
          leaf :+ (term.layer match
            case application @ gezi.ir.Apply(_, _) => application
            case parallel @ gezi.ir.Parallel(_, _) => parallel
            case choice @ gezi.ir.Choice(_, _)     => choice
            case thunk @ gezi.ir.Thunk(_, _, _)    => thunk
            case other                             => throw IllegalStateException(s"the term $term has the layer $other, which is no layer of the e-graph")
          )
    def sameShape(left: LayerWith[Any, Configured[C]], right: LayerWith[Any, Configured[C]]): Boolean = (left, right) match
      case (gezi.ir.Apply(_, _), gezi.ir.Apply(_, _))                       => true
      case (gezi.ir.Parallel(_, _), gezi.ir.Parallel(_, _))                 => true
      case (gezi.ir.Choice(_, _), gezi.ir.Choice(_, _))                     => true
      case (gezi.ir.Thunk(leftCode, leftHoles, leftFillings), gezi.ir.Thunk(rightCode, rightHoles, rightFillings)) =>
        leftCode == rightCode && leftHoles == rightHoles && leftFillings.size == rightFillings.size
      case (NoinlineLeaf(leftLeaf), NoinlineLeaf(rightLeaf))                => Configured.same(leftLeaf, rightLeaf)
      case _                                                                => false
    def spelled(term: Configured[C], classRoot: Int): Boolean =
      graph.instructionNode(term).exists(node => graph.root(node) == classRoot) ||
        layers(term).exists(layer =>
          nodesByRoot.getOrElse(classRoot, Vector.empty).exists(live =>
            sameShape(live.layer, layer) &&
            live.layer.children.lazyZip(layer.children).forall((child, childTerm) => spelled(childTerm, child))
          )
        )
    spelled(term, classRoot)
