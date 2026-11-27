package com.yang_bo.gezi.backendcomparison

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import com.yang_bo.gezi.egraph.EGraph
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.GeneratedStore
import com.yang_bo.gezi.generatedinputs.OrientationGenerators
import com.yang_bo.gezi.generatedinputs.StandInStorages
import com.yang_bo.gezi.generatedinputs.StoreGenerators
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.Interned
import com.yang_bo.gezi.ir.IrLayer
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.saturation.ConstantStorageStop
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.saturation.StopSignal

/** The law of a round's constant storage stop (`ConstantStorageStop`), delta by
  * delta, against the naive matching as oracle: on a graph whose classes hold
  * storages of constant size, for every node the stop does not hide and every
  * key, the instances (orientation, root class, classes of the essential
  * metavariables) the program finds from that node through the stop's view are
  * exactly those it finds from it on the graph itself that have a naive
  * derivation (`NaiveMatching.derivations`) reading that node (the node it
  * takes at a layer, or the node's class as holding a closure) and no hidden
  * node (no node of a stopped class but its pattern views, no stopped class as
  * holding a closure). Derived before the run: the stop's view answers the
  * graph's answers less the hidden nodes and the stopped classes' closures, so
  * a run from a node through the view is a run on the graph whose derivation
  * reads that node and nothing hidden, and every such run goes through the
  * view. Each input is a generated store and its orientations, saturated, then
  * generated storage leaves (poisoned: their views throw) each united with the
  * root class of a naive match where there is one, so that the leaf's class
  * hides a member some derivation reads. The stopped classes are checked
  * independently of the predicate both sides share: they are exactly the
  * classes of the leaves of constant size, besides which one leaf not of
  * constant size is united into a matched class too and stops nothing of its
  * own. The law is per delta, as the saturation matches: a stop that cut the
  * climb from a stopped class's pattern view to its users would lose a consumer
  * found from that view, though the consumer's own node still finds it. Its
  * purpose is to catch a stop that hides too much or too little, the oracle
  * sharing no code with the view or the program.
  */
class ConstantStorageStopMatchingLawTest
    extends com.yang_bo.gezi.generatedinputs.FailFastSuite
    with GeneratedProperties:

  private type C = StandInStorages.type

  private given StandInStorages.type = StandInStorages

  stoppableProperty(
    "a round that stops finds exactly the naive matches that read no hidden node",
    _.copy(testLimit = SuccessCount(300))
  ) { stopped =>
    for
      generated <- StoreGenerators.store.forAll
      orientations <- OrientationGenerators.orientationsOver(generated).forAll
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      picks <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.singleton(leafCount))
        .forAll
    yield matchesAgree(
      generated,
      orientations,
      picks.toVector,
      StopSignal.completedWith(stopped)
    )
  }

  private def matchesAgree(
      generated: GeneratedStore,
      orientations: Vector[Orientation[C]],
      picks: Vector[Int],
      stop: StopSignal
  ): Result =
    val criteria = picks.indices.toVector.map(position =>
      StandInStorages.opaque(s"criterion $position")
    )
    val storages = criteria.map(criterion =>
      StandInStorages.stored(PoisonedLeafStorage(criterion))
    )
    val growing = StandInStorages.opaque("criterion of a growing storage")
    val growingStorage =
      StandInStorages.stored(PoisonedLeafStorage(growing, constantSize = false))
    val store = Store(
      generated.store.noinline ++ criteria + growing,
      com.yang_bo.gezi.ir.TermConstruction(StandInStorages)
    )
    val program = Indexing.program(orientations, generated.codes)
    val compiled = ClosureCompilation.compiled(program)
    val empty = Saturation.initialGraph(
      store,
      Orientations.headArityBounds(orientations),
      Vector.empty,
      explained = false
    )
    val initial = empty.analysed(empty.storageLeaves)
    val (withInputs, _) = Saturation.inputsAdded(
      initial,
      generated.instructions ++ storages :+ growingStorage
    )
    val (saturated, _) = Saturation.saturated(
      program,
      compiled,
      BuiltInRule.beforeOptIn,
      withInputs,
      budget = 40,
      stop
    )
    val matchedRoots = (for
      orientation <- orientations
      root <- saturated.liveNodes.map(_.root).distinct
      if NaiveMatching
        .matches(saturated, orientation.matched, root, Map.empty)
        .nonEmpty
    yield root).distinct
    val targets = picks.map(pick =>
      if matchedRoots.nonEmpty then matchedRoots(pick % matchedRoots.size)
      else saturated.liveNodes(pick % saturated.liveNodes.size).root
    )
    val united = (storages :+ growingStorage)
      .zip(targets :+ targets.head)
      .foldLeft(saturated)((graph, pair) =>
        val (storage, target) = pair
        val leaf = graph
          .instructionNode(storage)
          .getOrElse(throw IllegalStateException(s"no node of $storage"))
        Saturation.agendaWorked(
          program,
          compiled,
          BuiltInRule.beforeOptIn,
          graph.unionQueued(
            graph.root(target),
            leaf,
            Justification.Congruence,
            None
          )
        )
      )
    val graph = united.withConstantStorageStop(true)
    val view = ConstantStorageStop.view(graph)
    def keyOf(matched: com.yang_bo.gezi.ematching.Match) =
      (
        matched.orientation,
        graph.root(matched.root),
        orientations(matched.orientation).essential.map(index =>
          matched.bindings(index).map(graph.root)
        )
      )
    val clean = for
      orientation <- orientations
      root <- graph.liveNodes.map(_.root).distinct
      derivation <- NaiveMatching.derivations(
        graph,
        orientation.matched,
        root,
        NaiveMatching.Derivation(Map.empty, Set.empty, Set.empty)
      )
      if derivation.nodesRead.forall(node =>
        !ConstantStorageStop.hidden(graph, node)
      ) &&
        derivation.closuresRead.forall(closure =>
          !ConstantStorageStop.stopped(graph, closure)
        )
    yield (
      (
        orientation.index,
        root,
        orientation.essential.map(derivation.bindings.get)
      ),
      derivation
    )
    val disagreements = for
      (kind, key) <- program.seeds.keySet.toVector
      node <- graph.liveNodes
        .map(_.node)
        .filterNot(ConstantStorageStop.hidden(graph, _))
      throughView = compiled
        .matches(kind, key, view, node)
        .found
        .map(keyOf)
        .toSet
      onGraph = compiled.matches(kind, key, graph, node).found.map(keyOf).toSet
      readingNode = clean.collect {
        case (instance, derivation)
            if derivation.nodesRead.contains(node) || derivation.closuresRead
              .contains(graph.root(node)) =>
          instance
      }.toSet
      if throughView != onGraph.intersect(readingNode)
    yield (kind, key, node, throughView, onGraph.intersect(readingNode))
    def leafRoot(storage: StandInStorages.Term) = graph.root(
      graph
        .instructionNode(storage)
        .getOrElse(throw IllegalStateException(s"no node of $storage"))
    )
    val stoppedRoots = graph.liveNodes
      .map(_.root)
      .distinct
      .filter(ConstantStorageStop.stopped(graph, _))
      .toSet
    Result
      .diff(stoppedRoots, storages.map(leafRoot).toSet)(_ == _)
      .log("the stopped classes are those of the leaves of constant size")
      .and(
        Result
          .assert(disagreements.isEmpty)
          .log(s"disagreements: ${disagreements.take(3)}")
      )
