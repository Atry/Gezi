package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StoreGenerators
import gezi.generatedinputs.StandInStorage
import gezi.generatedinputs.StandInStorages
import gezi.ir.Apply
import gezi.ir.Interned
import gezi.ir.IrLayer
import gezi.ir.NativeStorage
import gezi.ir.Parallel

/** A native storage of the tests, kept as a leaf, whose view throws when it is
  * read: the graph must take it without its view. Equal to itself only.
  */
final class PoisonedLeafStorage(
    value: StandInStorages.Term,
    criterionTerm: StandInStorages.Term
) extends StandInStorage:
  def standInCriterion: StandInStorages.Term = criterionTerm
  val closed: Boolean = true
  val suspensionFree: Boolean = true
  val handedOverWhole: Boolean = false
  protected val termChildren: IArray[AnyRef] = IArray(
    criterionTerm.representation
  )
  protected val constructorIndex: Int = 0
  val leafInEGraph: Boolean = true
  val constantSize: Boolean = true

  /** False: a stand-in of the tests forms no group. */
  def precedes(other: gezi.ir.NativeStorage): Boolean = false

  /** A stand-in is one object: equal to itself only, in the pool as outside it.
    */
  def contentHash: Int = System.identityHashCode(this)
  def sameContent(other: NativeStorage): Boolean = this eq other

/** The law of the pattern views of storage leaves: generated stores and
  * instructions (`StoreGenerators.store`), with k native storages kept as
  * leaves, each given to a generated function, its criterion one of the
  * generated instructions, and the same instructions with each storage replaced
  * by a fresh noinline stand-in, are added to empty graphs. Derived before the
  * run from the expansion (a storage leaf adds its criterion, already in the
  * graph, and one parallel over its leaf and its criterion; a stand-in adds its
  * leaf only; no input writes `s ∥ T`, s being made after the inputs): the
  * graph of the storages has exactly k nodes more; it records exactly k pattern
  * views, each the node `Parallel(s's node, T's node)`, and queues exactly k
  * unions, each a pattern view with its leaf; and no storage's view is read.
  * Its purpose is to catch a pattern view missing, made twice, made over the
  * wrong nodes or not united, and an expansion that reads a storage leaf's
  * view.
  */
class PatternViewLawTest extends GeneratedProperties:

  property(
    "each storage leaf adds exactly its pattern view, over its leaf and its criterion, united with the leaf"
  ) {
    for
      generated <- StoreGenerators.store.forAll
      count <- Gen.int(Range.linear(1, 3)).forAll
      picks <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.singleton(count * 3))
        .forAll
    yield
      val instructions = generated.instructions
      def picked(position: Int): StandInStorages.Term =
        instructions(picks(position) % instructions.size)
      val poisoned = (0 until count).toVector.map(index =>
        PoisonedLeafStorage(picked(3 * index), picked(3 * index + 1))
      )
      val storages = poisoned.map(StandInStorages.stored)
      val functions =
        (0 until count).toVector.map(index => picked(3 * index + 2))
      val standIns = (0 until count).toVector.map(index =>
        StandInStorages.opaque(s"stand-in $index")
      )
      def added(
          store: gezi.ir.Store[StandInStorages.type],
          leaves: Vector[StandInStorages.Term]
      ): (EGraph[StandInStorages.type], Vector[Int]) =
        val inputs = instructions ++ functions
          .zip(leaves)
          .map((function, leaf) => StandInStorages.application(function, leaf))
        val graph = inputs.foldLeft(
          EGraph.empty(store, Map.empty, explained = false)
        )((current, input) => current.instructionAdded(input)._1)
        (
          graph,
          leaves.map(leaf =>
            graph
              .instructionNode(leaf)
              .getOrElse(throw IllegalStateException(s"no node of $leaf"))
          )
        )
      val (withStorages, leafNodes) = added(generated.store, storages)
      val (withStandIns, _) = added(
        generated.store.copy(noinline = generated.store.noinline ++ standIns),
        standIns
      )
      val criterionNodes = poisoned.map(storage =>
        withStorages
          .instructionNode(storage.standInCriterion)
          .getOrElse(throw IllegalStateException("no criterion node"))
      )
      val views = leafNodes
        .zip(criterionNodes)
        .map((leaf, criterion) =>
          withStorages.patternViews.find(view =>
            withStorages.layer(view) eq gezi.ir.Interned
              .canonicalLayer(Parallel[Int](leaf, criterion))
          )
        )
      val queued = withStorages.unionQueue.toVector.collect {
        case PendingUnion(first, second, Justification.PatternView(leaf), _) =>
          (first, second, leaf)
      }
      Result
        .diff(withStorages.nodeCount, withStandIns.nodeCount + count)(_ == _)
        .and(Result.diff(withStorages.patternViews.size, count)(_ == _))
        .and(
          Result
            .assert(views.forall(_.isDefined))
            .log(s"a pattern view over the wrong nodes: $views")
        )
        .and(Result.diff(queued.map(_._3).sorted, leafNodes.sorted)(_ == _))
        .and(
          Result
            .assert(
              queued.forall((first, second, leaf) =>
                second == leaf && withStorages.patternViews.contains(first)
              )
            )
            .log(s"$queued")
        )
  }
