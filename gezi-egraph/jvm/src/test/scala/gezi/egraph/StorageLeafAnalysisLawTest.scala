package gezi.egraph

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.StoreGenerators
import gezi.generatedinputs.StandInStorages
import gezi.ir.Interned
import gezi.ir.IrLayer
import gezi.ir.NativeStorage
import gezi.ir.NoinlineLeaf

/** The law of the storage analysis (`StorageLeafAnalysis`): generated
  * instructions and k storage leaves, each of a criterion drawn among a few
  * generated instructions, are added to a graph that keeps the analysis, and
  * generated pairs of their nodes are united, the agenda worked after each
  * union. Derived before the run, with an oracle that reads the classes'
  * members directly: every class's kept value is, for each criterion, the one
  * storage leaf of that criterion among the class's live members, or `Conflict`
  * when the class holds two distinct ones; a class with no storage leaf keeps
  * nothing. Its purpose is to catch an analysis that misses a leaf, keeps a
  * leaf of another class, reports a conflict where the leaves agree, or none
  * where they differ.
  */
class StorageLeafAnalysisLawTest extends GeneratedProperties:

  private val analysis = StorageLeafAnalysis(StandInStorages)

  /** The value the class's live members give directly. */
  private def scanned(
      graph: EGraph[StandInStorages.type],
      root: Int
  ): StorageLeaves[StandInStorages.type] =
    StorageLeaves(
      graph
        .classMembers(root)
        .map(_.layer)
        .collect { case NoinlineLeaf(instruction) =>
          instruction.representation: AnyRef
        }
        .collect {
          case storage: NativeStorage if storage.leafInEGraph => storage
        }
        .distinct
        .groupBy(storage => StandInStorages.criterionOf(storage))
        .map((criterion, storages) =>
          criterion -> (storages match
            case Vector(one) => StorageLeafState.Held(one)
            case _           => StorageLeafState.Conflict)
        )
    )

  @scala.annotation.tailrec
  private def agendaWorked(
      graph: EGraph[StandInStorages.type]
  ): EGraph[StandInStorages.type] = graph.unionTaken match
    case Some((pending, rest)) =>
      agendaWorked(
        rest.unionWorked(
          pending.first,
          pending.second,
          pending.justification,
          pending.made
        )
      )
    case None => graph

  property(
    "each class keeps its storage leaves by criterion, two distinct ones of a criterion in conflict"
  ) {
    for
      generated <- StoreGenerators.store.forAll
      count <- Gen.int(Range.linear(1, 6)).forAll
      picks <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.singleton(count * 2))
        .forAll
      unions <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.linear(0, 8))
        .forAll
    yield
      val instructions = generated.instructions
      val criteria = instructions.take(2)
      val storages = (0 until count).toVector.map(index =>
        StandInStorages.stored(
          PoisonedLeafStorage(
            instructions(picks(2 * index) % instructions.size),
            criteria(picks(2 * index + 1) % criteria.size)
          )
        )
      )
      val start = EGraph
        .empty(generated.store, Map.empty, explained = false)
        .analysed(analysis)
      val added = agendaWorked(
        (instructions ++ storages).foldLeft(start)((graph, input) =>
          graph.instructionAdded(input)._1
        )
      )
      val nodes = (instructions ++ storages).map(input =>
        added
          .instructionNode(input)
          .getOrElse(throw IllegalStateException(s"no node of $input"))
      )
      val united = unions
        .grouped(2)
        .collect { case List(first, second) =>
          (nodes(first % nodes.size), nodes(second % nodes.size))
        }
        .foldLeft(added)((graph, pair) =>
          agendaWorked(
            graph.unionWorked(pair._1, pair._2, Justification.Congruence, None)
          )
        )
      val roots = (0 until united.nodeCount).map(united.root).distinct.toVector
      Result.all(
        roots.toList.map(root =>
          Result.diff(
            united.analysisValue(analysis, root).getOrElse(analysis.identity),
            scanned(united, root)
          )(_ == _)
        )
      )
  }

  property("joined is commutative, associative and idempotent") {
    for
      generated <- StoreGenerators.store.forAll
      picks <- Gen
        .int(Range.linear(0, Int.MaxValue))
        .list(Range.singleton(9))
        .forAll
    yield
      val instructions = generated.instructions
      val criteria = instructions.take(2)
      def value(offset: Int): StorageLeaves[StandInStorages.type] =
        val storage = StandInStorages.stored(
          PoisonedLeafStorage(
            instructions(picks(offset) % instructions.size),
            criteria(picks(offset + 1) % criteria.size)
          )
        )
        if picks(offset + 2) % 3 == 0 then analysis.identity
        else analysis.made(NoinlineLeaf(storage))
      val (a, b, c) = (value(0), value(3), value(6))
      val join = analysis.joined
      Result
        .diff(join(a, b), join(b, a))(_ == _)
        .and(Result.diff(join(join(a, b), c), join(a, join(b, c)))(_ == _))
        .and(Result.diff(join(a, a), a)(_ == _))
        .and(Result.diff(join(a, analysis.identity), a)(_ == _))
  }
