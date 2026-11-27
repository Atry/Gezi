package gezi.extraction

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Apply
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.NoinlineLeaf
import gezi.ir.Parallel
import gezi.ir.Store
import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import scala.concurrent.Future

/** The extraction under a model that settles a production's children to their
  * first entry above a bound on their numbers of entries
  * (`CostModel.settledChildren`), as a thunk's jointly read fillings are
  * settled (`gezi.strategies.ThunkCandidates`). Its purpose is to catch an
  * extraction whose passes settle differently: a later pass offered fewer
  * entries that enumerates where the first pass settled, finds a combination
  * below the first pass's fixed point and throws; or one that cannot make again
  * an entry the first pass kept at an early entering, enumerated before the
  * children had their final numbers of entries, and throws; and a settling that
  * leaks below the bound, where the least over every combination is kept.
  *
  * The graph: leaves L0, L1, L2 and L3 of reading 0 and of generated costs, L0
  * and L2 the first of their classes by size; an application costs one more
  * than its children and is of reading 1. The class A unites L0 and `L1 L1`,
  * the class B unites L2 and `L3 L3`, so each keeps two entries, one of each
  * reading; the root is `A B`, of reading 1 alone.
  *
  * Expected, derived before the run, at bound 2 (a root whose children have two
  * entries each, 4 > 2 combinations, settles both to their leaves; one whose B
  * has one entry so far enumerates its 2 combinations):
  *   - L0 and L2 of cost `heavy`, L1 and L3 of cost `light`, heavy above 1 + 2
  *     · light: both applications, of cost 1 + 2 · light, below the root's
  *     every key, are entered before it, so the root is entered at two entries
  *     each, settled, and costs 1 + 2 · heavy;
  *   - L0 of cost `heavy`, L1 of cost `light`, L2 of cost `leaf`, L3 of cost
  *     `costly`, with 1 + heavy + leaf < 1 + 2 · costly: the root, entered
  *     while B has only L2, before `L3 L3`, enumerates A's two entries, keeping
  *     2 + 2 · light + leaf; entered again at two entries each it settles to 1
  *     + heavy + leaf, which is more. The extraction must keep 2 + 2 · light +
  *     leaf, made again over the readings that entry read, and not throw.
  * At bound 4 nothing is settled, and the root of the first graph costs the
  * least over every combination, 1 + 2 · (1 + 2 · light).
  */
class SettledChildrenLawTest extends GeneratedProperties:

  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private final case class Settling(value: Int, reading: Int)

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  /** The model of the graph above: settles an application's children of more
    * than one entry when the product of their numbers of entries exceeds
    * `bound`.
    */
  private final class SettlingModel(
      weights: Map[Configured[C], Int],
      bound: Int
  ) extends StatelessCostModel[C, Settling]:
    def cost(shape: Shape[C], childCosts: Vector[Settling]): Settling =
      shape match
        case Shape.Node(_, NoinlineLeaf(leaf)) => Settling(weights(leaf), 0)
        case Shape.Node(_, Apply(_, _))        =>
          Settling(1 + childCosts.map(_.value).sum, 1)
        case other =>
          throw IllegalArgumentException(
            s"no production of the test graph: $other"
          )
    val ordering: Ordering[Settling] = Ordering.by(_.value)
    override def sameReading(left: Settling, right: Settling): Boolean =
      left.reading == right.reading
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      shape.children.map(_ => true)
    override def settledChildren(
        shape: Shape[C],
        entryCounts: Vector[Int]
    ): Vector[Boolean] = shape match
      case Shape.Node(_, Apply(_, _))
          if entryCounts.filter(_ > 1).product > bound =>
        entryCounts.map(_ > 1)
      case _ => shape.children.map(_ => false)
    override def candidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, Settling]]]
    ): Vector[Entry[C, Settling]] =
      val settled = settledChildren(shape, options.map(_.size))
      val offered = options
        .zip(settled)
        .map((entries, isSettled) =>
          if isSettled then Vector(firstOf(entries)) else entries
        )
      CostModel
        .combinations(offered)
        .map(chosen => Entry(cost(shape, chosen.map(_.cost)), shape, chosen))
    override def leastCandidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, Settling]]]
    ): Vector[Entry[C, Settling]] =
      CostModel.leastOfEachReading(this, candidates(shape, options))

  private def firstOf(entries: Vector[Entry[C, Settling]]): Entry[C, Settling] =
    entries.reduce((kept, next) =>
      val bySize = next.size.compare(kept.size)
      if bySize < 0 || (bySize == 0 && ContentOrder.compare(next, kept) < 0)
      then next
      else kept
    )

  /** The root's entry of reading 1, the leaves L0 to L3 of the costs given,
    * under the model of `bound`.
    */
  private def rootCost(
      costs: Vector[Int],
      bound: Int,
      stopped: Future[Unit]
  ): Int =
    val leaves = Vector.tabulate(4)(number =>
      NoFacts.opaque(s"settled-children-leaf$number")
    )
    val Vector(heavyFirst, lightFirst, heavySecond, lightSecond) =
      leaves: @unchecked
    val weights = leaves.zip(costs).toMap
    val firstApplied = NoFacts.application(lightFirst, lightFirst)
    val secondApplied = NoFacts.application(lightSecond, lightSecond)
    val start = leaves.foldLeft(
      EGraph.empty(
        Store(noinline = leaves.toSet, gezi.ir.TermConstruction(NoFacts)),
        Map.empty,
        explained = false
      )
    )((graph, leaf) => graph.instructionAdded(leaf)._1)
    val (withFirst, firstNode) = start.instructionAdded(firstApplied)
    val (withSecond, secondNode) = withFirst.instructionAdded(secondApplied)
    val united = withSecond
      .unionWorked(
        withSecond.instructionNode(heavyFirst).getOrElse(fail("no node of L0")),
        firstNode,
        lemma,
        None
      )
      .unionWorked(
        withSecond
          .instructionNode(heavySecond)
          .getOrElse(fail("no node of L2")),
        secondNode,
        lemma,
        None
      )
    val (graph, rootNode) =
      united.instructionAdded(NoFacts.application(heavyFirst, heavySecond))
    val extracted =
      CountedExtraction
        .fixed(
          graph,
          Set.empty,
          SettlingModel(weights, bound),
          StopSignal.completedWith(stopped)
        )
        .getOrElse(fail("the extraction was stopped"))
    val entries = extracted.classes
      .getOrElse(graph.root(rootNode), fail("the root has no entries"))
      .entries
    val Vector(entry) = entries.filter(_.cost.reading == 1): @unchecked
    entry.cost.value

  stoppableProperty(
    "above the bound a root entered at its final numbers of entries settles, and below it the root is the least over every combination"
  ) { stopped =>
    for
      light <- Gen.int(Range.linear(1, 3)).forAll
      heavy <- Gen.int(Range.linear(2 + 2 * light, 20)).forAll
    yield Result.all(
      List(
        Result
          .diff(
            rootCost(Vector(heavy, light, heavy, light), 2, stopped),
            1 + 2 * heavy
          )(_ == _)
          .log("bound 2: both children settled to their leaves"),
        Result
          .diff(
            rootCost(Vector(heavy, light, heavy, light), 4, stopped),
            1 + 2 * (1 + 2 * light)
          )(_ == _)
          .log("bound 4: the least over every combination")
      )
    )
  }

  stoppableProperty(
    "an entry the first pass kept at an early, enumerated entering is kept, and no pass throws"
  ) { stopped =>
    for
      light <- Gen.int(Range.linear(1, 3)).forAll
      heavy <- Gen.int(Range.linear(2 + 2 * light, 20)).forAll
      leaf <- Gen.int(Range.linear(1, 5)).forAll
      // 1 + 2 · costly above 1 + heavy + leaf, so `L3 L3` is entered after the
      // root's first entering.
      costly <- Gen.int(Range.linear((heavy + leaf) / 2 + 1, 30)).forAll
    yield Result.diff(
      rootCost(Vector(heavy, light, leaf, costly), 2, stopped),
      2 + 2 * light + leaf
    )(_ == _)
  }

  /** The model of the superseded-node graph below: a leaf costs its weight and
    * has its own reading; an application costs one more than its children and
    * has reading 2 whatever its children's (a reading function that is not
    * injective), its children settled to their first entry when the product of
    * their numbers of entries above one exceeds 4; a parallel costs one more
    * than its left child, its right child unpriced, and has reading 1.
    */
  private final class SupersededNodeModel(
      weights: Map[Configured[C], Int],
      readings: Map[Configured[C], Int]
  ) extends StatelessCostModel[C, Settling]:
    def cost(shape: Shape[C], childCosts: Vector[Settling]): Settling =
      shape match
        case Shape.Node(_, NoinlineLeaf(leaf)) =>
          Settling(weights(leaf), readings(leaf))
        case Shape.Node(_, Apply(_, _)) =>
          Settling(1 + childCosts.map(_.value).sum, 2)
        case Shape.Node(_, Parallel(_, _)) =>
          val Vector(left, _) = childCosts: @unchecked
          Settling(1 + left.value, 1)
        case other =>
          throw IllegalArgumentException(
            s"no production of the superseded-node graph: $other"
          )
    val ordering: Ordering[Settling] = Ordering.by(_.value)
    override def sameReading(left: Settling, right: Settling): Boolean =
      left.reading == right.reading
    def pricedChildren(shape: Shape[C]): Vector[Boolean] = shape match
      case Shape.Node(_, Parallel(_, _)) => Vector(true, false)
      case _                             => shape.children.map(_ => true)
    override def settledChildren(
        shape: Shape[C],
        entryCounts: Vector[Int]
    ): Vector[Boolean] = shape match
      case Shape.Node(_, Apply(_, _))
          if entryCounts.filter(_ > 1).product > 4 =>
        entryCounts.map(_ > 1)
      case _ => shape.children.map(_ => false)
    override def candidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, Settling]]]
    ): Vector[Entry[C, Settling]] =
      val settled = settledChildren(shape, options.map(_.size))
      val offered = options
        .zip(settled)
        .map((entries, isSettled) =>
          if isSettled then Vector(firstOf(entries)) else entries
        )
      CostModel
        .combinations(offered)
        .map(chosen => Entry(cost(shape, chosen.map(_.cost)), shape, chosen))
    override def leastCandidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, Settling]]]
    ): Vector[Entry[C, Settling]] =
      CostModel.leastOfEachReading(this, candidates(shape, options))

  /** A reading the first pass kept rests on an entry its class later
    * superseded, made by a production settled at the end. Its purpose is to
    * catch directives recorded from the classes' kept entries alone, not from
    * every node of their trees.
    *
    * The graph: leaves `a` (`heavyLeaf`, reading 0, cost `heavy`), `b`
    * (`lightLeaf`, reading 6, cost `light`), `w` (`cheapLeaf`, reading 3, cost
    * 1) and `c` (`lateLeaf`, reading 7, cost `late`). Q (`call`) is `a w`, in
    * the class Y; P (`guarded`) is `b ∥ Q`, united with `a` in the class X; the
    * class W unites `w`, `c ∥ c` (reading 1) and `c c` (reading 2). So Q reads
    * X and W, and P reads Y at its unpriced position. A leaf's entry is made at
    * the start; the others come in the order of their costs.
    *
    * Expected, derived before the run, for light below heavy − 1 and late above
    * heavy + 1. The first pass makes Q(a, w) of reading 2 at 2 + heavy, from it
    * P's E = P(b, Q(a, w)) of reading 1 at 1 + light, then, X holding two
    * entries and W one (product 2), Q(E, w) of reading 2 at 3 + light, below 2
    * + heavy, which Y keeps. W's entries at 1 + late and 1 + 2 · late come
    * after: at two entries of W the product is 4 and Q enumerates, at three it
    * is 6 > 4 and Q settles to its first entries, Q(a, w) at 2 + heavy, which
    * is more. Y's kept tree Q(E, w) holds Q(a, w), superseded. Rebuilding Y's
    * reading 2 needs both combinations of Q, (0, 3) and (1, 3). Recorded from
    * every node of the kept trees, the second run makes them again and Y's
    * reading 2 costs 3 + light. Recorded from the classes' entries alone, it
    * has only (1, 3): X's reading 1 needs P, P needs Y, Y needs Q over X's
    * reading 1, Y has no entry, and the check of the second run throws.
    */
  private def supersededCost(
      light: Int,
      heavy: Int,
      late: Int,
      stopped: Future[Unit]
  ): Int =
    val Vector(heavyLeaf, lightLeaf, cheapLeaf, lateLeaf) =
      Vector("a", "b", "w", "c").map(name =>
        NoFacts.opaque(s"settled-children-superseded-$name")
      ): @unchecked
    val weights = Map(
      heavyLeaf -> heavy,
      lightLeaf -> light,
      cheapLeaf -> 1,
      lateLeaf -> late
    )
    val readings =
      Map(heavyLeaf -> 0, lightLeaf -> 6, cheapLeaf -> 3, lateLeaf -> 7)
    val call = NoFacts.application(heavyLeaf, cheapLeaf)
    val guarded = NoFacts.parallel(lightLeaf, call)
    val paralleled = NoFacts.parallel(lateLeaf, lateLeaf)
    val applied = NoFacts.application(lateLeaf, lateLeaf)
    val leaves = Vector(heavyLeaf, lightLeaf, cheapLeaf, lateLeaf)
    val start = leaves.foldLeft(
      EGraph.empty(
        Store(noinline = leaves.toSet, gezi.ir.TermConstruction(NoFacts)),
        Map.empty,
        explained = false
      )
    )((graph, leaf) => graph.instructionAdded(leaf)._1)
    val added = Vector(guarded, paralleled, applied).foldLeft(start)(
      (graph, instruction) => graph.instructionAdded(instruction)._1
    )
    def node(graph: EGraph[C], instruction: Configured[C]): Int = graph
      .instructionNode(instruction)
      .getOrElse(fail(s"no node of $instruction"))
    val graph = added
      .unionWorked(node(added, heavyLeaf), node(added, guarded), lemma, None)
      .unionWorked(node(added, cheapLeaf), node(added, paralleled), lemma, None)
      .unionWorked(node(added, cheapLeaf), node(added, applied), lemma, None)
    val extracted =
      CountedExtraction
        .fixed(
          graph,
          Set.empty,
          SupersededNodeModel(weights, readings),
          StopSignal.completedWith(stopped)
        )
        .getOrElse(fail("the extraction was stopped"))
    val entries = extracted.classes
      .getOrElse(graph.root(node(graph, call)), fail("Y has no entries"))
      .entries
    val Vector(entry) = entries.filter(_.cost.reading == 2): @unchecked
    entry.cost.value

  stoppableProperty(
    "a reading kept over an entry its class superseded, made by a production settled at the end, is made again"
  ) { stopped =>
    for
      light <- Gen.int(Range.linear(1, 3)).forAll
      heavy <- Gen.int(Range.linear(light + 2, 12)).forAll
      late <- Gen.int(Range.linear(heavy + 2, 40)).forAll
    yield Result.diff(supersededCost(light, heavy, late, stopped), 3 + light)(
      _ == _
    )
  }
