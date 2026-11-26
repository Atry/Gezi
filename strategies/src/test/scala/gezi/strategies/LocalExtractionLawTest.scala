package gezi.strategies

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.extraction.CostModel
import gezi.extraction.Extraction
import gezi.extraction.StatelessCostModel
import gezi.extraction.Shape
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.NoinlineLeaf
import gezi.ir.Store
import gezi.ir.{Apply, Choice, Parallel, Thunk}
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.PropertyT
import hedgehog.core.SuccessCount
import scala.util.Failure
import scala.util.Success
import scala.util.Try

/** The laws of `LocalExtraction.spelled` on generated graphs. Each graph
  * starts from a few noinline leaves and takes a generated sequence of
  * steps: an instruction added (an application, a parallel, a choice, or the
  * constant closure `λ_. b` of an instruction b added before), two nodes
  * united, or a β cycle: `(λ_. b) a` added and united with b, so that b's
  * class holds an application whose function's class is a closure whose
  * filling is b's class again, the shape of the witness of 2026-11-21
  * (class 7683's best `Apply(8173, 7361)`, class 8173's best
  * `Thunk(Slot, [Ignored], [7683])`); or a judgment absorbed:
  * `b + (b ∥ t)` added and united with b, the choice its class absorbs
  * (`Extraction.absorbedChoice`), which is no production and through which
  * `LocalExtraction` does not read, as a typing's judgments `x + (x ∥ t)`
  * are, and which closes a cycle through b's class that only that choice
  * reads. A cost is an integer: a generated
  * weight of the production's kind plus its children's costs, a generated
  * bit of each kind leaving its last child unpriced, so that the constant
  * closure can cost the same whatever its filling costs and the cycle be
  * cheaper than the class's finite productions, which is what made the
  * relaxation that `finalized` replaced keep a cycle of best entries.
  *
  * Each union is followed, in a graph closed under congruence, by the
  * unions it queues; a graph not closed is left with them queued, as a
  * saturation stopped mid-way leaves it, and there a class can hold no
  * live node with a finite derivation: its only finite node a duplicate of a
  * node of another class, its live nodes a cycle.
  *
  * (1) On graphs closed under congruence, spelling every class of the
  * graph in turn, the spelling cache handed from one to the next as a pass
  * of write-backs hands it, ends; each spelling, added to the graph, is a
  * node of the class it spells; and no subterm of a spelling (a name taken
  * as a leaf) is in the class of a term that encloses it. Its purpose is to
  * catch best entries that form a cycle, which made the spelling run forever
  * (the witness), or a spelling that is not its class's.
  *
  * (3) On graphs not closed, spelling every class in turn ends; a class
  * with a finite derivation by live nodes (or a name) is spelled, and one
  * with none fails with the `IllegalStateException` of a class with no
  * entry. Its purpose is to catch a class with no finite derivation that
  * loops or is not refused. (A re-added spelling is not compared with its
  * class there: in a graph not closed, two classes can hold the same layer.)
  *
  * (2) On acyclic graphs, closed or not, (a union only of two classes neither of which
  * reads the other, no β cycle, a cycle only through an absorbed judgment) under a superior model (every child priced,
  * so that a production costs no less than each child), each class's
  * spelling costs the least cost of its finite derivations by live nodes
  * that are productions, absorbed judgments left out (a class with none
  * fails as in (1)), the cost
  * computed by recursion over the acyclic graph: on an acyclic graph that is
  * the unique solution of the equations whose fixed point the relaxation
  * reached, so this is the cost the relaxation gave. Costs are compared, not
  * spellings: among productions of equal cost the relaxation kept the first
  * in its order, while `finalized` can finalize a class before a child of
  * its equal-cost first production is finalized, and so keep a later one.
  * Its purpose is to catch a finalization that fixes a class before its
  * least candidate is offered, or offers a production before its children
  * are final, and a walk that leaves out a class some production reads.
  *
  * (4) As (2), with every class of a graph spelled in turn from the cache a
  * pass over an earlier graph left, the graph the earlier one with more
  * steps taken on it, carried by `LocalExtraction.carriedCache`
  * (`SpellingRetention.KeptAcrossPasses`). Its purpose is to catch an
  * entry kept for a class that a later step changed, or that reads a changed
  * class: a step that adds a cheaper production below it leaves the kept
  * entry dearer than the least.
  *
  * (5) As (1), from a carried cache: on graphs closed under congruence, with
  * β cycles in either graph, every spelling is a term of its class. Its
  * purpose is to catch a kept entry spelled into a class it is not a term
  * of, such as an entry keyed by a root a union absorbed.
  */
class LocalExtractionLawTest extends GeneratedProperties:

  private given NoFacts.type = NoFacts

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  private val extraction = LocalExtraction(Vector(Compression.at[gezi.ir.NoFacts.type]), _ => Set.empty, SpellingRetention.KeptWithinAPass)

  /** A step of a generated graph; the numbers pick among the instructions or
    * the nodes made so far, modulo their count.
    */
  private enum Step:
    case Applied(function: Int, argument: Int)
    case Paralleled(left: Int, right: Int)
    case Chosen(left: Int, right: Int)
    case ConstantClosure(body: Int)
    case United(first: Int, second: Int)
    case BetaCycle(body: Int, argument: Int)
    case Absorbed(body: Int, criterion: Int)

  private val index = Gen.int(Range.linear(0, 1000))

  private val acyclicStep: Gen[Step] = Gen.choice1(
    for function <- index; argument <- index yield Step.Applied(function, argument),
    for left <- index; right <- index yield Step.Paralleled(left, right),
    for left <- index; right <- index yield Step.Chosen(left, right),
    index.map(Step.ConstantClosure(_)),
    for first <- index; second <- index yield Step.United(first, second),
    for body <- index; criterion <- index yield Step.Absorbed(body, criterion)
  )

  private val anyStep: Gen[Step] = Gen.frequency1(
    5 -> acyclicStep,
    1 -> (for body <- index; argument <- index yield Step.BetaCycle(body, argument))
  )

  /** The number of kinds of productions `kind` tells apart. */
  private val kindCount = 6

  private def kind(layer: Layer[Any]): Int = layer match
    case Apply(_, _)     => 0
    case Parallel(_, _)  => 1
    case Choice(_, _)    => 2
    case Thunk(_, _, _)  => 3
    case NoinlineLeaf(_) => 4
    case view: gezi.ir.StorageView[?] => throw IllegalStateException(s"a node's layer is never a storage's view: $view")

  private val nameKind = 5

  private val bits: Gen[Vector[Int]] = Gen.int(Range.constant(0, 1)).list(Range.singleton(kindCount)).map(_.toVector)

  private val weights: Gen[Vector[Int]] = Gen.int(Range.constant(0, 2)).list(Range.singleton(kindCount)).map(_.toVector)

  /** A production's weight by its kind plus its children's costs, its last
    * child left out where `unpricedLast` of its kind is 1.
    */
  private final class Weighted(weights: Vector[Int], unpricedLast: Vector[Int]) extends StatelessCostModel[NoFacts.type, Int]:
    def cost(shape: Shape[NoFacts.type], childCosts: Vector[Int]): Int =
      val shapeKind = shape match
        case Shape.Node(_, layer) => kind(layer)
        case Shape.Name(_)        => nameKind
        case other                => throw IllegalStateException(s"the local extraction lists names and nodes only, not $other")
      val priced = if unpricedLast(shapeKind) == 1 then childCosts.dropRight(1) else childCosts
      weights(shapeKind) + priced.sum
    val ordering: Ordering[Int] = Ordering.Int
    def pricedChildren(shape: Shape[NoFacts.type]): Vector[Boolean] = shape.children.map(_ => true)

  private final case class Generated(graph: EGraph[NoFacts.type], instructions: Vector[Configured[NoFacts.type]])

  /** The graph of the steps; a union of two classes one of which reads the
    * other left out when `acyclic`; the unions each union queues (those of
    * the congruence) worked at once when `closed`.
    */
  private def generated(leafCount: Int, steps: List[Step], acyclic: Boolean, closed: Boolean): Generated =
    val leaves = Vector.tabulate(leafCount)(number => NoFacts.opaque(s"local-extraction-leaf$number"))
    val empty = EGraph.empty(Store(noinline = leaves.toSet, gezi.ir.TermConstruction(gezi.ir.NoFacts)), Map.empty, explained = false)
    continued(Generated(leaves.foldLeft(empty)((graph, leaf) => graph.instructionAdded(leaf)._1), leaves), steps, acyclic, closed)

  /** The graph given with the steps taken on it, as `generated` takes them. */
  private def continued(start: Generated, steps: List[Step], acyclic: Boolean, closed: Boolean): Generated =
    def united(graph: EGraph[NoFacts.type], first: Int, second: Int): EGraph[NoFacts.type] =
      val once = graph.unionWorked(first, second, lemma, None)
      if closed then unionsWorked(once) else once
    steps.foldLeft(start)((current, step) =>
      def instruction(number: Int): Configured[NoFacts.type] = current.instructions(number % current.instructions.size)
      def added(instruction: Configured[NoFacts.type]): Generated =
        Generated(current.graph.instructionAdded(instruction)._1, current.instructions :+ instruction)
      def constantClosure(body: Configured[NoFacts.type]): Configured[NoFacts.type] = NoFacts.thunkOrInstance(Code.Slot(0), Vector(Hole.Ignored), Vector(body))
      step match
        case Step.Applied(function, argument) => added(NoFacts.application(instruction(function), instruction(argument)))
        case Step.Paralleled(left, right)     => added(NoFacts.parallel(instruction(left), instruction(right)))
        case Step.Chosen(left, right)         => added(NoFacts.choice(instruction(left), instruction(right)))
        case Step.ConstantClosure(body)       => added(constantClosure(instruction(body)))
        case Step.United(first, second) =>
          val nodes = current.graph.nodeCount
          val (firstRoot, secondRoot) = (current.graph.root(first % nodes), current.graph.root(second % nodes))
          if acyclic && (reaches(current.graph, firstRoot, secondRoot) || reaches(current.graph, secondRoot, firstRoot)) then current
          else current.copy(graph = united(current.graph, first % nodes, second % nodes))
        case Step.Absorbed(body, criterion) =>
          val judged = instruction(body)
          val choice = NoFacts.choice(judged, NoFacts.parallel(judged, instruction(criterion)))
          if current.graph.instructionNode(choice).isDefined then current
          else
            val (withChoice, choiceNode) = current.graph.instructionAdded(choice)
            val judgedNode = withChoice.instructionNode(judged).getOrElse(throw IllegalStateException(s"$judged was not filed"))
            Generated(united(withChoice, choiceNode, judgedNode), current.instructions :+ choice)
        case Step.BetaCycle(body, argument) =>
          val application = NoFacts.application(constantClosure(instruction(body)), instruction(argument))
          val (withApplication, applicationNode) = current.graph.instructionAdded(application)
          val (withBody, bodyNode) = withApplication.instructionAdded(instruction(body))
          Generated(united(withBody, applicationNode, bodyNode), current.instructions :+ application)
    )

  /** The graph with the unions on its queue worked, and those they queue. */
  @scala.annotation.tailrec
  private def unionsWorked(graph: EGraph[NoFacts.type]): EGraph[NoFacts.type] = graph.unionTaken match
    case Some((pending, rest)) =>
      unionsWorked(rest.unionWorked(pending.first, pending.second, pending.justification, pending.made))
    case None => graph

  /** The classes the class reads, itself included. */
  private def readClasses(graph: EGraph[NoFacts.type], root: Int): Set[Int] =
    @scala.annotation.tailrec
    def visited(pending: List[Int], seen: Set[Int]): Set[Int] = pending match
      case Nil                           => seen
      case next :: rest if seen(next)    => visited(rest, seen)
      case next :: rest =>
        val children = graph.classMembers(next).flatMap(_.layer.children.map(graph.root)).toList
        visited(children ::: rest, seen + next)
    visited(List(root), Set.empty)

  /** Whether the class `from` reads the class `to`, or is it. */
  private def reaches(graph: EGraph[NoFacts.type], from: Int, to: Int): Boolean = readClasses(graph, from).contains(to)

  /** The roots of the graph's classes, in the order of their first node. */
  private def roots(graph: EGraph[NoFacts.type]): Vector[Int] = graph.liveNodes.map(_.root).distinct

  /** Every class of the graph spelled in turn, the cache handed on from
    * each spelling that succeeds; a spelling that throws leaves it as it was.
    */
  private def spellings(
      prepared: LocalExtraction.Prepared[NoFacts.type, Int],
      graph: EGraph[NoFacts.type],
      classes: Vector[Int]
  ): Vector[(Int, Try[Configured[NoFacts.type]])] =
    spellingsFrom(prepared, graph, classes, SpellingCache.empty[NoFacts.type, Int])._2

  /** `spellings` from the cache given, with the cache the last spelling left. */
  private def spellingsFrom(
      prepared: LocalExtraction.Prepared[NoFacts.type, Int],
      graph: EGraph[NoFacts.type],
      classes: Vector[Int],
      start: SpellingCache[NoFacts.type, Int]
  ): (SpellingCache[NoFacts.type, Int], Vector[(Int, Try[Configured[NoFacts.type]])]) =
    classes.foldLeft((start, Vector.empty[(Int, Try[Configured[NoFacts.type]])])) { case ((cache, spelled), root) =>
      Try(extraction.spelled(prepared, graph, root, cache, Set.empty)) match
        case Success((spelling, next)) => (next, spelled :+ (root -> Success(spelling)))
        case Failure(error)            => (cache, spelled :+ (root -> Failure(error)))
    }

  /** Every class of the second graph spelled in turn from the cache a pass
    * over the first graph left, carried to the second by
    * `LocalExtraction.carriedCache` (`SpellingRetention.KeptAcrossPasses`),
    * the second graph being the first with more steps taken on it.
    */
  private def carriedSpellings(
      prepared: LocalExtraction.Prepared[NoFacts.type, Int],
      first: EGraph[NoFacts.type],
      second: EGraph[NoFacts.type]
  ): Vector[(Int, Try[Configured[NoFacts.type]])] =
    val (firstCache, _) = spellingsFrom(prepared, first, roots(first), SpellingCache.empty[NoFacts.type, Int])
    val carried = CarriedSpellings(firstCache, prepared, first.nodeCount, first.unionCount)
    spellingsFrom(prepared, second, roots(second), LocalExtraction.carriedCache(carried, second, prepared, Set.empty))._2

  /** The classes that have a finite derivation by live nodes, a named class
    * by its name: the least set closed under a member whose children are all
    * in it.
    */
  private def derivable(graph: EGraph[NoFacts.type], namedClasses: Set[Int]): Set[Int] =
    @scala.annotation.tailrec
    def grown(found: Set[Int]): Set[Int] =
      val next = found ++ roots(graph).filter(root =>
        graph.classMembers(root).exists(_.layer.children.forall(child => found.contains(graph.root(child))))
      )
      if next == found then found else grown(next)
    grown(namedClasses)

  /** A spelling that fails is the `IllegalStateException` of a class with no
    * entry.
    */
  private def failedForNoEntry(root: Int, outcome: Try[Configured[NoFacts.type]]): Result = outcome match
    case Failure(error: IllegalStateException) =>
      Result.assert(error.getMessage == s"the class $root has no entry").log(s"the class $root failed with $error")
    case other => Result.failure.log(s"the class $root, with no finite derivation, gave $other")

  /** A graph with a β cycle at its end, names among its instructions and a
    * model that may leave a kind's last child unpriced, with the classes
    * that hold the names.
    */
  private final case class CyclicCase(graph: EGraph[NoFacts.type], namedClasses: Map[Int, Configured[NoFacts.type]], model: Weighted)

  private def cyclicCase(closed: Boolean): PropertyT[CyclicCase] =
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- anyStep.list(Range.linear(0, 25)).forAll
      cycleBody <- index.forAll
      cycleArgument <- index.forAll
      nameNumbers <- index.list(Range.linear(0, 3)).forAll
      kindWeights <- weights.forAll
      unpricedLast <- bits.forAll
    yield
      val Generated(graph, instructions) =
        generated(leafCount, steps :+ Step.BetaCycle(cycleBody, cycleArgument), acyclic = false, closed = closed)
      val names = nameNumbers.map(number => instructions(number % instructions.size)).toSet
      val namedClasses = names.flatMap(name => graph.instructionNode(name).map(node => graph.root(node) -> name)).toMap
      CyclicCase(graph, namedClasses, Weighted(kindWeights, unpricedLast))

  property(
    "on graphs closed under congruence, every class is spelled by a term of its class with no class inside its own spelling",
    _.copy(testLimit = SuccessCount(100))
  ) {
    cyclicCase(closed = true).map { case CyclicCase(graph, namedClasses, model) =>
      val nameSet = namedClasses.values.toSet
      Result.all(spellings(LocalExtraction.Prepared(model, namedClasses), graph, roots(graph)).toList.map {
        case (root, Success(spelling)) =>
          val (withSpelling, node) = graph.instructionAdded(spelling)
          val ownClassBelow = classesBelow(withSpelling, nameSet, spelling, Map.empty).toList.collect {
            case (term, classes) if classes.contains(classOf(withSpelling, term)) => term
          }
          Result
            .diff(withSpelling.root(node), withSpelling.root(root))(_ == _)
            .log(s"the class $root spelled $spelling")
            .and(Result.diff(ownClassBelow, Nil)(_ == _).log(s"terms with a subterm of their own class in $spelling"))
        case (root, Failure(error)) => Result.failure.log(s"the class $root failed with $error")
      })
    }
  }

  property(
    "on graphs not closed under congruence, a class is spelled if and only if it has a finite derivation, and fails otherwise",
    _.copy(testLimit = SuccessCount(100))
  ) {
    cyclicCase(closed = false).map { case CyclicCase(graph, namedClasses, model) =>
      val finite = derivable(graph, namedClasses.keySet)
      Result.all(spellings(LocalExtraction.Prepared(model, namedClasses), graph, roots(graph)).toList.map {
        case (root, Success(spelling)) =>
          Result.assert(finite.contains(root)).log(s"the class $root has no finite derivation and was spelled $spelling")
        case (root, outcome) =>
          Result.assert(!finite.contains(root)).log(s"the class $root has a finite derivation").and(failedForNoEntry(root, outcome))
      })
    }
  }

  private def classOf(graph: EGraph[NoFacts.type], term: Configured[NoFacts.type]): Int =
    graph.root(graph.instructionNode(term).getOrElse(throw IllegalStateException(s"$term was not filed")))

  /** For each distinct subterm of the term, the classes of its proper
    * subterms, a name taken as a leaf; added to `known`, each subterm once.
    */
  private def classesBelow(
      graph: EGraph[NoFacts.type],
      names: Set[Configured[NoFacts.type]],
      term: Configured[NoFacts.type],
      known: Map[Configured[NoFacts.type], Set[Int]]
  ): Map[Configured[NoFacts.type], Set[Int]] =
    if known.contains(term) then known
    else
      val children = if names.contains(term) then Vector.empty else graph.store.expanded(term).children
      val withChildren = children.foldLeft(known)((current, child) => classesBelow(graph, names, child, current))
      withChildren.updated(term, children.flatMap(child => withChildren(child) + classOf(graph, child)).toSet)

  property("on acyclic graphs under a superior model, every spelling costs its class's least finite derivation") {
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- acyclicStep.list(Range.linear(0, 25)).forAll
      kindWeights <- weights.forAll
      closed <- Gen.boolean.forAll
    yield
      val Generated(graph, _) = generated(leafCount, steps, acyclic = true, closed = closed)
      val model = Weighted(kindWeights, Vector.fill(kindCount)(0))
      val classes = roots(graph)
      val least = classes.foldLeft(Map.empty[Int, Option[Int]])((known, root) => leastCosts(graph, kindWeights, root, known))
      def spellingCost(term: Configured[NoFacts.type]): Int =
        val layer = graph.store.expanded(term)
        kindWeights(kind(layer)) + layer.children.map(spellingCost).sum
      Result.all(spellings(LocalExtraction.Prepared(model, Map.empty), graph, classes).toList.map((root, outcome) =>
        (least(root), outcome) match
          case (Some(cost), Success(spelling)) =>
            Result.diff(spellingCost(spelling), cost)(_ == _).log(s"the class $root spelled $spelling")
          case (Some(cost), Failure(error)) => Result.failure.log(s"the class $root, of least cost $cost, failed with $error")
          case (None, _)                    => failedForNoEntry(root, outcome)
      ))
  }

  property(
    "on acyclic graphs under a superior model, every spelling from a cache carried across passes costs its class's least finite derivation"
  ) {
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      firstSteps <- acyclicStep.list(Range.linear(0, 20)).forAll
      secondSteps <- acyclicStep.list(Range.linear(0, 10)).forAll
      kindWeights <- weights.forAll
      closed <- Gen.boolean.forAll
    yield
      val first = generated(leafCount, firstSteps, acyclic = true, closed = closed)
      val Generated(graph, _) = continued(first, secondSteps, acyclic = true, closed = closed)
      val model = Weighted(kindWeights, Vector.fill(kindCount)(0))
      val least = roots(graph).foldLeft(Map.empty[Int, Option[Int]])((known, root) => leastCosts(graph, kindWeights, root, known))
      def spellingCost(term: Configured[NoFacts.type]): Int =
        val layer = graph.store.expanded(term)
        kindWeights(kind(layer)) + layer.children.map(spellingCost).sum
      Result.all(carriedSpellings(LocalExtraction.Prepared(model, Map.empty), first.graph, graph).toList.map((root, outcome) =>
        (least(root), outcome) match
          case (Some(cost), Success(spelling)) =>
            Result.diff(spellingCost(spelling), cost)(_ == _).log(s"the class $root spelled $spelling")
          case (Some(cost), Failure(error)) => Result.failure.log(s"the class $root, of least cost $cost, failed with $error")
          case (None, _)                    => failedForNoEntry(root, outcome)
      ))
  }

  property(
    "on graphs closed under congruence, every spelling from a cache carried across passes is a term of its class",
    _.copy(testLimit = SuccessCount(100))
  ) {
    for
      cyclic <- cyclicCase(closed = true)
      secondSteps <- anyStep.list(Range.linear(0, 10)).forAll
    yield
      val CyclicCase(firstGraph, namedClasses, model) = cyclic
      val second = continued(Generated(firstGraph, filedInstructions(firstGraph)), secondSteps, acyclic = false, closed = true).graph
      val namedNow = namedClasses.values.flatMap(name => second.instructionNode(name).map(node => second.root(node) -> name)).toMap
      val prepared = LocalExtraction.Prepared(model, namedClasses)
      val (firstCache, _) = spellingsFrom(prepared, firstGraph, roots(firstGraph), SpellingCache.empty[NoFacts.type, Int])
      val carried = CarriedSpellings(firstCache, prepared, firstGraph.nodeCount, firstGraph.unionCount)
      val secondPrepared = LocalExtraction.Prepared(model, namedNow)
      val (_, spelled) = spellingsFrom(secondPrepared, second, roots(second), LocalExtraction.carriedCache(carried, second, secondPrepared, Set.empty))
      Result.all(spelled.toList.map {
        case (root, Success(spelling)) =>
          val (withSpelling, node) = second.instructionAdded(spelling)
          Result.diff(withSpelling.root(node), withSpelling.root(root))(_ == _).log(s"the class $root spelled $spelling")
        case (root, Failure(error)) => Result.failure.log(s"the class $root failed with $error")
      })
  }

  /** The instructions the graph filed, in the order of their nodes: the
    * instructions a step taken on the graph picks among.
    */
  private def filedInstructions(graph: EGraph[NoFacts.type]): Vector[Configured[NoFacts.type]] =
    (0 until graph.nodeCount).flatMap(graph.nodeInstruction).toVector

  /** The least cost of the finite derivations of the class and of the
    * classes it reads, none for a class with none, added to `known`, by
    * recursion over the acyclic graph: the least, over the class's live
    * nodes whose children all have one, of the node's weight and its
    * children's least costs.
    */
  private def leastCosts(
      graph: EGraph[NoFacts.type],
      kindWeights: Vector[Int],
      root: Int,
      known: Map[Int, Option[Int]]
  ): Map[Int, Option[Int]] =
    if known.contains(root) then known
    else
      val members = graph.classMembers(root).filterNot(member => Extraction.absorbedChoice(graph, root, member.layer))
      val withChildren = members
        .flatMap(_.layer.children.map(graph.root))
        .foldLeft(known)((current, child) => leastCosts(graph, kindWeights, child, current))
      val costs = members.flatMap(member =>
        member.layer.children
          .foldLeft(Option(0))((sum, child) => sum.zip(withChildren(graph.root(child))).map(_ + _))
          .map(kindWeights(kind(member.layer)) + _)
      )
      withChildren.updated(root, costs.minOption)
