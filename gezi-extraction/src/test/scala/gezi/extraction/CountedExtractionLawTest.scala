package gezi.extraction

import gezi.saturation.StopSignal
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.{Apply, Choice, Parallel}

/** The fixed point laws of `CountedExtraction.fixed` on generated graphs. Each
  * graph starts from a few noinline leaves and takes a generated sequence of
  * steps: an instruction added (an application, a parallel or a choice of
  * instructions added before), or two nodes united, which makes classes that
  * read themselves. Some of the instructions are names. A cost has a value and
  * a reading, 0 or 1 (`CostModel`, THE CONTRACT): the value of a production is
  * a generated weight of its kind (an application, a parallel, a choice, a
  * leaf, a name, a specialization choice or a judgment, each 0 to 2) plus its
  * children's values, each child of reading 1 adding a generated penalty (0 to
  * 2), so that costs tie, a class can read itself at no cost, and a child's
  * best entry is not always the one its parent does best over; a generated bit
  * of each kind leaves its last child unpriced, as the modules leave a
  * parallel's criterion, so that a child can improve at no change of its
  * parent's cost; the reading of a production is a generated bit of its kind
  * plus its children's readings, modulo 2. Costs are ordered by their values
  * alone.
  *
  * A production's children are read as the extraction reads them: the class
  * itself by its entries of productions that do not read it, any other class by
  * its entries, one of each reading. (1) No production read over any
  * combination of the entries of the fixed point is cheaper than its class's
  * entry of the same reading, nor, when it does not read its class, than its
  * class's entry of the same reading among the productions that do not read it.
  * (2) A class has an entry if and only if one of its productions has every
  * child's entry, and an entry of a production that does not read it if and
  * only if one such production has every child's entry. (3) No entry is stale:
  * every entry kept, read again over its children's final entries of the
  * readings it was made over, has the same reading and an equal cost; so a
  * spelling, which spells each child by its class's final entry of that reading
  * (`Extraction.spelled`), costs what its entry says. Their purpose is to catch
  * an extraction that stops before its fixed point (a production not read again
  * after a child improved, a count of children missing that never reaches
  * zero), that keeps one entry where a parent needs another reading, or that
  * gives a class an entry no production supports.
  */
class CountedExtractionLawTest extends GeneratedProperties:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of CountedExtractionLawTest, "every kept entry is the least finite tree of its class and reading", takes 3.233 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(5, "s")

  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  /** A step of a generated graph; the numbers pick among the instructions or
    * the nodes made so far, modulo their count.
    */
  private enum Step:
    case Applied(function: Int, argument: Int)
    case Paralleled(left: Int, right: Int)
    case Chosen(members: List[Int])
    case United(first: Int, second: Int)

  private val index = Gen.int(Range.linear(0, 1000))

  private val step: Gen[Step] = Gen.choice1(
    for function <- index; argument <- index
    yield Step.Applied(function, argument),
    for left <- index; right <- index yield Step.Paralleled(left, right),
    index.list(Range.linear(1, 3)).map(Step.Chosen(_)),
    for first <- index; second <- index yield Step.United(first, second)
  )

  /** The weights of the kinds of productions, by the order of `weight`. */
  private val weights: Gen[Vector[Int]] =
    Gen.int(Range.linear(0, 2)).list(Range.singleton(kindCount)).map(_.toVector)

  /** The number of kinds of productions `Weighted.kind` tells apart. */
  private def kindCount: Int = 7

  private final case class Generated(
      graph: EGraph[C],
      instructions: Vector[Configured[C]]
  )

  private def generated(leafCount: Int, steps: List[Step]): Generated =
    val leaves =
      Vector.tabulate(leafCount)(number => NoFacts.opaque(s"leaf$number"))
    val empty = EGraph.empty(
      Store(noinline = leaves.toSet, gezi.ir.TermConstruction(NoFacts)),
      Map.empty,
      explained = false
    )
    val start = Generated(
      leaves.foldLeft(empty)((graph, leaf) => graph.instructionAdded(leaf)._1),
      leaves
    )
    steps.foldLeft(start)((current, step) =>
      def instruction(number: Int): Configured[C] =
        current.instructions(number % current.instructions.size)
      def added(instruction: Configured[C]): Generated =
        Generated(
          current.graph.instructionAdded(instruction)._1,
          current.instructions :+ instruction
        )
      step match
        case Step.Applied(function, argument) =>
          added(
            NoFacts.application(instruction(function), instruction(argument))
          )
        case Step.Paralleled(left, right) =>
          added(NoFacts.parallel(instruction(left), instruction(right)))
        case Step.Chosen(members) =>
          added(
            gezi.ir.ChoiceSpine.nested[Configured[C]](
              members.toVector.map(instruction),
              (left, right) => NoFacts.choice(left, right)
            )
          )
        case Step.United(first, second) =>
          val nodes = current.graph.nodeCount
          current.copy(graph =
            current.graph
              .unionWorked(first % nodes, second % nodes, lemma, None)
          )
    )

  /** A cost: its value, which orders it, and its reading, 0 or 1. */
  private final case class ReadCost(value: Int, reading: Int)

  /** `unpricedLast(kind)` is 1 when a production of that kind does not count
    * its last child's value, as the modules leave a parallel's criterion
    * unpriced: a child improving there does not change the parent's cost.
    * `saturation` counts a priced child's value up to that bound at most, so
    * that the cost is not strictly monotone at priced positions.
    */
  private final class Weighted(
      weights: Vector[Int],
      readingBits: Vector[Int],
      penalty: Int,
      unpricedLast: Vector[Int],
      saturation: Option[Int],
      runsFirstOfReadingOne: Vector[Int]
  ) extends StatelessCostModel[C, ReadCost]:
    def cost(shape: Shape[C], childCosts: Vector[ReadCost]): ReadCost =
      val priced =
        childCosts.zip(CostModel.pricedUnder(this, shape, childCosts)).collect {
          case (child, true) => child
        }
      ReadCost(
        weights(kind(shape)) + priced
          .map(child =>
            saturation.fold(child.value)(
              child.value.min
            ) + penalty * child.reading
          )
          .sum,
        (readingBits(kind(shape)) + childCosts.map(_.reading).sum) % 2
      )
    val ordering: Ordering[ReadCost] = Ordering.by(_.value)
    override def sameReading(left: ReadCost, right: ReadCost): Boolean =
      left.reading == right.reading
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      val count = shape.children.size
      Vector.tabulate(count)(position =>
        !(unpricedLast(kind(shape)) == 1 && position == count - 1)
      )

    /** Under `runsFirstOfReadingOne(kind) == 1`, a production of that kind runs
      * only its first child of reading 1, as a narrow choice runs its first
      * narrow member, and drops the others; with none of reading 1 it runs them
      * all. A function of the children's readings only.
      */
    override def droppedChildren(
        shape: Shape[C],
        childCosts: Vector[ReadCost]
    ): Vector[Boolean] =
      if runsFirstOfReadingOne(kind(shape)) == 1 then
        childCosts.indexWhere(_.reading == 1) match
          case -1  => childCosts.map(_ => false)
          case run => childCosts.indices.toVector.map(_ != run)
      else childCosts.map(_ => false)

    override def mayDropChildren(shape: Shape[C]): Vector[Boolean] =
      shape.children.map(_ => runsFirstOfReadingOne(kind(shape)) == 1)

    private def kind(shape: Shape[C]): Int = shape match
      case Shape.Node(_, Apply(_, _))    => 0
      case Shape.Node(_, Parallel(_, _)) => 1
      case Shape.Node(_, Choice(_, _))   => 2
      case Shape.Node(_, _)              => 3
      case Shape.Name(_)                 => 4
      case Shape.Specialized(_, _)       => 5
      case Shape.Judged(_, _)            => 6

  /** The weighted model whose memo keeps the candidates of every call by its
    * arguments and the kind of call, and answers a call with equal arguments
    * from the memo (`CostModel.Memo`).
    */
  private final class CallsRemembered(base: Weighted)
      extends CostModel[C, ReadCost]:
    type Memo =
      Map[(Shape[C], Vector[Vector[Entry[C, ReadCost]]], Boolean), Vector[
        Entry[C, ReadCost]
      ]]
    def emptyMemo: Memo = Map.empty
    def cost(shape: Shape[C], childCosts: Vector[ReadCost]): ReadCost =
      base.cost(shape, childCosts)
    def ordering: Ordering[ReadCost] = base.ordering
    override def sameReading(left: ReadCost, right: ReadCost): Boolean =
      base.sameReading(left, right)
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      base.pricedChildren(shape)
    override def droppedChildren(
        shape: Shape[C],
        childCosts: Vector[ReadCost]
    ): Vector[Boolean] = base.droppedChildren(shape, childCosts)
    override def mayDropChildren(shape: Shape[C]): Vector[Boolean] =
      base.mayDropChildren(shape)
    def memoizedCandidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, ReadCost]]],
        memo: Memo
    ): (Vector[Entry[C, ReadCost]], Memo) =
      memo.get((shape, options, false)) match
        case Some(found) => (found, memo)
        case None        =>
          val found = base.candidates(shape, options)
          (found, memo.updated((shape, options, false), found))
    def memoizedLeastCandidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, ReadCost]]],
        memo: Memo
    ): (Vector[Entry[C, ReadCost]], Memo) =
      memo.get((shape, options, true)) match
        case Some(found) => (found, memo)
        case None        =>
          val found = base.leastCandidates(shape, options)
          (found, memo.updated((shape, options, true), found))

  /** Every combination of one option from each list, in order. */
  private def combinations[Value](
      options: Vector[Vector[Value]]
  ): Vector[Vector[Value]] =
    options.foldLeft(Vector(Vector.empty[Value]))((partial, choices) =>
      for
        chosen <- partial
        choice <- choices
      yield chosen :+ choice
    )

  /** A model's memo changes cost only: the extraction under a model that
    * answers calls with equal arguments from its memo keeps the entries the
    * stateless model's extraction keeps. Its purpose is to catch an extraction
    * whose result depends on a remembered answer standing in for a computed
    * one: a remembered candidate's child entries are the objects of the earlier
    * call's options, equal to the current call's but not always the same
    * objects, and the pass at cost finds a child entry in its list by reference
    * (`consistent`), so a check that needs the current call's own objects would
    * drop remembered candidates. A memo dropped or handed back stale between
    * calls is not caught: under a model that remembers a pure function the
    * extraction is the same either way, and its result shows no memo.
    */
  stoppableProperty(
    "an extraction under a remembering model keeps the entries the stateless model's keeps"
  ) { stopped =>
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- step.list(Range.linear(0, 30)).forAll
      nameNumbers <- index.list(Range.linear(0, 4)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      runsFirst <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
    yield
      val Generated(graph, instructions) = generated(leafCount, steps)
      val names = nameNumbers
        .map(number => instructions(number % instructions.size))
        .toSet
      val model = Weighted(
        kindWeights,
        readingBits,
        penalty,
        unpricedLast,
        None,
        runsFirst
      )
      val stateless = CountedExtraction
        .fixed(graph, names, model, StopSignal.completedWith(stopped))
        .getOrElse(fail("the extraction was stopped"))
      val remembering = CountedExtraction
        .fixed(
          graph,
          names,
          CallsRemembered(model),
          StopSignal.completedWith(stopped)
        )
        .getOrElse(fail("the extraction was stopped"))
      Result.diff(remembering.classes, stateless.classes)(_ == _)
  }

  stoppableProperty(
    "the extraction is at its fixed point, every entry is supported by a production, and no entry is stale"
  ) { stopped =>
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- step.list(Range.linear(0, 30)).forAll
      nameNumbers <- index.list(Range.linear(0, 4)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      runsFirst <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
    yield
      val Generated(graph, instructions) = generated(leafCount, steps)
      val names = nameNumbers
        .map(number => instructions(number % instructions.size))
        .toSet
      val model = Weighted(
        kindWeights,
        readingBits,
        penalty,
        unpricedLast,
        None,
        runsFirst
      )
      val extracted = CountedExtraction
        .fixed(graph, names, model, StopSignal.completedWith(stopped))
        .getOrElse(fail("the extraction was stopped"))
      val (productions, _) = Extraction.productions(graph, names)
      def entries(root: Int): ClassEntries[ReadCost] =
        extracted.classes.getOrElse(root, ClassEntries.unentered(Vector.empty))
      def childOptions(
          root: Int,
          shape: Shape[C]
      ): Vector[Vector[Entry[C, ReadCost]]] =
        shape.children.map(child =>
          if child == root then entries(child).looplessEntries
          else entries(child).entries
        )
      def ofReading(
          kept: Vector[Entry[C, ReadCost]],
          cost: ReadCost
      ): Option[Entry[C, ReadCost]] =
        kept.find(entry => model.sameReading(entry.cost, cost))
      val readable = productions.flatMap(production =>
        combinations(childOptions(production.root, production.shape)).map(
          children =>
            (production, model.cost(production.shape, children.map(_.cost)))
        )
      )
      val noCheaper = readable.toList.map((production, cost) =>
        val classEntries = entries(production.root)
        val loopless = !production.shape.children.contains(production.root)
        Result
          .assert(
            ofReading(classEntries.entries, cost)
              .exists(_.cost.value <= cost.value)
          )
          .and(
            Result.assert(
              !loopless || ofReading(classEntries.looplessEntries, cost)
                .exists(_.cost.value <= cost.value)
            )
          )
          .log(
            s"production $production costs $cost; entries ${classEntries.entries.map(_.cost)}, loopless ${classEntries.looplessEntries.map(_.cost)}"
          )
      )
      val supported = productions
        .map(_.root)
        .distinct
        .toList
        .map(root =>
          val ofClass = readable.filter(_._1.root == root)
          Result
            .diff(entries(root).best.isDefined, ofClass.nonEmpty)(_ == _)
            .and(
              Result.diff(
                entries(root).bestLoopless.isDefined,
                ofClass.exists(!_._1.shape.children.contains(root))
              )(_ == _)
            )
            .log(s"class $root")
        )
      val fresh = extracted.classes.toList.flatMap((root, classEntries) =>
        (classEntries.entries ++ classEntries.looplessEntries).map(entry =>
          val finalChildren = entry.shape.children
            .zip(entry.childEntries)
            .map((child, childEntry) =>
              extracted
                .entryOfReading(child, childEntry, loopless = child == root)
            )
          val again = model.cost(entry.shape, finalChildren.map(_.cost))
          Result
            .diff(again, entry.cost)(_ == _)
            .log(s"class $root, entry over ${entry.childEntries.map(_.cost)}")
        )
      )
      Result.all(noCheaper ++ supported ++ fresh)
  }

  /** The weighted model settling a production's children of more than one entry
    * to their first by size and content when the product of their numbers of
    * entries exceeds `bound` (`CostModel.settledChildren`), as a thunk's
    * jointly read fillings are settled; a production some of whose children may
    * be dropped settles none, as the contract asks.
    */
  private final class Settling(base: Weighted, bound: Int)
      extends StatelessCostModel[C, ReadCost]:
    def cost(shape: Shape[C], childCosts: Vector[ReadCost]): ReadCost =
      base.cost(shape, childCosts)
    val ordering: Ordering[ReadCost] = base.ordering
    override def sameReading(left: ReadCost, right: ReadCost): Boolean =
      base.sameReading(left, right)
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      base.pricedChildren(shape)
    override def droppedChildren(
        shape: Shape[C],
        childCosts: Vector[ReadCost]
    ): Vector[Boolean] = base.droppedChildren(shape, childCosts)
    override def mayDropChildren(shape: Shape[C]): Vector[Boolean] =
      base.mayDropChildren(shape)
    override def settledChildren(
        shape: Shape[C],
        entryCounts: Vector[Int]
    ): Vector[Boolean] =
      if !base.mayDropChildren(shape).contains(true) && entryCounts
          .filter(_ > 1)
          .map(BigInt(_))
          .product > bound
      then entryCounts.map(_ > 1)
      else entryCounts.map(_ => false)
    override def candidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, ReadCost]]]
    ): Vector[Entry[C, ReadCost]] =
      val offered = options
        .zip(settledChildren(shape, options.map(_.size)))
        .map((entries, settled) =>
          if settled then
            Vector(
              entries.reduce((kept, next) =>
                if firstBySize(next, kept) then next else kept
              )
            )
          else entries
        )
      CostModel
        .combinations(offered)
        .map(chosen => Entry(cost(shape, chosen.map(_.cost)), shape, chosen))
    override def leastCandidates(
        shape: Shape[C],
        options: Vector[Vector[Entry[C, ReadCost]]]
    ): Vector[Entry[C, ReadCost]] =
      CostModel.leastOfEachReading(this, candidates(shape, options))

  private def firstBySize(
      candidate: Entry[C, ReadCost],
      kept: Entry[C, ReadCost]
  ): Boolean =
    val bySize = candidate.size.compare(kept.size)
    bySize < 0 || (bySize == 0 && ContentOrder.compare(candidate, kept) < 0)

  /** An extraction under a model that settles children above a bound runs its
    * passes to the end, and a class has an entry, and one among the productions
    * that do not read it, exactly when it is reachable: the least set of
    * classes holding each class one of whose productions does not read it and
    * reads only classes of the set, computed from the productions alone.
    * Settling picks among entries and never leaves a production without one, so
    * it changes no class's reachability. Its purpose is to catch passes that
    * settle differently on generated graphs whose readings follow their
    * children's: `CountedExtraction` throws when a later pass finds an entry
    * below its target or misses one, when its second run settles a production
    * with no directive, or keeps a reading the first run's did not or loses one
    * it kept. With the second run skipped, the law fails.
    */
  stoppableProperty(
    "an extraction under a settling model runs every pass and gives each class with a production of every child's entry an entry"
  ) { stopped =>
    for
      leafCount <- Gen.int(Range.linear(1, 3)).forAll
      steps <- step.list(Range.linear(0, 30)).forAll
      nameNumbers <- index.list(Range.linear(0, 4)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      runsFirst <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      bound <- Gen.int(Range.linear(1, 4)).forAll
    yield
      val Generated(graph, instructions) = generated(leafCount, steps)
      val names = nameNumbers
        .map(number => instructions(number % instructions.size))
        .toSet
      val model = Settling(
        Weighted(
          kindWeights,
          readingBits,
          penalty,
          unpricedLast,
          None,
          runsFirst
        ),
        bound
      )
      val extracted = CountedExtraction
        .fixed(graph, names, model, StopSignal.completedWith(stopped))
        .getOrElse(fail("the extraction was stopped"))
      val (productions, _) = Extraction.productions(graph, names)
      def entries(root: Int): ClassEntries[ReadCost] =
        extracted.classes.getOrElse(root, ClassEntries.unentered(Vector.empty))
      @scala.annotation.tailrec
      def reachable(found: Set[Int]): Set[Int] =
        val next = found ++ productions.collect {
          case production
              if !production.shape.children.contains(
                production.root
              ) && production.shape.children.forall(found.contains) =>
            production.root
        }
        if next == found then found else reachable(next)
      val reached = reachable(Set.empty)
      Result.all(
        productions
          .map(_.root)
          .distinct
          .toList
          .map(root =>
            Result
              .diff(entries(root).best.isDefined, reached.contains(root))(
                _ == _
              )
              .and(
                Result.diff(
                  entries(root).bestLoopless.isDefined,
                  reached.contains(root)
                )(_ == _)
              )
              .log(s"class $root")
          )
      )
  }

  /** Every finite tree of each class of at most `bound` in size, the trees of a
    * production that reads its own class over that class's trees of productions
    * that do not read it; none when more than `limit` trees are found. A model
    * much simpler than the extraction: the trees are listed, not searched.
    */
  private def treesUpTo(
      model: Weighted,
      productions: Vector[Production],
      bound: Int,
      limit: Int
  ): Option[Map[Int, Set[Entry[C, ReadCost]]]] =
    def loopless(root: Int, tree: Entry[C, ReadCost]): Boolean =
      !tree.shape.children.contains(root)
    def grown(
        trees: Map[Int, Set[Entry[C, ReadCost]]]
    ): Map[Int, Set[Entry[C, ReadCost]]] =
      productions.foldLeft(trees) { (current, production) =>
        val root = production.root
        val childTrees = production.shape.children.map(child =>
          val ofChild = trees.getOrElse(child, Set.empty)
          (if child == root then ofChild.filter(loopless(root, _))
           else ofChild).toVector
        )
        val made = within(childTrees.toList, bound - 1).map(children =>
          Entry(
            model.cost(production.shape, children.map(_.cost)),
            production.shape,
            children
          )
        )
        current.updated(
          root,
          current.getOrElse(root, Set.empty) ++ made.filter(_.size <= bound)
        )
      }
    @scala.annotation.tailrec
    def fixed(
        trees: Map[Int, Set[Entry[C, ReadCost]]]
    ): Option[Map[Int, Set[Entry[C, ReadCost]]]] =
      val next = grown(trees)
      if next.values.map(_.size).sum > limit then None
      else if next == trees then Some(next)
      else fixed(next)
    fixed(Map.empty)

  /** Every choice of one tree for each position whose sizes sum to at most
    * `budget`.
    */
  private def within(
      options: List[Vector[Entry[C, ReadCost]]],
      budget: Int
  ): Vector[Vector[Entry[C, ReadCost]]] =
    options match
      case Nil           => Vector(Vector.empty)
      case first :: rest =>
        first
          .filter(_.size <= budget)
          .flatMap(tree =>
            within(rest, budget - tree.size.toInt).map(tree +: _)
          )

  /** The least of the trees of each reading, by cost and then `ContentOrder`.
    */
  private def leastOfReadings(
      model: Weighted,
      trees: Iterable[Entry[C, ReadCost]]
  ): Map[Int, Entry[C, ReadCost]] =
    trees
      .groupBy(_.cost.reading)
      .view
      .mapValues(
        _.reduce((kept, next) =>
          if better(model, next, kept) then next else kept
        )
      )
      .toMap

  private def better(
      model: Weighted,
      candidate: Entry[C, ReadCost],
      entry: Entry[C, ReadCost]
  ): Boolean =
    val order = model.ordering.compare(candidate.cost, entry.cost)
    order < 0 || (order == 0 && ContentOrder.compare(candidate, entry) < 0)

  /** The extraction's kept entries against the least finite trees listed up to
    * `bound` in size: a kept entry smaller than the bound is the least tree of
    * its class and reading, every reading a listed tree has is kept, and no
    * listed tree is better than the kept entry of its reading; and likewise
    * among the trees of productions that do not read their class.
    */
  private def againstTrees(
      model: Weighted,
      extracted: Extracted[C, ReadCost],
      trees: Map[Int, Set[Entry[C, ReadCost]]],
      bound: Int
  ): List[Result] =
    def compared(
        root: Int,
        kept: Vector[Entry[C, ReadCost]],
        listed: Iterable[Entry[C, ReadCost]],
        kind: String
    ): List[Result] =
      leastOfReadings(model, listed).toList.map((reading, least) =>
        kept.find(_.cost.reading == reading) match
          case None =>
            Result.failure.log(
              s"class $root ($kind) has no entry of reading $reading; the least tree listed is $least"
            )
          case Some(entry) =>
            val agrees = if entry.size < bound then entry == least
            else !better(model, least, entry)
            Result
              .assert(agrees)
              .log(
                s"class $root ($kind), reading $reading: kept $entry, least listed $least"
              )
      )
    trees.toList.flatMap((root, ofClass) =>
      val classEntries =
        extracted.classes.getOrElse(root, ClassEntries.unentered(Vector.empty))
      compared(root, classEntries.entries, ofClass, "entries") ++
        compared(
          root,
          classEntries.looplessEntries,
          ofClass.filterNot(_.shape.children.contains(root)),
          "loopless"
        )
    )

  private val treeBound = 9

  private val treeLimit = 4000

  /** (4) THE DEFINITION of `CountedExtraction`: every class's kept entry of
    * each reading is the least finite tree of that class and reading, by cost
    * and then `ContentOrder`, checked against every tree listed up to a size
    * bound (`treesUpTo`; a graph with more trees than the limit is skipped).
    * Its purpose is to catch a kept entry that depends on the order in which
    * the extraction found it, such as a parent kept over a child's earlier
    * entry after the child improved at no change of the parent's cost, and a
    * class left without its least tree, such as one whose least cost is reached
    * only through a cycle at no cost. On the retired loop, whose kept entry was
    * the best ever produced, graphs of up to 80 steps falsified the earlier
    * statement of this law after 199 and 399 inputs (2026-11-13; a choice whose
    * unpriced member kept an application over a stale entry of its child), and
    * the extraction of the children's kept entries alone stopped on a cycle of
    * parallels at no cost after 699.
    */
  stoppableProperty(
    "every kept entry is the least finite tree of its class and reading",
    _.copy(testLimit = hedgehog.core.SuccessCount(1000))
  ) { stopped =>
    for
      leafCount <- Gen.int(Range.linear(1, 2)).forAll
      steps <- step.list(Range.linear(0, 16)).forAll
      nameNumbers <- index.list(Range.linear(0, 2)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      runsFirst <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
    yield
      val Generated(graph, instructions) = generated(leafCount, steps)
      val names = nameNumbers
        .map(number => instructions(number % instructions.size))
        .toSet
      val model = Weighted(
        kindWeights,
        readingBits,
        penalty,
        unpricedLast,
        None,
        runsFirst
      )
      val (productions, _) = Extraction.productions(graph, names)
      treesUpTo(model, productions, treeBound, treeLimit) match
        case None        => Result.success
        case Some(trees) =>
          Result.all(
            againstTrees(
              model,
              CountedExtraction
                .fixed(graph, names, model, StopSignal.completedWith(stopped))
                .getOrElse(fail("the extraction was stopped")),
              trees,
              treeBound
            )
          )
  }

  /** A level of a deep graph over the level below it and a leaf: an application
    * of the level below to itself, a parallel of it with itself, or a choice of
    * two applications of it and the leaf, so that every level's entry reads the
    * level below's twice.
    */
  private enum Level:
    case SelfApplied, SelfParalleled, ChosenBetweenApplications

  private val level: Gen[Level] = Gen.element1(
    Level.SelfApplied,
    Level.SelfParalleled,
    Level.ChosenBetweenApplications
  )

  /** Each level of the graph over the one below it and the leaf. */
  private def deepened(
      leaf: Configured[C],
      levels: List[Level]
  ): Configured[C] =
    levels.foldLeft(leaf)((below, next) =>
      next match
        case Level.SelfApplied    => NoFacts.application(below, below)
        case Level.SelfParalleled => NoFacts.parallel(below, below)
        case Level.ChosenBetweenApplications =>
          gezi.ir.ChoiceSpine.nested[Configured[C]](
            Vector(
              NoFacts.application(below, leaf),
              NoFacts.application(leaf, below)
            ),
            (left, right) => NoFacts.choice(left, right)
          )
    )

  /** The extraction of a graph 40 to 80 levels deep, each level reading the one
    * below twice, so that the entry of the top spells a term whose size is
    * exponential in the depth over entries shared at every level; choices whose
    * readings may drop a member read both passes' entries there. Its purpose is
    * to catch an extraction that compares, hashes or walks entries by structure
    * (a `.distinct` or a `Set` of entries, whose case class hash walks the
    * whole shared entry: main's jit NativeRouteCompilationTest hung in
    * `Entry.hashCode` for more than ten minutes, 2026-11-14). The defect shows
    * as a property that does not finish.
    */
  stoppableProperty(
    "an extraction over entries shared at every level of a deep graph finishes, the top entered"
  ) { stopped =>
    for
      levels <- level.list(Range.linear(40, 80)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
    yield
      val leaf = NoFacts.opaque("leaf")
      val top = deepened(leaf, levels)
      val (graph, topNode) = EGraph
        .empty(
          Store(noinline = Set(leaf), gezi.ir.TermConstruction(NoFacts)),
          Map.empty,
          explained = false
        )
        .instructionAdded(leaf)
        ._1
        .instructionAdded(top)
      // Every kind's readings may drop its children, a choice's included.
      val model = Weighted(
        kindWeights,
        readingBits,
        penalty,
        unpricedLast,
        None,
        Vector.fill(kindCount)(1)
      )
      val extracted = CountedExtraction
        .fixed(graph, Set.empty, model, StopSignal.completedWith(stopped))
        .getOrElse(fail("the extraction was stopped"))
      Result
        .assert(
          extracted.classes.get(graph.root(topNode)).exists(_.best.isDefined)
        )
        .log(s"levels $levels")
  }

  /** The model is strictly monotone at the position over the child costs:
    * raising that child's value by `raised` (positive) gives a strictly
    * costlier parent.
    */
  private def strictAt(
      model: Weighted,
      shape: Shape[C],
      childCosts: Vector[ReadCost],
      position: Int,
      raised: Int
  ): Boolean =
    val worse = childCosts.updated(
      position,
      childCosts(position).copy(value = childCosts(position).value + raised)
    )
    model.ordering.compare(
      model.cost(shape, childCosts),
      model.cost(shape, worse)
    ) < 0

  private val childCost: Gen[ReadCost] =
    for
      value <- Gen.int(Range.linear(0, 3));
      reading <- Gen.int(Range.linear(0, 1))
    yield ReadCost(value, reading)

  /** The contract's strictness at priced positions on the productions of a
    * generated graph, by a model that saturates a priced child's value at
    * `saturation` or not at all: for each production, each priced position and
    * generated child costs, whether raising the child's value raises the
    * parent's.
    */
  private def strictness(saturation: Option[Int]) =
    for
      leafCount <- Gen.int(Range.linear(1, 2)).forAll
      steps <- step.list(Range.linear(0, 16)).forAll
      kindWeights <- weights.forAll
      readingBits <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      penalty <- Gen.int(Range.linear(0, 2)).forAll
      unpricedLast <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      runsFirst <- Gen
        .int(Range.linear(0, 1))
        .list(Range.singleton(kindCount))
        .map(_.toVector)
        .forAll
      costs <- childCost.list(Range.singleton(4)).forAll
      raised <- Gen.int(Range.linear(1, 2)).forAll
    yield
      val Generated(graph, _) = generated(leafCount, steps)
      val model = Weighted(
        kindWeights,
        readingBits,
        penalty,
        unpricedLast,
        saturation,
        runsFirst
      )
      val (productions, _) = Extraction.productions(graph, Set.empty)
      productions.toList.flatMap(production =>
        val shape = production.shape
        val childCosts = shape.children.indices.toVector.map(position =>
          costs(position % costs.size)
        )
        CostModel.pricedUnder(model, shape, childCosts).zipWithIndex.collect {
          case (true, position) =>
            (
              shape,
              childCosts,
              position,
              strictAt(model, shape, childCosts, position, raised)
            )
        }
      )

  /** (5) The generated model meets the contract's strictness at priced
    * positions (`CostModel`, THE CONTRACT), which law (4)'s exactness rests on.
    * Its purpose is to catch a test model that law (4) would check under a
    * contract it breaks.
    */
  property("the generated model is strictly monotone at priced positions") {
    strictness(None).map(checked =>
      Result.all(
        checked.map((shape, childCosts, position, strict) =>
          Result
            .assert(strict)
            .log(s"$shape over $childCosts at priced position $position")
        )
      )
    )
  }

  /** (6) The negative control of (5): a model that counts a priced child's
    * value as 0 (saturating at 0) fails the strictness check at every priced
    * position. Under such a model the extraction's last pass keeps a non-least
    * tree without throwing (measured 2026-11-13: a class Parallel(X, X) of cost
    * 0 whatever its children, over a class X of a leaf of cost 1 and Apply(X,
    * X) of cost 0, kept the parallel over the applications, size 7, where the
    * least tree is the parallel over the leaves, size 3), so the contract, not
    * the extraction, is the guard. Its purpose is to catch a strictness check
    * that accepts what it must reject.
    */
  property(
    "a model that saturates priced children fails the strictness check"
  ) {
    strictness(Some(0)).map(checked =>
      Result.all(
        checked.map((shape, childCosts, position, strict) =>
          Result
            .assert(!strict)
            .log(s"$shape over $childCosts at priced position $position")
        )
      )
    )
  }
