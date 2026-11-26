package gezi.contest.corpora.reductions

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.ExchangeText
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import snapshot4s.generated.snapshotConfig

/** The answer of `problems/speculative_untabling/weighted_paths` by its
  * definition, computed in the tests at the small sizes of the bottom rungs
  * and of the point table, as `CsesDefinitions` computes the CSES problems':
  * the value of a node asked once along every path that reaches it, with no
  * value remembered, and its weight by K steps of x ↦ x² + 1 modulo
  * 10^9 + 7.
  */
object WeightedPathsDefinitions:

  private val modulus: BigInt = BigInt(WeightedPaths.modulus)

  /** The value of the root. */
  def value(site: WeightedPaths.Site): NativeValue =
    def weight(node: Int): BigInt = (1 to site.steps).foldLeft(BigInt(site.seeds(node)))((value, _) => (value * value + 1) % modulus)
    def of(node: Int): BigInt = weight(node) + site.successors(node).map(of).sum
    NativeValue.natural(of(0) % modulus)

class WeightedPathsDistinctReferenceTest
    extends CsesFamilySuite(
      WeightedPaths.distinctFamilies.head(0),
      WeightedPaths.distinctFamilies.head(1),
      WeightedPathsDefinitions.value,
      "speculative_untabling_weighted_paths_distinct"
    )

class WeightedPathsRecurringReferenceTest
    extends CsesFamilySuite(
      WeightedPaths.recurringFamilies.head(0),
      WeightedPaths.recurringFamilies.head(1),
      WeightedPathsDefinitions.value,
      "speculative_untabling_weighted_paths_recurring"
    )

/** The tests of the point table of `problems/speculative_untabling`
  * (`CsesPoints.weightedPaths`), the check its computed references name, as
  * `CsesPointsReferenceTest` tests the CSES tables. Their inputs are the rows
  * of the table, the data under test, not generated.
  *
  *   - The rows' snapshot, whose purpose is to show in review what each row
  *     reads as, and to catch a row that no longer reads (a field of another
  *     encoding, a shared node read as two): every row, its name, its site
  *     and its Result.
  *   - The definition law, whose purpose is to catch a Result that is not
  *     the problem's answer by its statement: each row's Result is the
  *     definition's computed in the test (`WeightedPathsDefinitions`).
  *   - The solver law, whose purpose is to catch an answer of the family
  *     (`WeightedPaths.answer`) that is not the row's Result: each row's
  *     Result is the family's `solved`.
  *   - The reading law, whose purpose is to catch a point whose program does
  *     not answer its reference (inputs encoded otherwise than the program's
  *     header gives them, a node bound where its successors are not): each
  *     point's reference is the row's Result, its claim this suite, and the
  *     program's reading by the reference reading, tabling(weak_head)
  *     knowing top within `WeightedPathsPointsReferenceTest.stepLimit` steps
  *     and `tableLimit` tables, is that Result alone.
  */
class WeightedPathsPointsReferenceTest extends gezi.generatedinputs.FailFastSuite with snapshot4s.munit.SnapshotAssertions:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  override val munitTimeout: scala.concurrent.duration.Duration = WeightedPathsPointsReferenceTest.timeout

  private val group = ReductionTesting.group

  private val table = CsesPoints.weightedPaths

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.problems.sharedExpansions, _ => group.cses.weightedPaths, _ => table.rows(group))

  test("every row of the table reads") {
    val rows = table.rows(group).map(row => s"  ${row.point}: ${row.site} => ${WeightedPathsPointsReferenceTest.shown(row.result)}")
    assertFileSnapshot((table.table +: rows).mkString("", "\n", "\n"), "speculative_untabling/points.txt")
  }

  test("each row's Result is the problem's definition's") {
    table.rows(group).foreach(row => assertEquals(row.result, WeightedPathsDefinitions.value(row.site), row.point))
  }

  test("each row's Result is the family's answer") {
    table.rows(group).foreach(row => assertEquals(table.family.solved(CsesFamily.Drawn(Vector(row.site), 0L)), Vector(row.result), row.point))
  }

  test("each program reads its row's Result") {
    table.rows(group).zip(table.points(group)).foreach((row, point) =>
      assertEquals(point.point, row.point)
      assertEquals(point.drawn.reference, Reference.Computed(Vector(row.result.normalForm), getClass.getName), row.point)
      gezi.weakhead.NormalForms
        .normalForms(gezi.weakhead.Mode.TablingWeakHead, Reduction.programRoot(point.drawn.program))
        .result(
          gezi.weakhead.ReadingState
            .knowingTop(WeightedPathsPointsReferenceTest.stepLimit, gezi.weakhead.ReadingConfiguration.withoutFacts)
            .copy(tableLimit = WeightedPathsPointsReferenceTest.tableLimit)
        ) match
        case gezi.weakhead.Computed.Done(forms, _) =>
          assert(
            forms.map(form => gezi.frontend.Defunctionalization.instructionTerm[gezi.ir.NoFacts.type](form)).toSet == Set(row.result.normalForm),
            row.point
          )
        case gezi.weakhead.Computed.Stopped(after) =>
          fail(s"${row.point}: the reading stopped: ${after.exhausted}, ${after.budget.spent} steps, ${after.tables.held} tables")
    )
  }

/** The limits of the reading law, and how a Result is shown. */
object WeightedPathsPointsReferenceTest:

  /** A natural Result in decimal. */
  def shown(value: NativeValue): String = value match
    case NativeValue.Binary(digits) => CsesFamily.naturalOf(digits).toString
    case other                      => throw IllegalArgumentException(s"no natural: $other")

  /** The steps of the reading law's readings: 1,400,000, about twice the
    * largest reading of the rows. MEASURED 2026-11-21 by a scratch probe in
    * contest-corpora's tests (CPUs 8 and 9 of contest.slice, nice 10, the
    * 1-minute load 5 to 9), tabling(weak_head) knowing top, each row's
    * program read to its one normal form: weighted_paths_shared_chain (five
    * nodes, K = 5, one seed of 999,999,999) 695,790 steps and 294,330
    * tables; weighted_paths_sink_three_steps 16,230 and 6,787,
    * weighted_paths_diamond 10,502 and 4,560, weighted_paths_sink_zero_steps
    * 1,710 and 847. The shared chain is past the CSES tables' 150,000 steps
    * and the reference reading's 50,000 tables, which is why the table has a
    * suite of its own: five squarings of numbers of about 30 bits.
    */
  val stepLimit: Long = 1400000

  /** The tables of the reading law's readings, about twice the largest
    * reading's (`stepLimit`).
    */
  val tableLimit: Int = 600000

  /** The deadline of the suite's tests, 15 s, about two and a half times
    * the reading law's: MEASURED 2026-11-21 (CPUs 8 and 9 of contest.slice,
    * nice 10, the 1-minute load about 5), the reading law took 5.9 s, its
    * shared chain's 695,790 steps most of it, and every other test of the
    * suite less than 0.1 s. The rows cannot be made smaller: they are the
    * data the family's files give, and their reading is the law.
    */
  val timeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(15, scala.concurrent.duration.SECONDS)

/** The laws of the generator of `WeightedPaths`, on graphs of generated
  * sizes drawn from generated seeds.
  *
  *   - The graph law, whose purpose is to catch a graph some node of which
  *     the root does not reach, or an edge that goes to an earlier node, to
  *     the node itself or twice to one node, or an out-degree outside 1 to 3:
  *     every successor is a later node, each node's successors are distinct,
  *     each node but the last has 1 to 3 of them and the last none, and every
  *     node is reached by the walk from the root along the numbering.
  *   - The linearity law, whose purpose is to catch a site whose data writes
  *     a node again at each path that reaches it, or whose IR grows faster
  *     than the graph: the exchange line of the root (`ExchangeText`), which
  *     binds each repeated instruction once, has at most
  *     `WeightedPathsLawTest.charactersPerElement` characters for each node
  *     and each edge.
  *   - The seeds law, whose purpose is to catch a recurring site whose
  *     nodes draw more seeds than the three of the site, or a seed outside 0
  *     to 10^9 + 6: every seed is below the modulus, and a recurring site
  *     has at most three.
  */
class WeightedPathsLawTest extends GeneratedProperties:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts
  given gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private def seeds: Gen[Long] = Gen.long(hedgehog.Range.constant(0L, (1L << 31) - 1))

  private def nodes: Gen[Int] = Gen.int(hedgehog.Range.linear(1, 2000))

  property("every node is reached from the root, along edges to later nodes", _.copy(testLimit = 50)) {
    for
      seed <- seeds.forAll
      count <- nodes.forAll
    yield
      val successors = WeightedPaths.graph(count, Draws.fromSeed(seed))._1
      val reached = successors.indices.foldLeft(Set(0))((found, node) => if found.contains(node) then found ++ successors(node) else found)
      Result.all(
        List(
          Result.assert(successors.size == count).log(s"${successors.size} nodes"),
          Result.assert(successors.zipWithIndex.forall((next, node) => next.forall(later => later > node && later < count))).log("edges to later nodes"),
          Result.assert(successors.forall(next => next.distinct.size == next.size)).log("distinct successors"),
          Result.assert(successors.init.forall(next => next.size >= 1 && next.size <= 3) && successors.last.isEmpty).log("out-degrees"),
          Result.assert(reached.size == count).log(s"${reached.size} of $count nodes reached")
        )
      )
  }

  property("the root's exchange line is linear in the graph", _.copy(testLimit = 10)) {
    for
      seed <- seeds.forAll
      count <- Gen.int(hedgehog.Range.linear(1, 100)).forAll
    yield
      val draws = Draws.fromSeed(seed)
      val (successors, afterGraph) = WeightedPaths.graph(count, draws)
      val nodeSeeds = CsesFamily.drawnValues(count, afterGraph)(WeightedPaths.belowModulus)._1
      val site = WeightedPaths.Site(1, nodeSeeds, successors)
      val root = WeightedPaths.arguments(site) match
        case Vector(_, Term.Closed(instruction)) => instruction
        case other                               => throw IllegalStateException(s"no closed root among ${other.size} arguments")
      val written = ExchangeText.line[gezi.ir.NoFacts.type](root).length
      Result
        .assert(written <= WeightedPathsLawTest.charactersPerElement * (count + site.edges))
        .log(s"$written characters for $count nodes and ${site.edges} edges")
  }

  property("seeds are below the modulus, and a recurring site has at most three", _.copy(testLimit = 50)) {
    for
      seed <- seeds.forAll
      family <- Gen.elementUnsafe(List(WeightedPaths.distinctFamilies.head.head, WeightedPaths.recurringFamilies.head.head)).forAll
    yield
      val site = family.drawnSite(Draws.fromSeed(seed))._1
      val below = Result.assert(site.seeds.forall(value => value >= 0 && value < WeightedPaths.modulus)).log(site.toString)
      family.seeds match
        case WeightedPaths.Seeds.Distinct  => below
        case WeightedPaths.Seeds.Recurring => below.and(Result.assert(site.seeds.distinct.size <= WeightedPaths.recurringValues).log(site.toString))
  }

/** The bound of the linearity law. */
object WeightedPathsLawTest:

  /** About one and a half times the largest number of characters for a
    * node and an edge measured, most of them the seeds' naturals of about
    * 30 bits each, about 680 characters a node: MEASURED 2026-11-21 by a
    * scratch probe in contest-corpora's tests (CPUs 8 and 9 of
    * contest.slice, nice 10), the exchange line of the root of a site of
    * distinct seeds had 1,354 characters at 2 nodes and 1 edge, 451 for a
    * node and an edge, and 555,171 at 1,000 nodes and 1,993 edges (185),
    * 1,073,968 at 2,000 and 3,990 (179), 2,067,192 at 4,000 and 7,976 (173)
    * and 3,945,284 at 8,000 and 16,042 (164).
    */
  val charactersPerElement: Int = 1000
