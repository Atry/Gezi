package gezi.contest.corpora.reductions

import gezi.weakhead.Mode
import gezi.weakhead.Reading
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Term

/** The helpers of the reduction families' `.plt` files that read normal forms:
  * `set_read/2`, every normal form the judge answers
  * (`Reduction.answeredNormalForms`), as a set; `numeral_form/2`, the canonical
  * term of a unary numeral; and a problem's snapshot as terms.
  *
  * THE BUDGET: the Prolog `set_read/2` read under findall with no budget; here
  * every reading gets `Reading.budgetSteps(10)`, 20,000,000 steps, the family's
  * limit of 10 seconds (`Reduction.defaultLimits`), the intent being a bound no
  * small program reaches: a reading the budget stops fails its test, it is
  * never read as an empty set.
  */
object SetReading:

  val limit: Long = Reading.budgetSteps(10)

  private val group: ReductionGroup = ReductionTesting.group

  /** Every normal form the mode answers for the program, as a set. */
  def setRead(mode: Mode, program: Term): Set[DeBruijnTerm] =
    Reduction.answeredNormalForms(mode, program, limit) match
      case NormalFormReading.Finished(normalForms) => normalForms.toSet
      case stopped => throw AssertionError(s"a reading stopped: $stopped")

  /** The canonical terms of the unary numerals, as a set. */
  def numeralForms(numbers: Vector[Int]): Set[DeBruijnTerm] =
    numbers
      .map(number =>
        group.scott
          .canonical("unary", Scott.unaryTree(number))
          .deBruijnTerm(Map.empty)
      )
      .toSet

  /** `problem_snapshot/2`: the canonical terms of the problem's expected trees,
    * as a set.
    */
  def snapshot(problem: ReductionProblem): Set[DeBruijnTerm] =
    problem.expected.trees
      .map(tree =>
        group.scott.canonical(problem.typeName, tree).deBruijnTerm(Map.empty)
      )
      .toSet

  /** The problem of the point. */
  def problem(
      problems: Vector[ReductionProblem],
      point: String
  ): ReductionProblem =
    problems
      .find(_.point == point)
      .getOrElse(throw AssertionError(s"no problem $point"))

  /** The test of the small points: each reads its snapshot under the mode. */
  def assertSnapshotsRead(
      suite: munit.FunSuite,
      mode: Mode,
      problems: Vector[ReductionProblem],
      points: Vector[String]
  ): Unit =
    points.foreach(point =>
      val found = problem(problems, point)
      suite.assertEquals(
        (point, setRead(mode, found.program)),
        (point, snapshot(found))
      )
    )

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_collect_keys.plt`).
  */
class CollectKeysReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  test("theSetIsTheTotalsOfTheOrdersAndWalks") {
    for
      (rows, columns, keys) <- Vector(
        (2, 2, Vector(3)),
        (2, 2, Vector(1, 2)),
        (2, 3, Vector(2, 3))
      )
      (count, edges) = CollectKeys.grid(rows, columns)
      shortest = CollectKeys.shortestTotal(count, edges, keys, 0)
      slack <- Vector(-1, 0, 2)
    do
      val budget = shortest + slack
      val read = setRead(
        Mode.TablingWeakHead,
        CollectKeys.collectKeysTerm(
          group.attractors,
          count,
          edges,
          keys,
          0,
          budget
        )
      )
      val expected = numeralForms(
        CollectKeys.collectKeysTotals(count, edges, keys, 0, budget)
      )
      assertEquals(
        (rows, columns, keys, budget, read),
        (rows, columns, keys, budget, expected)
      )
  }

  test("theSmallPointAndTheNearMissReadTheirSnapshots") {
    val problems = CollectKeys.problems(group)
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      problems,
      Vector("reduction_collect_keys_small", "reduction_collect_keys_near_miss")
    )
    assertEquals(
      snapshot(problem(problems, "reduction_collect_keys_small")).size,
      1
    )
    assertEquals(
      snapshot(problem(problems, "reduction_collect_keys_near_miss")),
      Set.empty[DeBruijnTerm]
    )
  }

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_path_lengths.plt`).
  */
class PathLengthsReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private lazy val group = ReductionTesting.group

  /** The family's problems, read once
    * (`theSmallPointsAndTheNearMissReadTheirSnapshots`).
    */
  private lazy val problems = PathLengths.problems(group)

  /** The group, its attractors and the family's problems, forced before the
    * first test, so that no test pays for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group, _ => group.attractors, _ => problems)

  test("theSetIsTheLengthsOfTheLayers") {
    for
      (shape, size) <- Vector(
        (GraphShape.TwoRings, 2),
        (GraphShape.TwoRings, 3),
        (GraphShape.ChordRing, 3),
        (GraphShape.ChordRing, 4)
      )
      graph = Graphs.graph(shape, size)
      bound <- Vector(0, 2, 5, 8)
    do
      val read = setRead(
        Mode.TablingWeakHead,
        PathLengths.pathLengthsTerm(
          group.attractors,
          graph.count,
          graph.edges,
          graph.start,
          graph.target,
          bound
        )
      )
      val expected = numeralForms(
        PathLengths.walkLengths(graph.edges, graph.start, graph.target, bound)
      )
      assertEquals((shape, size, bound, read), (shape, size, bound, expected))
  }

  test("theSmallPointsAndTheNearMissReadTheirSnapshots") {
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      problems,
      Vector(
        "reduction_path_lengths_chord_ring_small",
        "reduction_path_lengths_two_rings_small",
        "reduction_path_lengths_chord_ring_near_miss"
      )
    )
    assertEquals(
      snapshot(
        problem(problems, "reduction_path_lengths_chord_ring_near_miss")
      ),
      Set.empty[DeBruijnTerm]
    )
  }

/** The law of the courses' program with its step budget, whose purpose is to
  * catch a program whose answers, the closed βη normal forms N with program ⊑_O
  * N, are not the completable courses: on every prerequisite graph of three
  * courses (each course's prerequisites any subset of the other two, 64 graphs,
  * cycles included), tabling(weak_head) reads the numerals of
  * `Hidden37Courses.completable`.
  *
  * FIXME: the untabled weak head is exact when it finishes,
  * https://github.com/Atry/private-overlay/issues/2043 tabling(weak_head) in
  * general is not (a re-entered table is answered as empty, the least fixed
  * point by set inclusion), so on the cyclic graphs this law checks
  * tabling(weak_head)'s reading against the completable courses, not the
  * program's answers by Definition 14. Candidates: a proof that the courses'
  * program re-enters no table, or a law by consistency (◇) beside the reading.
  */
class Hidden37CoursesReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  test("theCompletableCoursesOfEveryGraphOfThreeCourses") {
    val count = 3
    val choices = (0 until count).toVector.map(course =>
      (0 until count).toVector
        .filter(_ != course)
        .toSet
        .subsets()
        .map(_.toVector.sorted)
        .toVector
    )
    val graphs = choices.foldLeft(Vector(Vector.empty[Vector[Int]]))(
      (partial, options) => partial.flatMap(prefix => options.map(prefix :+ _))
    )
    graphs.foreach(prerequisites =>
      val read = setRead(
        Mode.TablingWeakHead,
        Hidden37Courses.coursesTerm(group.attractors, count, prerequisites)
      )
      val expected =
        numeralForms(Hidden37Courses.completable(count, prerequisites))
      assertEquals((prerequisites, read), (prerequisites, expected))
    )
  }

/** The law of the obstacles' program with its step budget, whose purpose is to
  * catch a program whose answers are not the removal counts of the walks
  * across: on every grid of two rows and two or three columns whose corners are
  * free (each other cell free or an obstacle), at every budget from 0 to 2,
  * tabled weak head reads the numerals of `Hidden37Obstacles.removalCounts`.
  * The untabled reading would follow every walk of up to 18 steps one by one;
  * the tabled one reads each state once.
  */
class Hidden37ObstaclesReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  test("theRemovalCountsOfEverySmallGrid") {
    for
      columns <- Vector(2, 3)
      inner = (0 until 2 * columns).toVector.filterNot(cell =>
        cell == 0 || cell == 2 * columns - 1
      )
      obstacles <- inner.toSet.subsets().toVector
      grid = Vector.tabulate(2, columns)((row, column) =>
        if obstacles.contains(row * columns + column) then 1 else 0
      )
      budget <- 0 to 2
    do
      val read = setRead(
        Mode.TablingWeakHead,
        Hidden37Obstacles.obstaclesTerm(group.attractors, grid, budget)
      )
      val expected = numeralForms(Hidden37Obstacles.removalCounts(grid, budget))
      assertEquals((grid, budget, read), (grid, budget, expected))
  }

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_reachable_set.plt`).
  */
class ReachableSetReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  test("theSetIsTheBreadthFirstReachableSet") {
    for
      (shape, size) <- Vector(
        (GraphShape.TwoRings, 2),
        (GraphShape.TwoRings, 3),
        (GraphShape.ChordRing, 3),
        (GraphShape.ChordRing, 5)
      )
      graph = Graphs.graph(shape, size)
      start <- 0 until graph.count
    do
      val read = setRead(
        Mode.TablingWeakHead,
        ReachableSet.reachableSetTerm(graph.count, graph.edges, start)
      )
      val expected = numeralForms(
        ReachableSet.reachableNodes(graph.count, graph.edges, start)
      )
      assertEquals((shape, size, start, read), (shape, size, start, expected))
  }

  test("theSmallPointsReadTheirSnapshots") {
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      ReachableSet.problems(group),
      Vector(
        "reduction_reachable_set_two_rings_small",
        "reduction_reachable_set_chord_ring_small",
        "reduction_reachable_set_two_rings_near_miss"
      )
    )
  }

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_shortest_superstring.plt`).
  */
class ShortestSuperstringReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  test("theSetIsTheLengthsOfTheOrdersAndOverlaps") {
    for
      words <- Vector(
        Vector(Vector(1, 0, 1), Vector(0, 1, 1)),
        Vector(Vector(1, 1), Vector(1, 0), Vector(0, 1)),
        Vector(Vector(1, 0, 1, 1), Vector(1, 1, 0, 0), Vector(0, 0, 1, 0))
      )
      shortest = ShortestSuperstring.shortestSuperstring(words)
      slack <- Vector(-1, 0, 2)
    do
      val budget = shortest + slack
      val read = setRead(
        Mode.TablingWeakHead,
        ShortestSuperstring.superstringTerm(group.attractors, words, budget)
      )
      val expected =
        numeralForms(ShortestSuperstring.superstringTotals(words, budget))
      assertEquals((words, budget, read), (words, budget, expected))
  }

  test("theSmallPointAndTheNearMissReadTheirSnapshots") {
    val problems = ShortestSuperstring.problems(group)
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      problems,
      Vector(
        "reduction_shortest_superstring_small",
        "reduction_shortest_superstring_near_miss"
      )
    )
    assertEquals(
      snapshot(problem(problems, "reduction_shortest_superstring_small")).size,
      1
    )
    assertEquals(
      snapshot(problem(problems, "reduction_shortest_superstring_near_miss")),
      Set.empty[DeBruijnTerm]
    )
  }

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_smallest_team.plt`).
  */
class SmallestTeamReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  private val smallTeams: Vector[(Int, Vector[Vector[Int]])] = Vector(
    (2, Vector(Vector(0), Vector(1), Vector(0, 1))),
    (3, Vector(Vector(0), Vector(1, 2), Vector(2), Vector(0, 1))),
    (3, Vector(Vector(0), Vector(1))),
    (4, Vector(Vector(0, 3), Vector(1), Vector(2, 3), Vector(1, 2), Vector(0)))
  )

  test("theSetIsTheSizesOfTheSufficientTeams") {
    for
      (skillCount, people) <- smallTeams
      budget <- 0 to people.size
    do
      val read = setRead(
        Mode.TablingWeakHead,
        SmallestTeam.teamTerm(group.attractors, skillCount, people, budget)
      )
      val expected =
        numeralForms(SmallestTeam.teamSizes(skillCount, people, budget))
      assertEquals((people, budget, read), (people, budget, expected))
  }

  test("theSmallPointAndTheNearMissReadTheirSnapshots") {
    val problems = SmallestTeam.problems(group)
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      problems,
      Vector(
        "reduction_smallest_team_small",
        "reduction_smallest_team_near_miss"
      )
    )
    assertEquals(
      snapshot(problem(problems, "reduction_smallest_team_small")).size,
      1
    )
    assertEquals(
      snapshot(problem(problems, "reduction_smallest_team_near_miss")),
      Set.empty[DeBruijnTerm]
    )
  }

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_two_coloring.plt`), under
  * tabling(weak_head).
  */
class TwoColoringReadingTest extends gezi.generatedinputs.FailFastSuite:
  import SetReading.*
  private val group = ReductionTesting.group

  /** The group's attractors, forced before the first test, so that no test pays
    * for reading them.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => group.attractors)

  test("smallGraphsReadTheirColorings") {
    Vector(
      (3, Vector((0, 1), (1, 2), (2, 0))),
      (4, Vector((0, 1), (1, 2), (2, 3), (3, 0))),
      (3, Vector((0, 1)))
    ).foreach((count, edges) =>
      val read = setRead(
        Mode.TablingWeakHead,
        TwoColoring.twoColoringTerm(group.attractors, count, edges)
      )
      assertEquals(
        (count, edges, read.size),
        (count, edges, TwoColoring.properColorings(count, edges).size)
      )
    )
  }

  test("theSmallPointAndTheTrapsReadTheirSnapshots") {
    assertSnapshotsRead(
      this,
      Mode.TablingWeakHead,
      TwoColoring.problems(group),
      Vector(
        "reduction_two_coloring_ring_small",
        "reduction_two_coloring_odd_ring_near_miss",
        "reduction_two_coloring_chord_near_miss"
      )
    )
  }
