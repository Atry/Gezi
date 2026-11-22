package gezi.contest.corpora.reductions

/** The snapshot of the programs of `problems/empty_set_reachability` and of
  * its tests, whose purpose is to catch a generator change that alters a
  * program, and the ports of its tests that do not evaluate.
  */
class EmptySetReachabilityTest extends GeneratedProgramsSuite("contest_empty_set_reachability"):
  def generated(group: ReductionGroup) =
    def form(term: gezi.frontend.Term): String = ReductionTesting.form(term)
    EmptySetReachability.points(group).map((point, graph) =>
      s"contest_hard/$point/program" -> (() => form(EmptySetReachability.graphTerm(group.attractors, graph)))
    ) ++ (for
      (shape, size) <- Vector((GraphShape.TwoRings, 2), (GraphShape.TwoRings, 3), (GraphShape.ChordRing, 3), (GraphShape.ChordRing, 5))
      graph = Graphs.graph(shape, size)
      start <- 0 until graph.count
      target <- 0 until graph.count
    yield s"cyclic_graph_term/${shape.written}/$size/$start/$target" -> (() =>
      form(EmptySetReachability.cyclicGraphTerm(graph.count, graph.edges, start, target))
    )) ++ Vector((GraphShape.TwoRings, 3), (GraphShape.TwoRings, 5), (GraphShape.ChordRing, 4), (GraphShape.ChordRing, 6)).map((shape, size) =>
      s"cut_graph_term/${shape.written}/$size" -> (() =>
        val (cut, _) = EmptySetReachability.cutGraph(shape, size)
        form(EmptySetReachability.cyclicGraphTerm(cut.count, cut.edges, cut.start, cut.target))
      )
    ) ++ Vector(
      "infinite_tree_term/one_first/both/111" -> (() =>
        form(EmptySetReachability.infiniteTreeTerm(group.attractors, TreeOrder.OneFirst, None, Vector(1, 1, 1)))
      )
    )

  test("theTreeWithoutABitDoesNotReachATargetHoldingIt") {
    assert(EmptySetReachability.treeReachable(Some(1), Vector(0, 1)).isEmpty)
    assertEquals(EmptySetReachability.treeReachable(Some(1), Vector(0, 0)), Some(2))
  }

  test("breadthFirstExpansions") {
    val expansions = Vector(
      EmptySetReachability.breadthFirstExpansions(TreeOrder.ZeroFirst, None, Vector()),
      EmptySetReachability.breadthFirstExpansions(TreeOrder.ZeroFirst, None, Vector(1)),
      EmptySetReachability.breadthFirstExpansions(TreeOrder.ZeroFirst, None, Vector(1, 1)),
      EmptySetReachability.breadthFirstExpansions(TreeOrder.OneFirst, None, Vector(1, 1))
    )
    assertEquals(expansions, Vector(0, 1, 3, 3))
  }

/** The snapshot of the problems of `problems/reachable_set` and of the
  * programs of its tests, whose purpose is to catch a generator change that
  * alters a program, type, expected trees or limits, and the port of its
  * test that does not evaluate.
  */
class ReachableSetTest extends GeneratedProgramsSuite("contest_reachable_set"):
  def generated(group: ReductionGroup) =
    def form(term: gezi.frontend.Term): String = ReductionTesting.form(term)
    ReductionTesting.problemLines(group, ReachableSet.problems(group)) ++ (for
      (shape, size) <- Vector((GraphShape.TwoRings, 2), (GraphShape.TwoRings, 3), (GraphShape.ChordRing, 3), (GraphShape.ChordRing, 5))
      graph = Graphs.graph(shape, size)
      start <- 0 until graph.count
    yield s"reachable_set_term/${shape.written}/$size/$start" -> (() =>
      form(ReachableSet.reachableSetTerm(graph.count, graph.edges, start))
    ))

  test("theNearMissReachesRingAOnly") {
    val (cut, _) = EmptySetReachability.cutGraph(GraphShape.TwoRings, 4)
    assertEquals(ReachableSet.reachableNodes(cut.count, cut.edges, cut.start), Vector(0, 1, 2, 3))
  }

/** The port of the test of `problems/smallest_team` that does not
  * evaluate.
  */
class SmallestTeamTest extends gezi.generatedinputs.FailFastSuite:

  test("theDynamicProgrammeFindsTheLeastEnumeratedSize") {
    GraphFamiliesTest.smallTeams.foreach((skillCount, people) =>
      assertEquals(
        (people, SmallestTeam.smallestTeam(skillCount, people)),
        (people, SmallestTeam.teamSizes(skillCount, people, people.size).headOption)
      )
    )
  }

/** The port of the test of the deleted Prolog file
  * (`git show 6ab16a338^:lambda_jit/corpora/contest_two_coloring.pl`) that
  * does not evaluate.
  */
class TwoColoringTest extends gezi.generatedinputs.FailFastSuite:

  test("theReferenceIsGenerateAndTest") {
    Vector(
      (3, Vector((0, 1), (1, 2), (2, 0))),
      (4, Vector((0, 1), (1, 2), (2, 3), (3, 0))),
      (5, Vector((0, 1), (2, 3))),
      (6, Vector((0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3))),
      (4, Vector((0, 2)))
    ).foreach((count, edges) =>
      val generated = (0 until (1 << count)).toVector
        .map(bits => (0 until count).toVector.map(node => (bits >> node) & 1))
        .filter(colors => edges.forall((from, to) => colors(from) != colors(to)))
        .map(TwoColoring.coloringCode)
        .distinct
        .sorted
      assertEquals((count, edges, TwoColoring.properColorings(count, edges)), (count, edges, generated))
    )
  }

object GraphFamiliesTest:

  /** The teams of the test helper `small_team/2`. */
  val smallTeams: Vector[(Int, Vector[Vector[Int]])] = Vector(
    (2, Vector(Vector(0), Vector(1), Vector(0, 1))),
    (3, Vector(Vector(0), Vector(1, 2), Vector(2), Vector(0, 1))),
    (3, Vector(Vector(0), Vector(1))),
    (4, Vector(Vector(0, 3), Vector(1), Vector(2, 3), Vector(1, 2), Vector(0)))
  )
