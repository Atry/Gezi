package com.yang_bo.gezi.contest.corpora.merges

/** The tests of the deleted Prolog tests `contest_merge_graph.plt` and
  * `contest_merge_datalog.plt` (`git show d32e69ff0^:lambda_jit/tests/<name>`)
  * that read programs on the judge under tabling(weak_head): every start and
  * target, or every pair of constants, of small graphs, against the references
  * (breadth-first search, semi-naive evaluation).
  */
class MergeGraphEndingsTest extends MergeProblemsSuite:

  // Measured 2026-11-16 on 2 CPUs (contest-lean.slice, CPUs 10,11, nice 10), the 1-minute load 9 to 22 over the run, every deadline raised to 600 s: the slowest test of MergeGraphEndingsTest, "theProgramAgreesWithBreadthFirstSearch", takes 3.101 s; the bound is 1.5 times that rounded up to 5 s.
  // FIXME: this suite exceeds the 3 s default with no reason yet; its slow tests are to be made fast. https://github.com/Atry/private-overlay/issues/1925
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(5, "s")
  import com.yang_bo.gezi.weakhead.Mode
  import com.yang_bo.gezi.contest.corpora.claims.Ending

  private def expected(holds: Boolean): Ending =
    if holds then Ending.Succeeded else Ending.Failed

  test("theProgramAgreesWithBreadthFirstSearch") {
    val graph = MergeGraph(MergeTesting.problems)
    for
      (shape, size) <- Vector(
        (MergeGraph.GraphShape.TwoRings, 2),
        (MergeGraph.GraphShape.TwoRings, 3),
        (MergeGraph.GraphShape.ChordRing, 3),
        (MergeGraph.GraphShape.ChordRing, 5)
      )
      shown = MergeGraph.graph(shape, size)
      start <- 0 until shown.count
      target <- 0 until shown.count
    do
      val ending = ClaimEndings.trueEnding(
        Mode.TablingWeakHead,
        graph.graphTerm(shown.count, shown.edges, start, target)
      )
      assertEquals(
        (shape, size, start, target, ending),
        (
          shape,
          size,
          start,
          target,
          expected(MergeGraph.reachable(shown.edges, start, target))
        )
      )
  }

  test("everyTupleAgreesWithSemiNaiveEvaluation") {
    val datalog = MergeDatalog(MergeTesting.problems)
    for
      (shape, size) <- Vector(
        (MergeDatalog.DatalogShape.TwoRings, 2),
        (MergeDatalog.DatalogShape.Line, 3)
      )
      relation = datalog.relation(shape, size)
      from <- 0 until relation.count
      to <- 0 until relation.count
    do
      val ending = ClaimEndings.trueEnding(
        Mode.TablingWeakHead,
        datalog.ruleTerm(
          relation.rule,
          relation.count,
          relation.facts,
          from,
          to
        )
      )
      assertEquals(
        (relation.rule, from, to, ending),
        (
          relation.rule,
          from,
          to,
          expected(
            datalog.referenceHolds(relation.rule, relation.facts, from, to)
          )
        )
      )
  }
