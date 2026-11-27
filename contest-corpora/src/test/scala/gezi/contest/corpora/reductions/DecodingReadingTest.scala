package gezi.contest.corpora.reductions

import gezi.weakhead.Mode
import gezi.weakhead.Reading
import gezi.weakhead.oldcorpora.Confirmation
import gezi.weakhead.oldcorpora.ScottDataType
import gezi.weakhead.oldcorpora.ScottDecoding
import gezi.contest.corpora.claims.Ending
import gezi.contest.corpora.merges.ClaimEndings
import gezi.frontend.Term
import gezi.frontend.Term.λ

/** The helper of the reduction families' `.plt` files that decodes a program's
  * answers (`decoded/4` under findall, the trees sorted): every tree the Scott
  * decoder reads of the program's root, as problems' trees.
  *
  * THE BUDGET: the Prolog decoded under findall with no budget; here a decoding
  * gets `Reading.budgetSteps(10)`, 20,000,000 steps, the family's 10 seconds,
  * the intent being a bound no small program reaches: a decoding the budget
  * stops fails its test.
  */
object Decoding:

  val limit: Long = Reading.budgetSteps(10)

  /** The distinct trees the program decodes to at the type under the mode. */
  def trees(mode: Mode, program: Term, typeName: String): Set[ScottTree] =
    Reduction.decodedTrees(mode, program, typeName, limit) match
      case Some(found) => found.map(Scott.fromDecoded).toSet
      case None => throw AssertionError(s"a decoding ran past $limit steps")

/** The reading tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_empty_set_reachability.plt`), on the
  * judge (`ClaimEndings`, 20 seconds as steps, as the Prolog's `ending/3`).
  */
class EmptySetReachabilityReadingTest
    extends gezi.generatedinputs.FailFastSuite:
  private val group = ReductionTesting.group

  private def expected(holds: Boolean): Ending =
    if holds then Ending.Succeeded else Ending.Failed

  test("theCyclicProgramAgreesWithBreadthFirstSearch") {
    for
      (shape, size) <- Vector(
        (GraphShape.TwoRings, 2),
        (GraphShape.TwoRings, 3),
        (GraphShape.ChordRing, 3),
        (GraphShape.ChordRing, 5)
      )
      graph = Graphs.graph(shape, size)
      start <- 0 until graph.count
      target <- 0 until graph.count
    do
      val ending = ClaimEndings.trueEnding(
        Mode.TablingWeakHead,
        EmptySetReachability.cyclicGraphTerm(
          graph.count,
          graph.edges,
          start,
          target
        )
      )
      assertEquals(
        (shape, size, start, target, ending),
        (
          shape,
          size,
          start,
          target,
          expected(Graphs.reachable(graph.edges, start, target))
        )
      )
  }

  test("aCutGraphAnswersNothing") {
    Vector(
      (GraphShape.TwoRings, 3),
      (GraphShape.TwoRings, 5),
      (GraphShape.ChordRing, 4),
      (GraphShape.ChordRing, 6)
    ).foreach((shape, size) =>
      val (graph, _) = EmptySetReachability.cutGraph(shape, size)
      val ending = ClaimEndings.trueEnding(
        Mode.TablingWeakHead,
        EmptySetReachability.cyclicGraphTerm(
          graph.count,
          graph.edges,
          graph.start,
          graph.target
        )
      )
      assertEquals((shape, size, ending), (shape, size, Ending.Failed))
    )
  }

  test("theTreeReadsWhenTheTargetIsOnTheDepthFirstPath") {
    val term = EmptySetReachability.infiniteTreeTerm(
      group.attractors,
      TreeOrder.OneFirst,
      None,
      Vector(1, 1, 1)
    )
    assertEquals(
      ClaimEndings.trueEnding(Mode.TablingWeakHead, term),
      Ending.Succeeded
    )
  }

/** The reading test of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_reduction_interpreter.plt`).
  */
class ReductionInterpreterReadingTest
    extends gezi.generatedinputs.FailFastSuite:
  private val group = ReductionTesting.group

  test("smallProgramsDecodeToTheReference") {
    ReductionInterpreterTest.testExpressions.foreach(expression =>
      val expected =
        Scott.binaryTree(ReductionInterpreter.referenceValue(expression))
      assertEquals(
        (
          expression,
          Decoding.trees(
            Mode.TablingWeakHead,
            ReductionInterpreter.programSurface(group, expression),
            "binary"
          )
        ),
        (expression, Set(expected))
      )
    )
  }

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_reduction_meanings.plt`). The Prolog
  * `meaning_confirmed/3` had no budget; here it gets `Decoding.limit`.
  */
class ReductionMeaningsReadingTest extends gezi.generatedinputs.FailFastSuite:

  test("trueIsTheUnaryZero") {
    val root = Reduction.programRoot(λ(t => λ(_ => t)))
    assertEquals(
      ScottDecoding.meaningConfirmed(
        root,
        ScottDataType.Booleans,
        Scott.leaf("true").decoded,
        Decoding.limit
      ),
      Confirmation.Confirmed
    )
    assertEquals(
      ScottDecoding.meaningConfirmed(
        root,
        ScottDataType.Unary,
        Scott.leaf("zero").decoded,
        Decoding.limit
      ),
      Confirmation.Confirmed
    )
  }

  test("theCountDecodesToHalf") {
    Vector(1, 2, 3, 6, 9).foreach(number =>
      assertEquals(
        (
          number,
          Decoding.trees(
            Mode.TablingWeakHead,
            ReductionMeanings.countSurface(number),
            "unary"
          )
        ),
        (number, Set(Scott.unaryTree((number + 1) / 2)))
      )
    )
  }

/** The tests of the deleted Prolog test (`git show
  * d32e69ff0^:lambda_jit/tests/contest_reduction_non_canonical.plt`).
  */
class ReductionNonCanonicalReadingTest
    extends gezi.generatedinputs.FailFastSuite:
  private val group = ReductionTesting.group

  private def treeValue(tree: ScottTree): BigInt = tree match
    case ScottTree("zero", Vector())     => 0
    case ScottTree("even", Vector(half)) => 2 * treeValue(half)
    case ScottTree("odd", Vector(half))  => 2 * treeValue(half) + 1
    case other => throw AssertionError(s"not a binary tree: $other")

  test("theReferenceFollowsTheDefinitionalPlus") {
    val trees = ReductionNonCanonicalTest.treesOfDepth(3)
    for
      left <- trees
      right <- trees
    do
      assertEquals(
        (
          left,
          right,
          Decoding.trees(
            Mode.TablingWeakHead,
            ReductionNonCanonical.sumSurface(group, left, right),
            "binary"
          )
        ),
        (left, right, Set(ReductionNonCanonical.plusTree(left, right)))
      )
  }

  test("everyProblemDecodesToItsNonCanonicalTree") {
    val problems = ReductionNonCanonical.problems(group)
    assert(problems.nonEmpty)
    problems.foreach(problem =>
      problem.expected match
        case Expected.One(tree) =>
          assertEquals(
            (
              problem.point,
              Decoding.trees(Mode.TablingWeakHead, problem.program, "binary")
            ),
            (problem.point, Set(tree))
          )
          assertNotEquals(
            (problem.point, tree),
            (problem.point, Scott.binaryTree(treeValue(tree)))
          )
        case other => fail(s"${problem.point} expects $other")
    )
  }
