package gezi.backendcomparison

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import scala.annotation.tailrec
import gezi.ir.{Apply, Parallel}

class FixedPointTest extends gezi.generatedinputs.FailFastSuite:

  /** `function first` and `function second`, paired in either order; the
    * three names are noinline leaves.
    */
  private type C = NoFacts.type

  private val function = NoFacts.opaque("function")
  private val first = NoFacts.opaque("first")
  private val second = NoFacts.opaque("second")
  private val functionOfFirst = NoFacts.application(function, first)
  private val functionOfSecond = NoFacts.application(function, second)
  private val pairInOrder = NoFacts.parallel(functionOfFirst, functionOfSecond)
  private val pairReversed = NoFacts.parallel(functionOfSecond, functionOfFirst)

  private val store = Store(noinline = Set(function, first, second), gezi.ir.TermConstruction(NoFacts))

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  private def added(graph: EGraph[C], instruction: Configured[C]): EGraph[C] =
    val (next, _) = graph.instructionAdded(instruction)
    next

  @tailrec
  private def unionsWorked(graph: EGraph[C]): EGraph[C] = graph.unionTaken match
    case Some((pending, rest)) =>
      unionsWorked(rest.unionWorked(pending.first, pending.second, pending.justification, pending.made))
    case None => graph

  private def united(graph: EGraph[C], instruction: Configured[C], other: Configured[C]): EGraph[C] =
    unionsWorked(
      graph.unionWorked(graph.instructionNode(instruction).get, graph.instructionNode(other).get, lemma, None)
    )

  test("the same classes over the same layers have one form, whatever the node numbers") {
    val inOrder = united(added(EGraph.empty(store, Map.empty, explained = false), pairInOrder), first, second)
    val reversed = united(
      added(added(EGraph.empty(store, Map.empty, explained = false), second), pairReversed),
      second,
      first
    )
    assertNotEquals(
      inOrder.nodes.map(_.layer),
      reversed.nodes.map(_.layer),
      "the two graphs number their nodes differently"
    )
    val form = FixedPoint.form(inOrder)
    assertEquals(form, FixedPoint.form(reversed))
    assertEquals((form.classes, form.liveNodes), (4, 5))
  }

  test("a union changes the form") {
    val apart = added(EGraph.empty(store, Map.empty, explained = false), pairInOrder)
    val joined = united(apart, first, second)
    assertNotEquals(FixedPoint.form(apart).digest, FixedPoint.form(joined).digest)
    assertEquals(FixedPoint.form(apart).classes, 6)
  }
