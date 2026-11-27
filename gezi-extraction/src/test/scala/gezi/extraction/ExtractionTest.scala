package gezi.extraction

import gezi.saturation.StopSignal
import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.ir.NoFacts
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.{Apply, Choice, NoinlineLeaf, Parallel}

class ExtractionTest extends gezi.generatedinputs.FailFastSuite:

  /** `applied` is `function first`; the other three are noinline leaves. */
  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private val function = NoFacts.opaque("function")
  private val first = NoFacts.opaque("first")
  private val second = NoFacts.opaque("second")
  private val applied = NoFacts.application(function, first)

  /** The number each instruction is spelled with. */
  private val numbers =
    Map(function -> 0, first -> 1, second -> 2, applied -> 3)

  private val store = Store(
    noinline = Set(function, first, second),
    gezi.ir.TermConstruction(NoFacts)
  )

  /** The cost of a spelling is its number of nodes. */
  private object Size extends StatelessCostModel[C, Int]:
    def cost(shape: Shape[C], childCosts: Vector[Int]): Int = 1 + childCosts.sum
    val ordering: Ordering[Int] = Ordering.Int
    def pricedChildren(shape: Shape[C]): Vector[Boolean] =
      shape.children.map(_ => true)

  private def spelling(shape: Shape[C], children: Vector[String]): String =
    shape match
      case Shape.Name(instruction) => s"name${numbers(instruction)}"
      case Shape.Node(_, NoinlineLeaf(instruction)) =>
        s"leaf${numbers(instruction)}"
      case Shape.Node(_, layer) =>
        s"${layer.getClass.getSimpleName}${children.mkString("(", ",", ")")}"
      case pattern =>
        s"${pattern.getClass.getSimpleName}${children.mkString("(", ",", ")")}"

  private def spelled(extracted: Extracted[C, Int], root: Int): String =
    val (_, result) = Extraction.spelled(
      extracted,
      root,
      Spelled[String, Unit]((), Map.empty)
    ) { (accumulator, shape, children) =>
      (accumulator, spelling(shape, children))
    }
    result

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  /** The graph of `function first` and `second` united. */
  private def united: (EGraph[C], Int) =
    val (withApplied, appliedNode) = EGraph
      .empty(store, Map.empty, explained = false)
      .instructionAdded(applied)
    val (withSecond, secondNode) = withApplied.instructionAdded(second)
    (withSecond.unionWorked(appliedNode, secondNode, lemma, None), appliedNode)

  test(
    "equal keys leave the heap in the order of SWI-Prolog's library(heaps)"
  ) {
    val heap = PairingHeap.of(Vector((1, "a"), (1, "b"), (1, "c"), (0, "d")))
    def drained(
        current: PairingHeap[Int, String],
        taken: Vector[String]
    ): Vector[String] = current.taken match
      case None                   => taken
      case Some((_, value, rest)) => drained(rest, taken :+ value)
    assertEquals(drained(heap, Vector.empty), Vector("d", "c", "b", "a"))
  }

  stoppableTest("a class is spelled by its cheapest production") { stopped =>
    val (graph, node) = united
    val root = graph.root(node)
    val extracted = CountedExtraction
      .fixed(graph, Set.empty, Size, StopSignal.completedWith(stopped))
      .getOrElse(fail("the extraction was stopped"))
    assertEquals(extracted.best(root).cost, 1)
    assertEquals(spelled(extracted, root), s"leaf${numbers(second)}")
  }

  stoppableTest("a name spells its class in one leaf") { stopped =>
    val (withApplied, appliedNode) = EGraph
      .empty(store, Map.empty, explained = false)
      .instructionAdded(applied)
    val extracted = CountedExtraction
      .fixed(withApplied, Set(applied), Size, StopSignal.completedWith(stopped))
      .getOrElse(fail("the extraction was stopped"))
    assertEquals(
      spelled(extracted, withApplied.root(appliedNode)),
      s"name${numbers(applied)}"
    )
    val unnamed = CountedExtraction
      .fixed(withApplied, Set.empty, Size, StopSignal.completedWith(stopped))
      .getOrElse(fail("the extraction was stopped"))
    assertEquals(
      spelled(unnamed, withApplied.root(appliedNode)),
      s"Apply(leaf${numbers(function)},leaf${numbers(first)})"
    )
  }

  stoppableTest(
    "a production that reads its own class reads it by an entry that does not"
  ) { stopped =>
    val (graph, node) = united
    val root = graph.root(node)
    val (withLoop, loop) =
      graph.layerAdded(Apply(graph.instructionNode(function).get, root))
    val looped = withLoop.unionWorked(loop, root, lemma, None)
    val loopRoot = looped.root(root)
    val extracted = CountedExtraction
      .fixed(looped, Set.empty, Size, StopSignal.completedWith(stopped))
      .getOrElse(fail("the extraction was stopped"))
    assertEquals(spelled(extracted, loopRoot), s"leaf${numbers(second)}")
    val looplessCosts = extracted.classes(loopRoot).bestLoopless.map(_.cost)
    assertEquals(looplessCosts, Some(1))
  }

  test("an absorbed choice is no production") {
    val (graph, node) = united
    val root = graph.root(node)
    val (withParallel, parallel) =
      graph.layerAdded(Parallel(root, graph.instructionNode(first).get))
    val (withChoice, choice) = withParallel.layerAdded(Choice(root, parallel))
    val joined = withChoice.unionWorked(choice, root, lemma, None)
    val (productions, _) = Extraction.productions(joined, Set.empty)
    assert(
      !productions.exists(
        _.shape == Shape.Node(choice, joined.layer(choice).map(joined.root))
      )
    )
    assert(
      Extraction.absorbedChoice(
        joined,
        joined.root(root),
        joined.layer(choice).map(joined.root)
      )
    )
  }
