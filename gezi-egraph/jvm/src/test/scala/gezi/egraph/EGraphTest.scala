package gezi.egraph

import gezi.ir.Code
import gezi.ir.CodeLayer
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.{Apply, NoinlineLeaf, Parallel, Slot, Thunk}

class EGraphTest extends gezi.generatedinputs.FailFastSuite:

  /** `pair` is the parallel of `function first` and `function second`; the
    * three names are noinline leaves.
    */
  private val function = Instruction.opaque("function")
  private val first = Instruction.opaque("first")
  private val second = Instruction.opaque("second")
  private val functionOfFirst = Instruction(Apply(function, first))
  private val functionOfSecond = Instruction(Apply(function, second))
  private val pair = Instruction(Parallel(functionOfFirst, functionOfSecond))

  private val store = Store(noinline = Set(function, first, second))

  private def added(graph: EGraph, instruction: Instruction): EGraph =
    val (next, _) = graph.instructionAdded(instruction)
    next

  private val lemma = Justification.Lemma(LemmaIdentifier(0), Vector.empty)

  test("an instruction's term is added children first, its instructions filed in that order") {
    val (graph, node) = EGraph.empty(store, Map.empty, explained = false).instructionAdded(pair)
    assertEquals(node, 5)
    assertEquals(
      graph.nodes.map(_.layer),
      Vector(
        NoinlineLeaf(function),
        NoinlineLeaf(first),
        Apply(0, 1),
        NoinlineLeaf(second),
        Apply(0, 3),
        Parallel(2, 4)
      )
    )
    assertEquals(
      graph.instructionFilings,
      Vector(
        function -> 0,
        first -> 1,
        functionOfFirst -> 2,
        second -> 3,
        functionOfSecond -> 4,
        pair -> 5
      )
    )
    assertEquals(graph.deltas, List(5, 4, 3, 2, 1, 0))
  }

  test("a layer over the same roots is the same node, and a later instruction is filed onto it") {
    val graph = added(added(EGraph.empty(store, Map.empty, explained = false), functionOfFirst), second)
    val united = graph.unionWorked(1, 3, lemma, None)
    assertEquals(united.root(3), 1, "a tie goes to the first node's root")
    val (withSecond, node) = united.instructionAdded(functionOfSecond)
    assertEquals(node, 2)
    assertEquals(withSecond.nodeCount, 4)
    assertEquals(withSecond.instructionFilings.last, functionOfSecond -> 2)
    assertEquals(withSecond.nodeInstruction(2), Some(functionOfFirst))
  }

  /** In a graph that records the terms made, a layer over other nodes of the
    * same roots is a made duplicate: a new node of the found node's class
    * that denotes the term made, its congruence with the found node
    * recorded, no class grown.
    */
  test("recording the terms made, a layer over other nodes of the same roots is a made duplicate in the found node's class") {
    val graph = added(added(EGraph.empty(store, Map.empty, explained = true), functionOfFirst), second)
    val united = graph.unionWorked(1, 3, lemma, None)
    assertEquals(united.root(3), 1, "a tie goes to the first node's root")
    val (withSecond, node) = united.instructionAdded(functionOfSecond)
    assertEquals(node, 4)
    assertEquals(withSecond.root(node), withSecond.root(2))
    assert(!withSecond.live(node), "a made duplicate is not live")
    assertEquals(withSecond.madeLayer(node), Apply(0, 3))
    assertEquals(withSecond.nodeCount, 5)
    assertEquals(withSecond.canonicalNodeCount, 4)
    assertEquals(withSecond.joiningUnionCount, united.joiningUnionCount)
    assertEquals(withSecond.unions.last, UnionRecord(4, 2, Justification.Congruence, None))
    assertEquals(withSecond.instructionFilings.last, functionOfSecond -> 4)
    assertEquals(withSecond.nodeInstruction(4), Some(functionOfSecond))
    assertEquals(withSecond.nodeInstruction(2), Some(functionOfFirst))
    val (again, nodeAgain) = withSecond.layerAdded(Apply(0, 3))
    assertEquals(nodeAgain, 4, "the same made layer is the same node")
    assertEquals(again.nodeCount, 5)
  }

  test("a union re-reads the smaller class's users: a congruent user is a duplicate") {
    val graph = added(EGraph.empty(store, Map.empty, explained = false), pair)
    val united = graph.unionWorked(1, 3, lemma, None)
    assert(!united.live(4), "function second, now function first, is a duplicate")
    assert(united.live(2))
    assertEquals(
      united.unionQueue.toList,
      List(PendingUnion(4, 2, Justification.Congruence, None))
    )
    val (pending, rest) = united.unionTaken.get
    val congruent =
      rest.unionWorked(pending.first, pending.second, pending.justification, pending.made)
    assertEquals(
      congruent.unions,
      Vector(UnionRecord(1, 3, lemma, None), UnionRecord(4, 2, Justification.Congruence, None))
    )
    assertEquals(congruent.root(2), 4, "a tie goes to the first node's root")
    assertEquals(congruent.signatures.get(Parallel(4, 4)), Some(5))
    assertEquals(
      congruent.members(4, MemberShape.Apply).filter(congruent.live),
      Vector(2)
    )
  }

  test("applications are filed under the heads of their function's class within the bound") {
    val once = Instruction(Apply(function, first))
    val twice = Instruction(Apply(once, first))
    val thrice = Instruction(Apply(twice, first))
    val spines = store
    val graph = added(EGraph.empty(spines, Map(function -> 2), explained = false), thrice)
    assertEquals(graph.classHeads(0), Vector(Head(function, 0)))
    assertEquals(graph.nodeHeads(2), Vector(Head(function, 1)))
    assertEquals(graph.headMembers(2, Head(function, 1)), Vector(2))
    assertEquals(graph.nodeHeads(3), Vector(Head(function, 2)))
    assertEquals(graph.nodeHeads(4), Vector.empty)
  }

  test("a class that gains a head files its applications under it and pushes them") {
    val other = Instruction.opaque("other")
    val otherOfFirst = Instruction(Apply(other, first))
    val heads = store.copy(noinline = store.noinline + other)
    val graph =
      added(added(EGraph.empty(heads, Map(function -> 1), explained = false), otherOfFirst), function)
    assertEquals(graph.deltas, List(3, 2, 1, 0))
    val united = graph.unionWorked(0, 3, lemma, None)
    assertEquals(united.root(3), 0)
    assertEquals(united.classHeads(0), Vector(Head(function, 0)))
    assertEquals(united.nodeHeads(2), Vector(Head(function, 1)))
    assertEquals(united.headMembers(2, Head(function, 1)), Vector(2))
    assertEquals(united.deltas, List(3, 2, 2, 3, 2, 1, 0))
  }

  test("a thunk with a hole is a closure state, and a read application queues a β step") {
    val identity = Code(Slot(0))
    val thunk = Instruction(Thunk(identity, Vector(Hole.Bound(0)), Vector.empty))
    val applied = Instruction(Apply(thunk, first))
    val closures = store
    val graph = added(EGraph.empty(closures, Map.empty, explained = false), applied)
    val state = ClosureState(0, Nil, 1)
    assert(graph.hasClosure(0))
    assertEquals(graph.closureStates(0), Vector(state))
    val read = graph.applicationRead(2)
    assert(read.readable(2))
    assertEquals(read.betaQueue.toList, List(PendingBeta(2, state)))
    assertEquals(read.applicationRead(2), read)
  }

  test("a duplicate thunk's closure state is dead: its twin's state stands for it") {
    // λx. x f, its filling f read by the code, so that the thunks over first and over second are two terms.
    val appliedToFilling = Code(Apply(Code(Slot(0)), Code(Slot(1))))
    val thunkOverFirst = Instruction(Thunk(appliedToFilling, Vector(Hole.Bound(0)), Vector(first)))
    val thunkOverSecond = Instruction(Thunk(appliedToFilling, Vector(Hole.Bound(0)), Vector(second)))
    val thunks = Instruction(Parallel(thunkOverFirst, thunkOverSecond))
    val appliedToSecond = Instruction(Apply(thunkOverSecond, second))
    val closures = store
    val graph = added(EGraph.empty(closures, Map.empty, explained = false), thunks)
    val united = graph.unionWorked(0, 2, lemma, None)
    assert(!united.live(3), "the thunk over second, now over first, is a duplicate")
    assertEquals(united.closureStates(3), Vector.empty)
    val (pending, rest) = united.unionTaken.get
    val congruent =
      rest.unionWorked(pending.first, pending.second, pending.justification, pending.made)
    val twinState = ClosureState(1, Nil, 1)
    assertEquals(congruent.closureStates(congruent.root(1)), Vector(twinState))
    val (withApplication, application) = congruent.instructionAdded(appliedToSecond)
    val read = withApplication.applicationRead(application)
    assertEquals(
      read.betaQueue.toList,
      List(PendingBeta(application, twinState)),
      "one β step, with the twin's state"
    )
  }

  test("entries are written again without the duplicates once half of them are") {
    val entries = Entries(Vector(1, 2, 3, 4), 0)
    val once = entries.oneDead(_ != 2)
    assertEquals(once, Entries(Vector(1, 2, 3, 4), 1))
    assertEquals(
      once.oneDead(node => node != 2 && node != 3),
      Entries(Vector(1, 4), 0)
    )
  }

  test("a closure state given every argument lists them in lambda order") {
    val state = ClosureState(0, Nil, 3).applied(10).applied(11)
    assertEquals(state.left, 1)
    assertEquals(state.argumentsWith(12), Vector(10, 11, 12))
  }
