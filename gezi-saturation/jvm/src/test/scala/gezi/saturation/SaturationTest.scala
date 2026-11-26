package gezi.saturation

import gezi.saturation.StopSignal
import gezi.egraph.GraphBuilding
import gezi.egraph.GraphView
import gezi.egraph.Justification
import gezi.egraph.UnionRecord
import gezi.ematching.Building
import gezi.ematching.CompiledProgram
import gezi.ematching.Match
import gezi.ematching.Matching
import gezi.ematching.OrientationPlan
import gezi.ematching.Program
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ir.BuiltInRule
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.Parallel

/** The loop over a compiled program written by hand for one orientation, a
  * parallel of two classes: with `Merge`, idempotence `X ∥ X = X`; with
  * `Add`, `X ∥ Y = X ∥ name`.
  */
private final class ParallelProgram(kind: SeedKind, name: Instruction)
    extends CompiledProgram:

  def matches(
      matchedKind: SeedKind,
      key: SeedKey,
      graph: GraphView,
      delta: Int
  ): Matching = (matchedKind, key, graph.layer(delta)) match
    case (`kind`, SeedKey.Parallel, Parallel(left, right))
        if kind == SeedKind.Add || graph.root(left) == graph.root(right) =>
      Matching(Vector(Match(0, graph.root(delta), Vector(Some(graph.root(left))))), 0)
    case _ => Matching.none

  def added[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) = (kind, bindings) match
    case (SeedKind.Merge, Vector(Some(node))) => (graph, node)
    case (SeedKind.Add, Vector(Some(node))) =>
      val (withName, nameNode) = graph.instructionAdded(name)
      withName.layerAdded(Parallel(node, nameNode))
    case other => throw IllegalArgumentException(s"no added side for $other")

  def shared[Graph <: GraphBuilding[Graph]](
      orientation: Int,
      part: Int,
      graph: Graph,
      bindings: Vector[Option[Int]]
  ): (Graph, Int) =
    throw IllegalArgumentException("the orientation has no shared subterm")

  def body[Graph <: GraphBuilding[Graph]](
      code: Code,
      graph: Graph,
      slotValues: Vector[Int]
  ): (Graph, Int) =
    throw IllegalArgumentException("the orientation reads no code")

class SaturationTest extends gezi.generatedinputs.FailFastSuite:

  private val leaf = Instruction.opaque("leaf")
  private val name = Instruction.opaque("name")
  private val pair = Instruction(Parallel(leaf, leaf))

  private val store = Store(noinline = Set(leaf, name))

  /** The plan saturation reads; the stub builds the added side itself. */
  private val program = Program(
    Map.empty,
    Vector(
      OrientationPlan(
        LemmaIdentifier(0),
        Direction.Forward,
        Building.Value(0),
        Vector(0),
        Vector.empty
      )
    ),
    Map.empty
  )

  stoppableTest("idempotence unites a parallel of one class with that class, then reaches its fixed point") { stopped =>
    val result = Saturation.run(
      program,
      ParallelProgram(SeedKind.Merge, name),
      BuiltInRule.all,
      store,
      Map.empty,
      Vector.empty,
      Vector(pair),
      budget = 1000,
      explained = false,
      StopSignal.completedWith(stopped)
    )
    assertEquals(result.inputNodes, Vector(1))
    assertEquals(result.inputNodesMade, 2)
    assertEquals(result.end, End.FixedPoint(1))
    assertEquals(
      result.graph.unions,
      Vector(
        UnionRecord(
          1,
          0,
          Justification.Lemma(LemmaIdentifier(0), Vector(Some(0))),
          None
        )
      )
    )
    assertEquals(result.graph.nodeCount, 2)
    assertEquals(result.graph.matchesFound, 3)
  }

  stoppableTest("the run stops as soon as the instances that changed the graph reach the budget") { stopped =>
    val result = Saturation.run(
      program,
      ParallelProgram(SeedKind.Add, name),
      BuiltInRule.all,
      store,
      Map.empty,
      Vector.empty,
      Vector(pair),
      budget = 1,
      explained = false,
      StopSignal.completedWith(stopped)
    )
    assertEquals(result.end, End.BudgetExhausted(1))
    assertEquals(result.graph.instances, 1)
    assertEquals(result.graph.nodeCount, 4)
  }

  /** Purpose: catch a saturation that ignores its stop signal, or that
    * reads it only after matching a delta.
    */
  test("a stop requested before the first delta ends the run stopped with no instance") {
    object Requested extends StopSignal:
      def stopRequested: Boolean = true
    val result = Saturation.run(
      program,
      ParallelProgram(SeedKind.Add, name),
      BuiltInRule.all,
      store,
      Map.empty,
      Vector.empty,
      Vector(pair),
      budget = 1000,
      explained = false,
      Requested
    )
    assertEquals(result.end, End.Stopped(0))
    assertEquals(result.graph.matchesFound, 0)
  }

  test("slot values put the arguments at the holes' slots and the fillings at the others") {
    assertEquals(
      Saturation.slotValues(
        Vector(Hole.Bound(2), Hole.Ignored, Hole.Bound(0)),
        Vector(20, 21, 22),
        Vector(30, 31)
      ),
      Vector(22, 30, 20, 31)
    )
  }
