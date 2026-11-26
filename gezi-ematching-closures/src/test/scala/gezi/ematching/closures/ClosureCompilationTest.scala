package gezi.ematching.closures

import gezi.egraph.EGraph
import gezi.egraph.Justification
import gezi.egraph.MemberShape
import gezi.ematching.Building
import gezi.ematching.LayerTemplate
import gezi.ematching.Match
import gezi.ematching.Matching
import gezi.ematching.OrientationPlan
import gezi.ematching.Program
import gezi.ematching.Seed
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ematching.Step
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Store
import gezi.ir.{Apply, NoinlineLeaf, Parallel, Slot}

class ClosureCompilationTest extends gezi.generatedinputs.FailFastSuite:

  private val name = Instruction.opaque("name")
  private val first = Instruction.opaque("first")
  private val second = Instruction.opaque("second")
  private val same = Instruction(Parallel(first, first))
  private val different = Instruction(Parallel(first, second))
  private val nameOfFirst = Instruction(Apply(name, first))
  private val nameOfSecond = Instruction(Apply(name, second))

  private val store = Store(noinline = Set(name, first, second))

  private def added(graph: EGraph, instruction: Instruction): (EGraph, Int) =
    graph.instructionAdded(instruction)

  /** The seed of `X ∥ X` at its root, the index's for the orientation
    * `X ∥ X = X`.
    */
  private val idempotence = Seed(
    0,
    Vector(
      Step.Layer(0, LayerTemplate.Parallel, Vector(1, 2)),
      Step.Root(1, 3),
      Step.Root(2, 4),
      Step.Same(4, 3),
      Step.Root(0, 5)
    ),
    5,
    Vector(Some(3))
  )

  private def plan(added: Building) = OrientationPlan(
    LemmaIdentifier(0),
    Direction.Forward,
    added,
    Vector(0),
    Vector.empty
  )

  test("a seed's steps find exactly the matches of its pattern") {
    val program = Program(
      Map((SeedKind.Merge, SeedKey.Parallel) -> Vector(idempotence)),
      Vector(plan(Building.Value(0))),
      Map.empty
    )
    val compiled = ClosureCompilation.compiled(program)
    val (withSame, sameNode) = added(EGraph.empty(store, Map.empty, explained = false), same)
    val (graph, differentNode) = added(withSame, different)
    assertEquals(
      compiled.matches(SeedKind.Merge, SeedKey.Parallel, graph, sameNode),
      Matching(Vector(Match(0, sameNode, Vector(Some(0)))), 0)
    )
    assertEquals(
      compiled.matches(SeedKind.Merge, SeedKey.Parallel, graph, differentNode),
      Matching.none
    )
    assertEquals(
      compiled.matches(SeedKind.Add, SeedKey.Parallel, graph, sameNode),
      Matching.none
    )
  }

  test("the matches of the entries an Each step reads come out in their order, and a witness once") {
    val members = Seed(
      0,
      Vector(
        Step.Root(0, 1),
        Step.EachMember(1, MemberShape.Apply, 2),
        Step.Layer(2, LayerTemplate.Apply, Vector(3, 4)),
        Step.Root(4, 5)
      ),
      1,
      Vector(Some(5))
    )
    val witness = Seed(
      1,
      Vector(Step.Root(0, 1), Step.Once(members.steps.drop(1))),
      1,
      Vector(Some(5))
    )
    val program = Program(
      Map((SeedKind.Add, SeedKey.Apply) -> Vector(members, witness)),
      Vector(plan(Building.Value(0)), plan(Building.Value(0))),
      Map.empty
    )
    val (withFirst, firstNode) = added(EGraph.empty(store, Map.empty, explained = false), nameOfFirst)
    val (withSecond, secondNode) = added(withFirst, nameOfSecond)
    val graph = withSecond.unionWorked(firstNode, secondNode, Justification.Congruence, None)
    val firstArgument = graph.root(1)
    val secondArgument = graph.root(3)
    assertEquals(
      ClosureCompilation
        .compiled(program)
        .matches(SeedKind.Add, SeedKey.Apply, graph, firstNode),
      Matching(
        Vector(
          Match(0, firstNode, Vector(Some(firstArgument))),
          Match(0, firstNode, Vector(Some(secondArgument))),
          Match(1, firstNode, Vector(Some(firstArgument)))
        ),
        3
      ),
      "the Each step reads both members, the witness the first, which succeeds"
    )
  }

  test("a building adds its layers children first and reads what it marks") {
    val identity = Code(Slot(0))
    val body = Code(Apply(identity, identity))
    val program = Program(
      Map.empty,
      Vector(
        plan(
          Building.Apply(
            Building.InstructionNode(name),
            Building.Parallel(Building.Value(0), Building.Value(0)),
            read = true
          )
        )
      ),
      Map(
        identity -> Building.Value(0),
        body -> Building.Apply(
          Building.CodeBody(identity),
          Building.CodeBody(identity),
          read = false
        )
      )
    )
    val compiled = ClosureCompilation.compiled(program)
    val (graph, firstNode) = added(EGraph.empty(store, Map.empty, explained = false), first)
    val (withAdded, addedNode) = compiled.added(0, graph, Vector(Some(firstNode)))
    assertEquals(withAdded.layer(addedNode), Apply(1, 2))
    assertEquals(withAdded.layer(1), NoinlineLeaf(name))
    assertEquals(withAdded.layer(2), Parallel(firstNode, firstNode))
    assert(withAdded.readable(addedNode))
    val (withBody, bodyNode) = compiled.body(body, withAdded, Vector(addedNode))
    assertEquals(withBody.layer(bodyNode), Apply(addedNode, addedNode))
  }
