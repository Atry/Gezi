package gezi.ematching.indexing

import gezi.egraph.Head
import gezi.egraph.MemberShape
import gezi.egraph.UserRole
import gezi.orientation.Orientation
import gezi.ematching.Building
import gezi.ematching.LayerTemplate
import gezi.ematching.Seed
import gezi.ematching.SeedKey
import gezi.ematching.SeedKind
import gezi.ematching.Step
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Hole
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.{Apply, Slot}

class IndexingTest extends gezi.generatedinputs.FailFastSuite:

  private type C = NoFacts.type
  private given C = NoFacts

  private val head = NoFacts.opaque("head")
  private val other = NoFacts.opaque("other")
  private val third = NoFacts.opaque("third")

  private def metavariable(index: Int): Pattern[C] = Pattern.Metavariable(index)

  private def instruction(name: Configured[C]): Pattern[C] =
    Pattern.InstructionReference(name)

  private def application(
      function: Pattern[C],
      argument: Pattern[C]
  ): Pattern[C] =
    Pattern.Apply(function, argument)

  private def orientation(
      index: Int,
      arity: Int,
      matched: Pattern[C],
      added: Pattern[C],
      essential: Vector[Int],
      functions: Vector[Int] = Vector.empty
  ) = Orientation(
    index = index,
    lemma = LemmaIdentifier(index),
    direction = Direction.Forward,
    arity = arity,
    matched = matched,
    added = added,
    functions = functions,
    essential = essential,
    shared = Vector.empty
  )

  private def seeds(orientations: Orientation[C]*) =
    Indexing.program[C](orientations.toVector, Set.empty).seeds

  test("a matched instruction is its own seed, filed under the instruction") {
    assertEquals(
      seeds(
        orientation(0, 1, instruction(head), instruction(other), Vector.empty)
      ),
      Map(
        (SeedKind.Add, SeedKey.InstructionNode(head)) -> Vector(
          Seed[C](0, Vector(Step.Root[C](0, 1)), 1, Vector(None))
        )
      )
    )
  }

  test("a metavariable met again is checked against its first binding") {
    val idempotence = orientation(
      0,
      1,
      Pattern.Parallel(metavariable(0), metavariable(0)),
      metavariable(0),
      Vector(0)
    )
    assertEquals(
      seeds(idempotence),
      Map(
        (SeedKind.Merge, SeedKey.Parallel[C]()) -> Vector(
          Seed[C](
            0,
            Vector(
              Step.Layer[C](0, LayerTemplate.Parallel, Vector(1, 2)),
              Step.Root[C](1, 3),
              Step.Root[C](2, 4),
              Step.Same[C](4, 3),
              Step.Root[C](0, 5)
            ),
            5,
            Vector(Some(3))
          )
        )
      )
    )
  }

  test(
    "every compound position is a seed, climbing to the root by signature where the siblings are determined"
  ) {
    val matched =
      application(
        instruction(head),
        Pattern.Parallel(metavariable(0), metavariable(1))
      )
    val program = seeds(
      orientation(
        0,
        2,
        matched,
        application(instruction(other), metavariable(1)),
        Vector(0, 1)
      )
    )
    assertEquals(
      program((SeedKind.Add, SeedKey.Headed(Head(head, 1)))),
      Vector(
        Seed[C](
          0,
          Vector(
            Step.Layer[C](0, LayerTemplate.Apply, Vector(1, 2)),
            Step.Root[C](1, 3),
            Step.InstructionIn(head, 3),
            Step.Root[C](2, 4),
            Step.EachMember[C](4, MemberShape.Parallel, 5),
            Step.Layer[C](5, LayerTemplate.Parallel, Vector(6, 7)),
            Step.Root[C](6, 8),
            Step.Root[C](7, 9),
            Step.Root[C](0, 10)
          ),
          10,
          Vector(Some(8), Some(9))
        )
      )
    )
    assertEquals(
      program((SeedKind.Add, SeedKey.Parallel[C]())),
      Vector(
        Seed[C](
          0,
          Vector(
            Step.Layer[C](0, LayerTemplate.Parallel, Vector(1, 2)),
            Step.Root[C](1, 3),
            Step.Root[C](2, 4),
            Step.Root[C](0, 5),
            Step.InstructionNode(head, 6),
            Step.Lookup[C](LayerTemplate.Apply, Vector(6, 5), 7),
            Step.Root[C](7, 8)
          ),
          8,
          Vector(Some(3), Some(4))
        )
      )
    )
    assertEquals(program.size, 2)
  }

  test(
    "a witness is matched once, and no seed stands inside a shallow witness"
  ) {
    val matched = application(
      instruction(head),
      application(instruction(other), metavariable(0))
    )
    val program =
      seeds(orientation(0, 1, matched, instruction(third), Vector.empty))
    assertEquals(
      program,
      Map(
        (SeedKind.Add, SeedKey.Headed(Head(head, 1))) -> Vector(
          Seed[C](
            0,
            Vector(
              Step.Layer[C](0, LayerTemplate.Apply, Vector(1, 2)),
              Step.Root[C](1, 3),
              Step.InstructionIn(head, 3),
              Step.Once(
                Vector(
                  Step.Root[C](2, 4),
                  Step.EachHeadMember(4, Head(other, 1), 5),
                  Step.Layer[C](5, LayerTemplate.Apply, Vector(6, 7)),
                  Step.Root[C](6, 8),
                  Step.InstructionIn(other, 8),
                  Step.Root[C](7, 9)
                )
              ),
              Step.Root[C](0, 10)
            ),
            10,
            Vector(Some(9))
          )
        )
      )
    )
  }

  test(
    "copies of a witness share its metavariables: the first is matched once, the later looked up by signature and checked against its class"
  ) {
    val copy = application(instruction(other), metavariable(0))
    val matched = Pattern.Parallel(copy, copy)
    assertEquals(
      seeds(orientation(0, 1, matched, instruction(third), Vector.empty)),
      Map(
        (SeedKind.Add, SeedKey.Parallel[C]()) -> Vector(
          Seed[C](
            0,
            Vector(
              Step.Layer[C](0, LayerTemplate.Parallel, Vector(1, 2)),
              Step.Once(
                Vector(
                  Step.Root[C](1, 3),
                  Step.EachHeadMember(3, Head(other, 1), 4),
                  Step.Layer[C](4, LayerTemplate.Apply, Vector(5, 6)),
                  Step.Root[C](5, 7),
                  Step.InstructionIn(other, 7),
                  Step.Root[C](6, 8)
                )
              ),
              Step.InstructionNode(other, 9),
              Step.Lookup[C](LayerTemplate.Apply, Vector(9, 8), 10),
              Step.Root[C](2, 11),
              Step.Root[C](10, 12),
              Step.Same[C](12, 11),
              Step.Root[C](0, 13)
            ),
            13,
            Vector(Some(8))
          )
        )
      ),
      "no seed stands inside either copy"
    )
  }

  test(
    "a lambda position is a seed under Closure, binding its metavariable to the class"
  ) {
    val matched = Pattern.Parallel(Pattern.Closure[C](0), metavariable(1))
    val program =
      seeds(orientation(0, 2, matched, instruction(other), Vector(0, 1)))
    assertEquals(
      program((SeedKind.Add, SeedKey.Closure[C]())),
      Vector(
        Seed[C](
          0,
          Vector(
            Step.Root[C](0, 1),
            Step.HasClosure[C](1),
            Step.EachUser[C](1, UserRole.Left, 2),
            Step.Layer[C](2, LayerTemplate.Parallel, Vector(3, 4)),
            Step.Root[C](4, 5),
            Step.Root[C](2, 6)
          ),
          6,
          Vector(Some(1), Some(5))
        )
      )
    )
  }

  test("seeds of one key are in the order of their orientations") {
    val first = orientation(
      0,
      1,
      Pattern.Parallel(metavariable(0), instruction(head)),
      instruction(other),
      Vector(0)
    )
    val second = orientation(
      1,
      1,
      Pattern.Parallel(instruction(other), metavariable(0)),
      instruction(head),
      Vector(0)
    )
    assertEquals(
      seeds(first, second)((SeedKind.Add, SeedKey.Parallel[C]()))
        .map(_.orientation),
      Vector(0, 1)
    )
  }

  test(
    "an added side reads the applications of function metavariables and of lambdas"
  ) {
    val identity = Code(Slot(0))
    val lambda = Pattern.Thunk[C](identity, Vector(Hole.Bound(0)), Vector.empty)
    val added = application(
      application(Pattern.Closure[C](0), metavariable(1)),
      application(lambda, application(metavariable(1), metavariable(0)))
    )
    assertEquals(
      Indexing.building(added, Vector(0)),
      Building.Apply(
        Building.Apply(Building.Value[C](0), Building.Value[C](1), read = true),
        Building.Apply(
          Building.Thunk[C](identity, Vector(Hole.Bound(0)), Vector.empty),
          Building
            .Apply(Building.Value[C](1), Building.Value[C](0), read = false),
          read = true
        ),
        read = true
      )
    )
    assertEquals(
      Indexing.building(added, Vector.empty),
      Building.Apply(
        Building
          .Apply(Building.Value[C](0), Building.Value[C](1), read = false),
        Building.Apply(
          Building.Thunk[C](identity, Vector(Hole.Bound(0)), Vector.empty),
          Building
            .Apply(Building.Value[C](1), Building.Value[C](0), read = false),
          read = true
        ),
        read = false
      )
    )
  }

  test("a code's body is one layer over references to its subcodes") {
    val slot = Code(Slot(1))
    val application = Code(Apply(slot, slot))
    val program = Indexing.program[C](Vector.empty, Set(slot, application))
    assertEquals(
      program.codes,
      Map(
        slot -> Building.Value[C](1),
        application -> Building.Apply(
          Building.CodeBody[C](slot),
          Building.CodeBody[C](slot),
          read = false
        )
      )
    )
  }
