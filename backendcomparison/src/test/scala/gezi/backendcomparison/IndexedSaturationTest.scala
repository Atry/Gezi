package gezi.backendcomparison

import gezi.saturation.StopSignal
import gezi.ematching.closures.ClosureCompilation
import gezi.egraph.Justification
import gezi.egraph.MadeNodes
import gezi.egraph.UnionRecord
import gezi.ematching.indexing.Indexing
import gezi.orientation.Orientation
import gezi.orientation.Orientations
import gezi.saturation.End
import gezi.saturation.Run
import gezi.saturation.Saturation
import gezi.ir.BuiltInRule
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.ir.Store
import gezi.ir.{Apply, Parallel, Slot}

/** Orientations compiled by the index, run by the closure backend and
  * saturated: the whole pipeline the comparison runs, on hand-written
  * generic examples.
  */
class IndexedSaturationTest extends gezi.generatedinputs.FailFastSuite:

  private val leaf = Instruction.opaque("leaf")
  private val name = Instruction.opaque("name")

  private def saturated(
      orientations: Vector[Orientation],
      store: Store,
      patternInstructions: Vector[Instruction],
      input: Instruction,
      stop: StopSignal
  ): Run =
    val program = Indexing.program(orientations, Indexing.codesMet(orientations, patternInstructions :+ input))
    Saturation.run(
      program,
      ClosureCompilation.compiled(program),
      BuiltInRule.all,
      store,
      Orientations.headArityBounds(orientations),
      patternInstructions,
      Vector(input),
      budget = 1000,
      explained = false,
      stop
    )

  private def orientation(matched: Pattern, added: Pattern) = Orientation(
    index = 0,
    lemma = LemmaIdentifier(0),
    direction = Direction.Forward,
    arity = 1,
    matched = matched,
    added = added,
    functions = Vector.empty,
    essential = Vector(0),
    shared = Vector.empty
  )

  stoppableTest("idempotence unites a parallel of one class with that class") { stopped =>
    val pair = Instruction(Parallel(leaf, leaf))
    val result = saturated(
      Vector(
        orientation(
          Pattern.Parallel(Pattern.Metavariable(0), Pattern.Metavariable(0)),
          Pattern.Metavariable(0)
        )
      ),
      Store(Set(leaf)),
      Vector.empty,
      pair,
      StopSignal.completedWith(stopped)
    )
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
    assertEquals(result.graph.matchesFound, 3)
  }

  stoppableTest("an added side applying a lambda takes a β step, united with the body") { stopped =>
    val applied = Instruction(Apply(name, leaf))
    val identity = Code(Slot(0))
    val result = saturated(
      Vector(
        orientation(
          Pattern.Apply(Pattern.InstructionReference(name), Pattern.Metavariable(0)),
          Pattern.Apply(
            Pattern.Thunk(identity, Vector(Hole.Bound(0)), Vector.empty),
            Pattern.Metavariable(0)
          )
        )
      ),
      Store(Set(leaf, name)),
      Vector(name),
      applied,
      StopSignal.completedWith(stopped)
    )
    assertEquals(result.inputNodes, Vector(2))
    assertEquals(result.inputNodesMade, 2)
    assertEquals(result.end, End.FixedPoint(1))
    assertEquals(
      result.graph.unions,
      Vector(
        UnionRecord(
          2,
          4,
          Justification.Lemma(LemmaIdentifier(0), Vector(Some(1))),
          Some(MadeNodes(3, 4))
        ),
        UnionRecord(4, 1, Justification.Beta(3), None)
      )
    )
    assertEquals(result.graph.nodeCount, 5)
    assertEquals(result.graph.matchesFound, 2)
  }
