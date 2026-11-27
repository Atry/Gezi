package com.yang_bo.gezi.backendcomparison

import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.ematching.closures.ClosureCompilation
import com.yang_bo.gezi.egraph.Justification
import com.yang_bo.gezi.egraph.MadeNodes
import com.yang_bo.gezi.egraph.UnionRecord
import com.yang_bo.gezi.ematching.indexing.Indexing
import com.yang_bo.gezi.orientation.Orientation
import com.yang_bo.gezi.orientation.Orientations
import com.yang_bo.gezi.saturation.End
import com.yang_bo.gezi.saturation.Run
import com.yang_bo.gezi.saturation.Saturation
import com.yang_bo.gezi.ir.BuiltInRule
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.{Apply, Parallel, Slot}

/** Orientations compiled by the index, run by the closure backend and
  * saturated: the whole pipeline the comparison runs, on hand-written generic
  * examples.
  */
class IndexedSaturationTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private type C = NoFacts.type

  private given NoFacts.type = NoFacts

  private val leaf = NoFacts.opaque("leaf")
  private val name = NoFacts.opaque("name")

  private def saturated(
      orientations: Vector[Orientation[C]],
      store: Store[C],
      patternInstructions: Vector[Configured[C]],
      input: Configured[C],
      stop: StopSignal
  ): Run[C] =
    val program = Indexing.program(
      orientations,
      Indexing.codesMet(orientations, patternInstructions :+ input)
    )
    Saturation.run(
      program,
      ClosureCompilation.compiled(program),
      BuiltInRule.beforeOptIn,
      store,
      Orientations.headArityBounds(orientations),
      patternInstructions,
      Vector(input),
      budget = 1000,
      explained = false,
      stop
    )

  private def orientation(
      matched: Pattern[C],
      added: Pattern[C]
  ): Orientation[C] = Orientation(
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

  stoppableTest("idempotence unites a parallel of one class with that class") {
    stopped =>
      val pair = NoFacts.parallel(leaf, leaf)
      val result = saturated(
        Vector(
          orientation(
            Pattern
              .Parallel(Pattern.Metavariable[C](0), Pattern.Metavariable[C](0)),
            Pattern.Metavariable[C](0)
          )
        ),
        Store(Set(leaf), com.yang_bo.gezi.ir.TermConstruction(NoFacts)),
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

  stoppableTest(
    "an added side applying a lambda takes a β step, united with the body"
  ) { stopped =>
    val applied = NoFacts.application(name, leaf)
    val identity = Code(Slot(0))
    val result = saturated(
      Vector(
        orientation(
          Pattern.Apply(
            Pattern.InstructionReference(name),
            Pattern.Metavariable[C](0)
          ),
          Pattern.Apply(
            Pattern.Thunk[C](identity, Vector(Hole.Bound(0)), Vector.empty),
            Pattern.Metavariable[C](0)
          )
        )
      ),
      Store(Set(leaf, name), com.yang_bo.gezi.ir.TermConstruction(NoFacts)),
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
