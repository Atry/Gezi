package com.yang_bo.gezi.orientation

import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.NonEmptyHoles
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Store
import com.yang_bo.gezi.ir.{Apply, Slot, Thunk}

/** The orientation compiler on hand-written generic lemmas, and the standard
  * order it numbers orientations by.
  */
class OrientationCompilationTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private val functionSlot = Code(Slot(1))
  private val argumentSlot = Code(Slot(0))
  private val apply = Code(Apply(functionSlot, argumentSlot))

  /** `name` and `other` are thunks of one and of two ignored binders over
    * `leaf`, an opaque instruction, which is noinline. The codes are
    * `apply(slot(1), slot(0))` and its two slots.
    */
  private type C = NoFacts.type

  private val leaf = NoFacts.opaque("leaf")
  private val name = NoFacts.thunk(
    argumentSlot,
    NonEmptyHoles(Hole.Ignored, Vector.empty),
    Vector(leaf)
  )
  private val other = NoFacts.thunk(
    argumentSlot,
    NonEmptyHoles(Hole.Ignored, Vector(Hole.Ignored)),
    Vector(leaf)
  )

  private val store = Store(Set(leaf), com.yang_bo.gezi.ir.TermConstruction(NoFacts))

  private def metavariable(index: Int): Pattern[C] = Pattern.Metavariable(index)

  private def application(
      function: Pattern[C],
      argument: Pattern[C]
  ): Pattern[C] = Pattern.Apply(function, argument)

  test(
    "the standard order puts numbers, the empty list, atoms and compounds in that order"
  ) {
    val sorted = Vector(
      PrologTerm.Compound(
        "f",
        Vector(PrologTerm.Atom("a"), PrologTerm.Atom("b"))
      ),
      PrologTerm.Atom("b"),
      PrologTerm.Compound("g", Vector(PrologTerm.Atom("a"))),
      PrologTerm.EmptyList,
      PrologTerm.Integer(2),
      PrologTerm.Compound("f", Vector(PrologTerm.Atom("x"))),
      PrologTerm.Atom("Z"),
      PrologTerm.Integer(1)
    ).sorted(using StandardOrder.ordering)
    assertEquals(
      sorted,
      Vector(
        PrologTerm.Integer(1),
        PrologTerm.Integer(2),
        PrologTerm.EmptyList,
        PrologTerm.Atom("Z"),
        PrologTerm.Atom("b"),
        PrologTerm.Compound("f", Vector(PrologTerm.Atom("x"))),
        PrologTerm.Compound("g", Vector(PrologTerm.Atom("a"))),
        PrologTerm.Compound(
          "f",
          Vector(PrologTerm.Atom("a"), PrologTerm.Atom("b"))
        )
      )
    )
  }

  test(
    "a side of metavariables alone is matched by no orientation, and equal sides by the forward one"
  ) {
    val compiled = OrientationCompilation.compiled(
      Vector(
        LemmaSides(
          LemmaIdentifier(0),
          1,
          application(Pattern.InstructionReference(name), metavariable(0)),
          metavariable(0)
        ),
        LemmaSides(
          LemmaIdentifier(1),
          1,
          Pattern.InstructionReference(other),
          Pattern.InstructionReference(other)
        )
      ),
      store
    )
    assertEquals(
      compiled.orientations.map(orientation =>
        (orientation.lemma, orientation.direction)
      ),
      Vector(
        (LemmaIdentifier(1), Direction.Forward),
        (LemmaIdentifier(0), Direction.Forward)
      )
    )
    assertEquals(compiled.orientations.map(_.index), Vector(0, 1))
    assertEquals(compiled.orientations(1).essential, Vector(0))
    // The matched side `other` is a reference and is filed too.
    assertEquals(compiled.patternInstructions, Vector(other, name))
  }

  test(
    "an eta-shaped thunk pattern is read as a closure of a function metavariable"
  ) {
    val lambda =
      Pattern.Thunk[C](apply, Vector(Hole.Bound(0)), Vector(metavariable(0)))
    val compiled = OrientationCompilation.compiled(
      Vector(
        LemmaSides(
          LemmaIdentifier(0),
          2,
          application(
            application(Pattern.InstructionReference(name), lambda),
            metavariable(1)
          ),
          application(
            application(Pattern.InstructionReference(other), metavariable(1)),
            lambda
          )
        )
      ),
      store
    )
    assertEquals(compiled.orientations.size, 2)
    compiled.orientations.foreach(orientation =>
      assertEquals(orientation.functions, Vector(0))
      assertEquals(orientation.essential, Vector(0, 1))
      assert(OrientationCompilation.mentions(orientation.matched).contains(0))
    )
    assertEquals(
      compiled.orientations.map(_.matched).collect {
        case Pattern.Apply(Pattern.Apply(_, Pattern.Closure(index)), _) =>
          index
      },
      Vector(0)
    )
  }
