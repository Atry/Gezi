package gezi.orientation

import gezi.ir.Direction
import gezi.ir.Instruction
import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern

class OrientationsTest extends gezi.generatedinputs.FailFastSuite:

  private val head = Instruction.opaque("head")
  private val other = Instruction.opaque("other")

  private def metavariable(index: Int) = Pattern.Metavariable(index)

  private def application(function: Pattern, argument: Pattern) =
    Pattern.Apply(function, argument)

  private def orientation(matched: Pattern, added: Pattern) = Orientation(
    index = 0,
    lemma = LemmaIdentifier(0),
    direction = Direction.Forward,
    arity = 2,
    matched = matched,
    added = added,
    functions = Vector.empty,
    essential = Vector.empty,
    shared = Vector.empty
  )

  private val matched = application(
    application(Pattern.InstructionReference(head), metavariable(0)),
    Pattern.Parallel(metavariable(1), metavariable(1))
  )

  test("an orientation whose added side is a metavariable or a strict subpattern only unites") {
    assert(Orientations.onlyUnites(orientation(matched, metavariable(1))))
    assert(
      Orientations.onlyUnites(
        orientation(matched, Pattern.Parallel(metavariable(1), metavariable(1)))
      )
    )
    assert(!Orientations.onlyUnites(orientation(matched, matched)))
    assert(
      !Orientations.onlyUnites(
        orientation(matched, Pattern.InstructionReference(other))
      )
    )
  }

  test("positions are listed in pre-order with their paths") {
    assertEquals(
      Orientations.positions(matched).map((path, _) => path),
      Vector(
        Vector(),
        Vector(0),
        Vector(0, 0),
        Vector(0, 1),
        Vector(1),
        Vector(1, 0),
        Vector(1, 1)
      )
    )
  }

  test("the head arity bound of an instruction is the most arguments any matched side applies it to") {
    val bounds = Orientations.headArityBounds(
      Vector(
        orientation(matched, metavariable(0)),
        orientation(
          application(metavariable(0), application(Pattern.InstructionReference(other), metavariable(1))),
          metavariable(0)
        ),
        orientation(
          application(Pattern.InstructionReference(head), metavariable(0)),
          metavariable(0)
        )
      )
    )
    assertEquals(bounds, Map(head -> 2, other -> 1))
  }
