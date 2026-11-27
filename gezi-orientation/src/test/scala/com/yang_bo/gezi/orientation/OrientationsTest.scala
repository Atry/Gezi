package com.yang_bo.gezi.orientation

import com.yang_bo.gezi.ir.Direction
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.Pattern

class OrientationsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:
  private given NoFacts.type = NoFacts

  private type C = NoFacts.type

  private val head = NoFacts.opaque("head")
  private val other = NoFacts.opaque("other")

  private def metavariable(index: Int): Pattern[C] = Pattern.Metavariable(index)

  private def application(
      function: Pattern[C],
      argument: Pattern[C]
  ): Pattern[C] =
    Pattern.Apply(function, argument)

  private def orientation(
      matched: Pattern[C],
      added: Pattern[C]
  ): Orientation[C] = Orientation(
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

  test(
    "an orientation whose added side is a metavariable or a strict subpattern only unites"
  ) {
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

  test(
    "the head arity bound of an instruction is the most arguments any matched side applies it to"
  ) {
    val bounds = Orientations.headArityBounds(
      Vector(
        orientation(matched, metavariable(0)),
        orientation(
          application(
            metavariable(0),
            application(Pattern.InstructionReference(other), metavariable(1))
          ),
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
