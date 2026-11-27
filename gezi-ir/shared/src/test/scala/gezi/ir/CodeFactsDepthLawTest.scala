package gezi.ir

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import scala.collection.immutable.BitSet

/** The facts of a code (`Code.facts`) on a chain of thunks nested 5,000 to
  * 10,000 deep, the shape a text in the multi-line CPS layout gives (a body
  * under a λ under a body …): each level
  * `Lk+1 = op (slot 1) (thunk Lk [bound 0] [slot 0])`, `op` an application or a
  * choice drawn for each level, over `L0 = slot 0 applied to slot 1`. Every
  * level reads slot 0 through the thunk, more than once since the thunk has a
  * hole, and slot 1 once, both outside a parallel's right operand.
  *
  * Purpose: catch a computation of the facts that recurses on the JVM stack
  * once per level of nesting, which overflowed on the contest point
  * `hidden_37_courses_large`, and facts that lose a slot's count or its reading
  * on the way. Measured 2026-11-19: with the facts read lazily, part by part,
  * the law threw `StackOverflowError` at these depths; computed as each code is
  * built, it passes in 0.76 s.
  */
class CodeFactsDepthLawTest extends GeneratedProperties:

  private val levels: Gen[List[Boolean]] =
    Gen
      .int(Range.linear(5000, 10000))
      .flatMap(depth => Gen.boolean.list(Range.singleton(depth)))

  /** The chain, an application at a level drawn true, a choice otherwise. */
  private def chain(applications: List[Boolean]): Code =
    applications.foldLeft(Code(Apply(Code(Slot(0)), Code(Slot(1)))))(
      (inner, application) =>
        val nested =
          Code(Thunk(inner, Vector(Hole.Bound(0)), Vector(Code(Slot(0)))))
        if application then Code(Apply(Code(Slot(1)), nested))
        else Code(Choice(Code(Slot(1)), nested))
    )

  property(
    "the facts of thunks nested thousands deep are computed with each level's counts",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) {
    for applications <- levels.forAll
    yield Result.diff(
      Code.facts(chain(applications)),
      CodeFacts(BitSet(0, 1), BitSet(0), BitSet(0, 1))
    )(_ == _)
  }
