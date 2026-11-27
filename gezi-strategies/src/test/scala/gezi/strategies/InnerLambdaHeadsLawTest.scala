package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Pattern
import gezi.saturation.HigherOrderMatching

/** The law that a metavariable a side applies is higher-order however deep the
  * lambda it is applied in (`HigherOrderMatching.higherOrderMetavariables`): a
  * thunk `λx0. … λxd. M xd`, M a filling of the outermost thunk passed down as
  * a filling of each inner one, has M among its higher-order metavariables for
  * every depth d from 1 (at depth 0 the thunk is the eta-shaped `λx. M x`,
  * which is read as M's closure and is no higher-order occurrence, by design).
  * Its purpose is to catch an occurrence search that does not read an inner
  * thunk's code through its fillings: such a metavariable was not found
  * higher-order, so its lemma matched only a target whose code equals the
  * side's, and a lemma whose function is applied inside a loop's case never
  * matched a loop that a let's β builds (2026-11-07, the hot ladder's inlined
  * site).
  */
class InnerLambdaHeadsLawTest extends GeneratedProperties:

  /** The code of a lambda of one binder, slot 0, whose slot 1 is M: at depth 0
    * `M x`, deeper an inner lambda of the same shape, M its filling.
    */
  private def code(depth: Int): Code =
    if depth == 0 then Code.Apply(Code.Slot(1), Code.Slot(0))
    else
      Code.Thunk(code(depth - 1), Vector(Hole.Bound(0)), Vector(Code.Slot(1)))

  property("aMetavariableAppliedInAnInnerLambdaIsHigherOrder") {
    for
      depth <- Gen.int(Range.linear(1, 5)).forAll
      index <- Gen.int(Range.linear(0, 9)).forAll
    yield
      val side = Pattern.Thunk(
        code(depth),
        Vector(Hole.Bound(0)),
        Vector(Pattern.Metavariable(index))
      )
      Result
        .assert(
          HigherOrderMatching.higherOrderMetavariables(side).contains(index)
        )
        .log(s"depth $depth")
  }
