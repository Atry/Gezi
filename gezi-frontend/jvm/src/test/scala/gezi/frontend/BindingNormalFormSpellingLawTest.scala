package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm

/** The laws of the binding normal form's spelling half
  * (`gezi.ir.BindingNormalForm.spelled`) against the front end's own
  * spelling, run before the front end calls it (the law first, while the
  * old path still exists). The inputs
  * are the front end's instructions of generated closed terms
  * (`HoasGenerators.instruction`) and the evaluator's instructions
  * (`HoasGenerators.evaluatorInstruction`), whose spellings are not the
  * front end's.
  */
class BindingNormalFormSpellingLawTest extends GeneratedProperties:

  /** Catches a spelling that renumbers a body's slots, shares two closed
    * parts the front end keeps apart or keeps apart two it shares, or folds
    * a chain the front end does not: the front end's instruction is its own
    * spelling.
    */
  property("the front end's instruction is its own spelling") {
    for root <- HoasGenerators.instruction.forAll
    yield Result.diff(BindingNormalForm.spelled(root), root)(_ == _)
  }

  /** Catches a spelling of an instruction the front end did not make (a
    * thunk with filled holes, a code that reads closed parts the front end
    * would hoist) that differs from the front end's respelling of it
    * (`Respelling.respelled` with no name kept).
    */
  property("the spelling of the evaluator's instruction is the front end's respelling") {
    for
      size <- Gen.int(Range.linear(1, 8)).forAll
      root <- HoasGenerators.evaluatorInstruction(size).forAll
    yield Result.diff(BindingNormalForm.spelled(root), Respelling.respelled(root, Set.empty))(_ == _)
  }
