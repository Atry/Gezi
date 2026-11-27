package gezi.weakhead

import gezi.ir.NoFacts

import hedgehog.Gen
import hedgehog.Size
import gezi.frontend.Term
import gezi.generatedinputs.DeBruijnHoas
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.generatedinputs.SeededSnapshots
import snapshot4s.generated.snapshotConfig

/** The heads the weak-head evaluator finds for generated closed terms, in both
  * modes, recorded as a seeded snapshot: the expected heads are as complex as
  * the evaluator, so there is no concise law. Its purpose is to show, as a diff
  * beside the inputs, any change of the heads found, of their order under
  * `weak_head`, of the set under `tabling(weak_head)`, or of which terms run
  * past the budget (the terms with no head, Ω among them, do untabled and
  * finish with no head tabled).
  */
class WeakHeadSnapshotTest
    extends gezi.generatedinputs.FailFastSuite
    with SeededSnapshots:

  given NoFacts.type = NoFacts

  /** A budget far above what the finishing terms of at most 50 nodes take and
    * far below what would make the snapshot slow to compute.
    */
  private val stepLimit = 10000L

  /** Closed terms with no library name: two in five of `closedTerm` at sizes
    * from 40 up (up to 20 nodes and more), two in five one of them applied to
    * another, so that most samples reduce before their head, and one in five
    * with no head.
    */
  private val terms: Gen[Term] =
    val closed = HoasGenerators.closedTerm.scale(size =>
      Size(math.min(Size.max, 40 + size.value))
    )
    Gen.frequency1(
      2 -> closed,
      2 -> (for function <- closed; argument <- closed
      yield function(argument)),
      1 -> HoasGenerators.headlessTerm
    )

  private def text(term: Term): String = LambdalatticeText.text(term)

  private def reading(mode: Mode, term: Term): String =
    val value = EvaluatorTesting.valueOf(term)
    EvaluatorTesting.headsWithin(mode, value, stepLimit) match
      case Bounded.Finished(heads) =>
        if heads.isEmpty then "no head"
        else
          heads
            .map(head => text(DeBruijnHoas.term(head)))
            .mkString("heads: ", " ; ", "")
      case Bounded.Exceeded            => s"past $stepLimit steps"
      case Bounded.Exhausted(resource) => s"out of $resource"

  test("the heads of generated terms under weak_head and tabling(weak_head)") {
    assertSeededSnapshot(terms, 20261031L, 40, "weak_head/generated_terms.txt")(
      text,
      identity[String]
    )(term =>
      s"weak_head: ${reading(Mode.WeakHead, term)}\ntabling(weak_head): ${reading(Mode.TablingWeakHead, term)}"
    )
  }
