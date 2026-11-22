package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.entry.OutputDisplay
import gezi.contest.runner.PipeLines
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Instruction

/** The law that the judge reads and judges a display at the size of its
  * graph: an answer line whose display is `V40`, `V0` a Church numeral and
  * each `Vi` the application `V(i-1) V(i-1)` of the one before to itself, a
  * line of 40 bindings whose tree has 2^40 applications, is read
  * (`PipeLines.answerRead`) and judged (`Outcome.judged`) as no normal form
  * against a generated reference and candidate, within the default deadline
  * and allocating less than 256 MB on the test's thread. Its purpose is to
  * catch a reader or a judgment that builds the display's tree
  * (`Defunctionalization.instructionTerm`), which an untrusted entry could
  * make exhaust the judge's heap with a short line.
  * The bound on
  * allocation is far below any tree of the display, 2^40 nodes of at
  * least 16 bytes each.
  */
class SharedDisplayLawTest extends GeneratedProperties:

  private def numeral(count: Int): DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda((1 to count).foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)((body, _) =>
      DeBruijnTerm.Apply(DeBruijnTerm.Variable(1), body))))

  /** The counts of numerals that are βη normal forms (the numeral of 1 is
    * an η redex).
    */
  private val counts = Gen.element(0, List(2, 3, 4, 5, 6))

  private val height: Int = 40

  /** The bytes the current thread has allocated so far, from the JVM's
    * thread bean, or none where the JVM does not count them.
    */
  private def allocated: Option[Long] = java.lang.management.ManagementFactory.getThreadMXBean match
    case bean: com.sun.management.ThreadMXBean if bean.isThreadAllocatedMemorySupported => Some(bean.getCurrentThreadAllocatedBytes)
    case _                                                                             => None

  property("a display of 2^40 applications as 40 bindings is read and judged no normal form, at the size of its graph", _.copy(testLimit = 5)) {
    for
      base <- counts.forAll
      referenceCount <- counts.forAll
      member <- Gen.boolean.forAll
    yield
      val start = allocated
      val display = (1 to height).foldLeft(Defunctionalization.thunkInstruction(numeral(base)))((below, _) => Instruction.Apply(below, below))
      val line = PipeLines.answerLine("point", Vector.empty, OutputDisplay.Shown(display))
      val reference = numeral(referenceCount)
      val judgments = PipeLines.answerRead(line) match
        case PipeLines.AnswerRead.Answer(_, _, read) =>
          Vector(
            Outcome.judged(Question.Evaluation(Set(reference)), read),
            Outcome.judged(Question.Judgment(Defunctionalization.thunkInstruction(reference), member), read)
          )
        case _ => Vector.empty
      val spent = start.zip(allocated).map((before, after) => after - before)
      Result.all(
        List(
          Result.diff(judgments, Vector((Outcome.NoAnswer, Share(0, 2)), (Outcome.Unknown, Share(0, if member then 2 else 1))))(_ == _)
            .log(s"the line of ${line.length} characters"),
          Result.assert(spent.forall(_ < 256L * 1024 * 1024)).log(s"$spent bytes allocated")
        )
      )
  }
