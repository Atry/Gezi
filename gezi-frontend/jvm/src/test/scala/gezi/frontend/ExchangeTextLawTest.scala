package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** The laws of the exchange format (`ExchangeText`) on generated closed
  * instructions of every construct, some holding a closed part several
  * times (towers of diamonds, whose tree is exponential in their height),
  * the bits of literals as arguments, the variable arguments partial
  * function of a literal and top beside it in one body, and some whose own
  * text begins with a binding of the printer's shape `(λt. t V) λm. BODY`:
  *
  *   - a line reads back as its instruction, the line of the instruction
  *     read is the same line, and it holds no tab and no newline;
  *   - a line whose number of the printer's bindings is changed is no line:
  *     one more than the text has, or one fewer, which leaves a binding of
  *     the printer uncontracted;
  *   - a line of normal forms reads back as its members in order.
  *
  * Their purpose is to catch a reader that contracts a binding the printer
  * did not write (the program's own import, the reason the line writes N)
  * or misses one it wrote, a reader whose contraction gives another
  * instruction than the readback's (two slots where the readback has one,
  * as for top written once as a name and once inside a literal), a printer or
  * a reader that drops, reorders or misreads a part (a choice's members), a
  * line that would split a field of the judge's points file or pipe, and a
  * set of normal forms whose members the choice's spine does not give back.
  */
class ExchangeTextLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private val instructions: Gen[Configured[NoFacts.type]] = SharingInstructions.instructions

  /** The text the printer writes for the instruction, the input's log. */
  private def printedText(instruction: Configured[NoFacts.type]): String = ReadableText.printedNameless(instruction).text

  property("a line reads back as its instruction, is the line written again, and holds no tab or newline", _.copy(testLimit = 20)) {
    instructions.forAllWithLog(printedText).map(instruction =>
      val written = ExchangeText.line(instruction)
      Result.all(
        List(
          Result.diff(ExchangeText.term[NoFacts.type](written).map(Configured.same(_, instruction)), Right(true))(_ == _),
          Result.assert(!written.exists(character => character == '\t' || character == '\n' || character == '\r'))
        )
      )
    )
  }

  property("a line whose number of the printer's bindings is changed is no line", _.copy(testLimit = 20)) {
    for
      instruction <- instructions.forAllWithLog(printedText)
      more <- Gen.boolean.forAll
    yield
      val written = ExchangeText.line(instruction)
      val count = ReadableText.printedNameless(instruction).bindings
      val changed = if more || count == 0 then count + 1 else count - 1
      val prefix = s"λstart. start (λk. k $count) "
      Result
        .assert(written.startsWith(prefix))
        .log(s"the line does not start with $prefix")
        .and(
          Result
            .assert(ExchangeText.term(s"λstart. start (λk. k $changed) ${written.drop(prefix.length)}").isLeft)
            .log(s"read with $changed bindings for $count")
        )
  }

  property("a line of normal forms reads back as its members in order") {
    for programs <- HoasGenerators.closedTerm.list(Range.linear(0, 4)).forAll
    yield
      val members = programs.toVector
        .map(program => Defunctionalization.thunkInstruction[NoFacts.type](program.deBruijnTerm(Map.empty)))
        .filter {
          case member =>
            member.layer match
              case gezi.ir.Choice(_, _) => false
              case _                    => true
        }
      Result.diff(
        ExchangeText
          .normalForms[NoFacts.type](ExchangeText.normalFormsLine(members))
          .map(found => found.size == members.size && found.lazyZip(members).forall(Configured.same(_, _))),
        Right(true)
      )(_ == _)
  }
