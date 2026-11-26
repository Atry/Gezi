package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.LambdalatticeProblem
import gezi.frontend.SyntaxError
import gezi.ir.Code
import gezi.ir.Configured
import gezi.ir.Hole
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.NonEmptyHoles
import scala.jdk.StreamConverters.*

/** Malformed inputs with exactly one planted defect of a known kind, so that
  * a test of an error checks the reason and the place the defect predicts:
  * lambdalattice text with one unexpected character or one unbound name, and
  * a thunk with one slot out of range or one filling missing. Each starts
  * from a well-formed input of `HoasGenerators.closedTerm`.
  */
object PlantedDefects:

  /** A lambdalattice text and the problem its one defect must be reported
    * as.
    */
  final case class MalformedText(text: String, expected: LambdalatticeProblem)

  /** Characters that start no token: a semicolon, the set symbols that are
    * not the calculus's spellings (∪, ∩, ∅), a lone `|` (only `||` is a
    * spelling of ∥), the double vertical line U+2016, `%` (a comment is
    * CDN's, which `#` starts) and a capital letter. The text of a term has
    * no `|`, so an inserted one is never the half of a `||`.
    */
  private val unexpectedCharacters: Vector[Int] = Vector(';', 0x222a, 0x2229, 0x2205, '|', 0x2016, '%', '@')

  /** The text of a generated term with one character that starts no token
    * inserted at any position, reported as `Syntax(UnexpectedCharacter(c),
    * p)` with p the insertion's offset in code points: the tokenizer reads
    * the whole text before the parser, so the first such character is the
    * error, whatever the parse would have found.
    */
  def unexpectedCharacter: Gen[MalformedText] =
    for
      term <- HoasGenerators.closedTerm
      codePoints = LambdalatticeText.text(term).codePoints.toScala(Vector)
      position <- Gen.int(Range.constant(0, codePoints.size))
      character <- Gen.element(unexpectedCharacters.head, unexpectedCharacters.tail.toList)
    yield MalformedText(
      (codePoints.take(position) ++ (character +: codePoints.drop(position))).map(Character.toString(_)).mkString,
      LambdalatticeProblem.Syntax(SyntaxError.UnexpectedCharacter(character), position)
    )

  // TODO: undeclaredName and unboundName stood here. Their purpose: the text of a generated term that uses the
  // name `undeclared_name`, which the names given to the conversion do not hold, reported as
  // `UnboundName("undeclared_name")`. They named library terms by Term.define leaves of HoasGenerators.closedTerm
  // over library names, a free variable (blacklisted) and a table of library files deleted when the library became files reached by paths.
  // Their replacement generates lambdalattice text
  // with the free name directly. The deleted code:
  // git show 2908bffd5:lambda_jit/frontend/src/test/scala/lambdajit/generatedinputs/PlantedDefects.scala.

  /** The kind of a thunk's planted defect. */
  enum ThunkDefect:

    /** The code reads the slot one past its thunk's last, which reading the
      * thunk back reports as `SlotOutOfRange`.
      */
    case SlotOutOfRange

    /** The thunk lacks its last filling while a hole is bound to its last
      * slot, so that its fillings are fewer than its slots that are no
      * hole, which reading it back reports as `FillingsNotMatched`. Without
      * a hole at the last slot, a thunk short of its last filling is a
      * thunk of one slot fewer whose code reads past it, the defect
      * `SlotOutOfRange`; it is not planted under this kind.
      */
    case MissingFilling

  /** A closed instruction whose top thunk carries one planted defect, and
    * its kind: a generated abstraction through the front end
    * (`Defunctionalization.thunkInstruction`), its code applied to the slot
    * one past the last, or its last filling dropped when a hole is bound to
    * its last slot.
    */
  def malformedThunk: Gen[(Configured[NoFacts.type], ThunkDefect)] =
    val planted = for
      body <- HoasGenerators.closedTerm
      defect <- Gen.element1(ThunkDefect.SlotOutOfRange, ThunkDefect.MissingFilling)
    yield
      Defunctionalization.thunkInstruction[NoFacts.type](gezi.frontend.Term.λ(_ => body).deBruijnTerm(Map.empty))(using NoFacts).layer match
        case gezi.ir.Thunk(code, holes, fillings) =>
          defect match
            case ThunkDefect.SlotOutOfRange =>
              val slotCount = holes.count(_.isInstanceOf[Hole.Bound]) + fillings.size
              Some((NoFacts.thunk(Code.Apply(code, Code.Slot(slotCount)), plantedHoles(holes), fillings), defect))
            case ThunkDefect.MissingFilling =>
              val slotCount = holes.count(_.isInstanceOf[Hole.Bound]) + fillings.size
              Option.when(fillings.nonEmpty && holes.contains(Hole.Bound(slotCount - 1)))(
                (NoFacts.thunk(code, plantedHoles(holes), fillings.dropRight(1)), defect)
              )
        case other => throw IllegalStateException(s"an abstraction's instruction is no thunk: $other")
    Gen.fromSome(planted)

  /** The holes of a thunk the front end made, which has at least one. */
  private def plantedHoles(holes: Vector[Hole]): NonEmptyHoles =
    NonEmptyHoles.of(holes).getOrElse(throw IllegalStateException("an abstraction's thunk has no hole"))
