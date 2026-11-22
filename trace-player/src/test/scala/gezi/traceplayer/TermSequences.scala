package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Instruction
import gezi.rewritetrace.PositionSegment
import gezi.rewritetrace.Positions
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceCommand

/** Generated closed IR terms and generated traces over them, for the
  * player's tests on Node.js, where no strategy runs: a trace's commands are
  * `Native` commands, each putting a generated term at a position drawn
  * among the positions of the term the commands before it made, so that the
  * replay has something to compute and the page several steps to draw.
  */
object TermSequences:

  /** A generated closed term, read back through its text so that it is the
    * instruction the front end spells for it, as every term a trace writes
    * is (`TraceText.readBack`).
    */
  val term: Gen[Instruction] =
    HoasGenerators.closedTerm.map(generated => Defunctionalization.thunkInstruction(Lambdalattice.term(text(generated))))

  /** The lambdalattice text of a generated term. */
  def text(generated: gezi.frontend.Term): String = LambdalatticeText.text(generated)

  /** The text of a closed instruction, as a trace writes its terms. */
  def instructionText(instruction: Instruction): String =
    gezi.frontend.Lambdalattice.closedText(instruction)

  /** Every position of the term, the root first, in preorder. */
  def positions(instruction: Instruction): Vector[Vector[PositionSegment]] =
    if instruction.opaque then Vector(Vector.empty)
    else
      val layer = instruction.layered
      Vector.empty +: layer.children.zip(Positions.roles(layer)).flatMap((child, role) => positions(child).map(role +: _))

  /** A generated start and a trace from it of one or two rounds, each of
    * zero to three `Native` commands. The trace does not hold its start
    * (`Trace`), so the start is given beside it.
    */
  val trace: Gen[(Instruction, Trace)] = traceFrom(term)

  /** A trace as `trace` gives, from a start that refers to a generated
    * closed term twice, `λf. f t t`, so that the printer shares it.
    */
  val sharingTrace: Gen[(Instruction, Trace)] =
    traceFrom(
      HoasGenerators.closedTerm.map(generated =>
        Defunctionalization.thunkInstruction(
          Lambdalattice.term(text(gezi.frontend.Term.Abstraction(function => function(generated)(generated))))
        )
      )
    )

  /** A trace of one or two rounds from a start the generator gives. */
  private def traceFrom(starts: Gen[Instruction]): Gen[(Instruction, Trace)] =
    for
      start <- starts
      roundCount <- Gen.int(Range.linear(1, 2))
      rounds <- (1 to roundCount).foldLeft(Gen.constant((start, Vector.empty[Vector[TraceCommand]]))) { (sofar, _) =>
        sofar.flatMap((current, done) => round(current).map((after, commands) => (after, done :+ commands)))
      }
    yield (start, Trace(Vector.empty, Vector.empty, rounds._2))

  /** Zero to three `Native` commands from the term, with the term they make. */
  private def round(start: Instruction): Gen[(Instruction, Vector[TraceCommand])] =
    for
      count <- Gen.int(Range.linear(0, 3))
      made <- (1 to count).foldLeft(Gen.constant((start, Vector.empty[TraceCommand]))) { (sofar, _) =>
        sofar.flatMap((current, commands) => native(current).map(command => (step(current, command), commands :+ command)))
      }
    yield made

  /** A `Native` command at a drawn position of the term. */
  private def native(current: Instruction): Gen[TraceCommand] =
    val found = positions(current)
    for
      position <- Gen.element(found.head, found.tail.toList)
      value <- term
    yield TraceCommand.Native(position, value)

  /** The term a `Native` command makes of the term. */
  def step(current: Instruction, command: TraceCommand): Instruction = command match
    case TraceCommand.Native(position, value) => Positions.replaced(current, position, value)
    case other                                => throw IllegalArgumentException(s"the samples make Native commands only, not $other")
