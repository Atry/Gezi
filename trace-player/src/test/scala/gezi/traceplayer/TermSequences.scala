package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.rewritetrace.PositionSegment
import gezi.rewritetrace.Positions
import gezi.rewritetrace.Trace
import gezi.rewritetrace.TraceCommand
import gezi.ir.{Configured, NativeSpecializer}

private given termSequencesNoFacts: NoFacts.type = NoFacts

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
  val term: Gen[Configured[NoFacts.type]] =
    HoasGenerators.closedTerm.map(generated => Defunctionalization.thunkInstruction(Lambdalattice.term(text(generated)))(using gezi.ir.NoFacts))

  /** The lambdalattice text of a generated term. */
  def text(generated: gezi.frontend.Term): String = LambdalatticeText.text(generated)

  /** The text of a closed instruction, as a trace writes its terms. */
  def instructionText[C <: NativeSpecializer & Singleton](instruction: Configured[C])(using C): String =
    gezi.frontend.Lambdalattice.closedText(instruction)

  /** Every position of the term, the root first, in preorder. */
  def positions[C <: NativeSpecializer & Singleton](instruction: Configured[C])(using C): Vector[Vector[PositionSegment]] =
    if instruction.opaque then Vector(Vector.empty)
    else
      val layer = instruction.layered
      Vector.empty +: layer.children.zip(Positions.roles(layer)).flatMap((child, role) => positions(child).map(role +: _))

  /** A generated start and a trace from it of one or two rounds, each of
    * zero to three `Native` commands. The trace does not hold its start
    * (`Trace`), so the start is given beside it.
    */
  val trace: Gen[(Configured[NoFacts.type], Trace[NoFacts.type])] = traceFrom(term)

  /** A trace as `trace` gives, from a start that refers to a generated
    * closed instruction t twice as a child of two layers, `(x t) t`, so that
    * the printer binds t as a shared instruction (ReadableText, SHARING: a
    * closed instruction the term refers to more than once; a subterm repeated
    * inside one code, as in the spelling of `λf. f t t`, is not shared). The
    * instruction t is an application `u (v w)`, so that it is neither a bit
    * of a literal nor an application of one to a bit, which the printer
    * never shares (`ReadableText.literalPart`), nor opaque, nor a level of a
    * variable arguments partial function, whatever u, v and w are.
    */
  val sharingTrace: Gen[(Configured[NoFacts.type], Trace[NoFacts.type])] =
    traceFrom(
      for
        function <- term
        head <- term
        argumentFunction <- term
        argumentArgument <- term
      yield
        val shared = NoFacts.application(head, NoFacts.application(argumentFunction, argumentArgument))
        NoFacts.application(NoFacts.application(function, shared), shared)
    )

  /** A trace of one or two rounds from a start the generator gives. */
  private def traceFrom[C <: NativeSpecializer & Singleton](starts: Gen[Configured[C]])(using C): Gen[(Configured[C], Trace[C])] =
    for
      start <- starts
      roundCount <- Gen.int(Range.linear(1, 2))
      rounds <- (1 to roundCount).foldLeft(Gen.constant((start, Vector.empty[Vector[TraceCommand[C]]]))) { (sofar, _) =>
        sofar.flatMap((current, done) => round(current).map((after, commands) => (after, done :+ commands)))
      }
    yield (start, Trace(Vector.empty, Vector.empty, rounds._2))

  /** Zero to three `Native` commands from the term, with the term they make. */
  private def round[C <: NativeSpecializer & Singleton](start: Configured[C])(using C): Gen[(Configured[C], Vector[TraceCommand[C]])] =
    for
      count <- Gen.int(Range.linear(0, 3))
      made <- (1 to count).foldLeft(Gen.constant((start, Vector.empty[TraceCommand[C]]))) { (sofar, _) =>
        sofar.flatMap((current, commands) => native(current).map(command => (step(current, command), commands :+ command)))
      }
    yield made

  /** A `Native` command at a drawn position of the term. */
  private def native[C <: NativeSpecializer & Singleton](current: Configured[C])(using C): Gen[TraceCommand[C]] =
    val found = positions(current)
    for
      position <- Gen.element(found.head, found.tail.toList)
      value <- term
    yield TraceCommand.Native(position, value)

  /** The term a `Native` command makes of the term. */
  def step[C <: NativeSpecializer & Singleton](current: Configured[C], command: TraceCommand[C])(using C): Configured[C] = command match
    case TraceCommand.Native(position, value) => Positions.replaced(current, position, value)
    case other                                => throw IllegalArgumentException(s"the samples make Native commands only, not $other")
