package gezi.contest.entry

import java.nio.file.Path
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.ExchangeText
import gezi.frontend.Lambdalattice
import gezi.ir.Instruction
import gezi.saturation.StopSignal
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** What a finished cell displays of its Output: that the Output has no
  * normal form, or a closed term, a choice of whose members the judge reads.
  * The first is no term
  * of the language, which has no term for the choice of nothing; on the pipe
  * it is the exchange format's own line
  * (`gezi.frontend.ExchangeText.noNormalFormLine`): the display reads "no
  * normal form, or a term", the bytes of the pipe unchanged.
  */
enum OutputDisplay:

  /** The Output is known to have no normal form. */
  case NoNormalForm

  /** The members of the term's choice, the Output's normal forms among
    * them, and any other member a remainder that asserts nothing. The term
    * is the instruction of the IR, as the exchange format reads it
    * (`ExchangeText.term`), at the size of its graph: the judge reads it
    * from an untrusted process, and a short line can stand for a tree too
    * large to build.
    */
  case Shown(term: Instruction)

  /** The display as text: the exchange format's line of no normal form, or
    * the term shown as the function writes it.
    */
  def written(termText: Instruction => String): String = this match
    case NoNormalForm => ExchangeText.noNormalFormLine
    case Shown(shown) => termText(shown)

/** The displays an entry makes from its own terms. */
object OutputDisplay:

  /** The display of a closed term an entry holds as a de Bruijn term: its
    * instruction (`Defunctionalization.thunkInstruction`).
    */
  def shown(term: DeBruijnTerm): OutputDisplay = Shown(Defunctionalization.thunkInstruction(term))

/** What a cell's run comes to: the display of the cell's output, the phases of its run (`Phase`)
  * and the entry after it. An immutable value; the entry does no I/O.
  */
enum Interaction:
  case Finished(output: OutputDisplay, phases: Vector[Report], entry: Entry)

/** Where an entry writes the OpenTheory articles of its compilation, given
  * once when it is loaded:
  * nowhere in the scored pass, a directory in the judge's article re-read.
  * An entry that writes articles writes the article of each
  * round of each schedule it runs to `round-<n>.art` in the directory, `n`
  * counting the rounds from 1 across the whole JVM
  * (`gezi.strategies.Schedule.articled`), never restarted at a cell.
  *
  * `WrittenWithTraces` is asked by a reader that wants the trace of every
  * point the entry extracts, for the trace player, not only of the points that get
  * an article: the entry writes the articles as under `Written` and, beside
  * them, `trace-<k>.lambdalattice` for every point with an extraction. The
  * judge's re-read asks `Written`, so that a point whose trace cannot yet be
  * written reads as it does with no trace.
  */
enum ArticleDestination:
  case Discarded
  case Written(directory: Path)
  case WrittenWithTraces(directory: Path)

/** The cell convention: a cell is a closed term `State → (State, Output)` whose pair is
  * a Scott pair `λk. k s o`, and the state starts as `λx.x`.
  *
  * The two projections contract the beta redexes the projection itself
  * creates and nothing else: a cell `λs.λk. B` applied to
  * the state σ and the projection π becomes `B[s := σ, k := π]`; when that is
  * π applied to exactly two arguments, it becomes the argument π selects.
  * Otherwise the term of the last step is returned. At most four beta steps
  * are taken, each substituting σ or π, so the projections always end, even
  * for a cell `λs.λk. Ω`. So the Output of `λs.λk. k s p` is `p` itself,
  * whatever the state, and a cell that does not touch the state leaves it
  * the same term.
  */
object Cells:

  /** The state before the first cell, `λx.x`. */
  val initialState: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0))

  /** The projection of a pair's first component, `λa. λb. a`. */
  private val first: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(1)))

  /** The projection of a pair's second component, `λa. λb. b`. */
  private val second: DeBruijnTerm = DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))

  /** The cell `λs.λk. k s output` of a closed Output, which leaves the
    * state as it is: the cell of a point.
    */
  def cell(output: DeBruijnTerm): DeBruijnTerm =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable(0), DeBruijnTerm.Variable(1)), output)))

  /** The state after the cell, `cell state (λa. λb. a)` with the
    * projection's own redexes contracted.
    */
  def nextState(cell: DeBruijnTerm, state: DeBruijnTerm): DeBruijnTerm = projected(cell, state, first)

  /** The cell's Output on the state, `cell state (λa. λb. b)` with the
    * projection's own redexes contracted.
    */
  def output(cell: DeBruijnTerm, state: DeBruijnTerm): DeBruijnTerm = projected(cell, state, second)

  /** The cell's Output as the bare application `cell state (λa. λb. b)`,
    * nothing contracted: a display equal to the Output that asserts nothing,
    * since its head is a beta redex and so it is no normal form.
    */
  def unreducedOutput(cell: DeBruijnTerm, state: DeBruijnTerm): OutputDisplay =
    OutputDisplay.shown(DeBruijnTerm.Apply(DeBruijnTerm.Apply(cell, state), second))

  /** `nextState` through the front end: the defunctionalized IR of the
    * state after the cell.
    */
  def nextStateInstruction(cell: DeBruijnTerm, state: DeBruijnTerm): Instruction =
    Defunctionalization.thunkInstruction(nextState(cell, state))

  /** `output` through the front end: the defunctionalized IR of the cell's
    * Output, the instruction of `p` itself for a cell `λs.λk. k s p`.
    */
  def outputInstruction(cell: DeBruijnTerm, state: DeBruijnTerm): Instruction =
    Defunctionalization.thunkInstruction(output(cell, state))

  /** The display of an Output whose answers, the closed βη normal forms N
    * with Output ⊑_O N, are known to be exactly these closed pure terms, the
    * most canonical display: for none
    * `OutputDisplay.NoNormalForm`, the normal form itself for one, else
    * their right-nested choice, the members in the order of their
    * lambdalattice text.
    */
  def displayed(normalForms: Set[DeBruijnTerm]): OutputDisplay =
    if normalForms.isEmpty then OutputDisplay.NoNormalForm
    else OutputDisplay.shown(DeBruijnTerm.nestedChoice(normalForms.toVector.sortBy(Lambdalattice.text(_, Map.empty))))

  /** `cell state projection` with the projection's own redexes contracted. */
  private def projected(cell: DeBruijnTerm, state: DeBruijnTerm, projection: DeBruijnTerm): DeBruijnTerm =
    cell match
      case DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(body)) =>
        substituted(body, 0, state, projection).result match
          case DeBruijnTerm.Apply(DeBruijnTerm.Apply(head, firstArgument), secondArgument) if head == projection =>
            if projection == first then firstArgument else secondArgument
          case contracted => contracted
      case _ => DeBruijnTerm.Apply(DeBruijnTerm.Apply(cell, state), projection)

  /** The body of `λs. λk. body` with the closed terms `state` for `s` and
    * `projection` for `k`, at `depth` binders inside the body. The cell is
    * closed, so no variable of the body points outside `s`. Trampolined:
    * a cell's body is as deep as the program it carries, thousands of levels
    * for a large workload, and one JVM frame per level overflowed the stack
    * (2026-11-02, on the
    * `repeated_library_edit_distances` points).
    */
  private def substituted(body: DeBruijnTerm, depth: Int, state: DeBruijnTerm, projection: DeBruijnTerm): TailRec[DeBruijnTerm] =
    body match
      case DeBruijnTerm.Variable(index) if index == depth     => done(projection)
      case DeBruijnTerm.Variable(index) if index == depth + 1 => done(state)
      case DeBruijnTerm.Variable(index) if index > depth + 1 =>
        throw IllegalArgumentException(s"a cell is a closed term; variable $index at depth $depth points outside it")
      case variable @ DeBruijnTerm.Variable(_) => done(variable)
      case DeBruijnTerm.Lambda(inner)          => tailcall(substituted(inner, depth + 1, state, projection)).map(DeBruijnTerm.Lambda(_))
      case DeBruijnTerm.Apply(function, argument) =>
        for
          substitutedFunction <- tailcall(substituted(function, depth, state, projection))
          substitutedArgument <- tailcall(substituted(argument, depth, state, projection))
        yield DeBruijnTerm.Apply(substitutedFunction, substitutedArgument)
      case constant @ DeBruijnTerm.Constant(_) => done(constant)
      case DeBruijnTerm.Free(name) =>
        throw IllegalArgumentException(s"a cell is a closed term; it holds the free name $name")
      case DeBruijnTerm.Choice(left, right) =>
        for
          substitutedLeft <- tailcall(substituted(left, depth, state, projection))
          substitutedRight <- tailcall(substituted(right, depth, state, projection))
        yield DeBruijnTerm.Choice(substitutedLeft, substitutedRight)
      case DeBruijnTerm.Parallel(left, right) =>
        for
          substitutedLeft <- tailcall(substituted(left, depth, state, projection))
          substitutedRight <- tailcall(substituted(right, depth, state, projection))
        yield DeBruijnTerm.Parallel(substitutedLeft, substitutedRight)

/** An entry that runs cells by the protocol's simplest display, the Output
  * not evaluated, and keeps the state as a term: a tool an entry may use for
  * the cells it does not evaluate, not a default of `Entry`.
  */
final case class UnevaluatedCells(state: DeBruijnTerm) extends Entry:

  def run(cell: DeBruijnTerm, source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction =
    Interaction.Finished(
      OutputDisplay.shown(Cells.output(cell, state)),
      Vector.empty,
      copy(state = Cells.nextState(cell, state))
    )
