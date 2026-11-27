package gezi.contest.entry

import java.nio.file.Path
import gezi.frontend.DeBruijnTerm
import gezi.frontend.DeBruijnTermOf
import gezi.frontend.Defunctionalization
import gezi.weakhead.ScottADTChoices
import gezi.saturation.StopSignal
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall
import gezi.ir.{Closed, Configured, NativeSpecializer}

/** What a finished cell displays of its Output, in the configuration `C` of its entry. Three kinds:
  *
  *   - `Values`, the Output's Scott ADT values (`ScottADTChoices.of`): the closed terms `λc1 … ck. ci v1 … vn`, each
  *     field again one, that the Output is ⊑_O; the empty set, `top`, is the display of an Output with no Scott ADT
  *     value, whether or not it has a normal form;
  *   - `Remainder`, a closed term the entry evaluated no further, as the display of an Output whose reading was
  *     stopped by its budget, or of a judgment `N ∥ T` left undecided, which asserts nothing the Output does not;
  *   - `Mixed`, Scott ADT values beside a remainder, which the protocol allows on one line.
  *
  * The display as text is written by the pipe's formatter (`gezi.contest.runner.PipeLines.answerLine`): the values
  * as the Scott ADT reading, the remainder as any term of the configuration.
  */
enum OutputDisplay[C <: NativeSpecializer & Singleton]:

  /** The Output's Scott ADT values, which may be none. */
  case Values(choices: ScottADTChoices[C])

  /** A term of the configuration the Output was left as, a choice of whose members the judge reads: those that are
    * Scott ADT values assert membership, any other member asserts nothing.
    */
  case Remainder(term: Configured[C])

  /** Scott ADT values and a remainder together. */
  case Mixed(choices: ScottADTChoices[C], remainder: Configured[C])

/** The displays an entry makes from its own terms. */
object OutputDisplay:

  /** The display of an Output with no Scott ADT value. */
  def noScottADTValue[C <: NativeSpecializer & Singleton](using C): OutputDisplay[C] = Values(ScottADTChoices.empty[C])

  /** The display of a closed term an entry holds as a de Bruijn term, left as it is: its instruction
    * (`Defunctionalization.thunkInstruction`).
    */
  def remainder[C <: NativeSpecializer & Singleton](term: DeBruijnTermOf[Configured[C]])(using C): OutputDisplay[C] =
    Remainder(Defunctionalization.thunkInstruction[C](term))

/** What a cell's run comes to: the display of the cell's output, the phases of its run (`Phase`)
  * and the entry after it. An immutable value; the entry does no I/O.
  */
enum Interaction[C <: NativeSpecializer & Singleton]:
  case Finished(output: OutputDisplay[C], phases: Vector[Report], entry: Entry[C])

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
  def cell[K](output: DeBruijnTermOf[K]): DeBruijnTermOf[K] =
    DeBruijnTerm.Lambda(DeBruijnTerm.Lambda(DeBruijnTerm.Apply(DeBruijnTerm.Apply(DeBruijnTerm.Variable[K](0), DeBruijnTerm.Variable[K](1)), output)))

  /** The state after the cell, `cell state (λa. λb. a)` with the
    * projection's own redexes contracted.
    */
  def nextState[K](cell: DeBruijnTermOf[K], state: DeBruijnTermOf[K]): DeBruijnTermOf[K] = projected(cell, state, first)

  /** The cell's Output on the state, `cell state (λa. λb. b)` with the
    * projection's own redexes contracted.
    */
  def output[K](cell: DeBruijnTermOf[K], state: DeBruijnTermOf[K]): DeBruijnTermOf[K] = projected(cell, state, second)

  /** The cell's Output as the bare application `cell state (λa. λb. b)`,
    * nothing contracted: a display equal to the Output that asserts nothing,
    * since its head is a beta redex and so it is no normal form.
    */
  def unreducedOutput[C <: NativeSpecializer & Singleton](cell: DeBruijnTermOf[Configured[C]], state: DeBruijnTermOf[Configured[C]])(using C): OutputDisplay[C] =
    OutputDisplay.remainder[C](DeBruijnTerm.Apply(DeBruijnTerm.Apply(cell, state), second))

  /** `nextState` through the front end: the defunctionalized IR of the
    * state after the cell.
    */
  def nextStateInstruction[C <: NativeSpecializer & Singleton](cell: DeBruijnTermOf[Configured[C]], state: DeBruijnTermOf[Configured[C]])(using C): Configured[C] =
    Defunctionalization.thunkInstruction(nextState(cell, state))

  /** `output` through the front end: the defunctionalized IR of the cell's
    * Output, the instruction of `p` itself for a cell `λs.λk. k s p`.
    */
  def outputInstruction[C <: NativeSpecializer & Singleton](cell: DeBruijnTermOf[Configured[C]], state: DeBruijnTermOf[Configured[C]])(using C): Configured[C] =
    Defunctionalization.thunkInstruction(output(cell, state))

  /** `cell state projection` with the projection's own redexes contracted. */
  private def projected[K](cell: DeBruijnTermOf[K], state: DeBruijnTermOf[K], projection: DeBruijnTermOf[K]): DeBruijnTermOf[K] =
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
  private def substituted[K](body: DeBruijnTermOf[K], depth: Int, state: DeBruijnTermOf[K], projection: DeBruijnTermOf[K]): TailRec[DeBruijnTermOf[K]] =
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
final case class UnevaluatedCells[C <: NativeSpecializer & Singleton](specializer: C, state: DeBruijnTermOf[Configured[C]]) extends Entry[C]:

  def run(cell: DeBruijnTermOf[Configured[C]], source: gezi.hotspot.ExpansionSource, stop: StopSignal): Interaction[C] =
    given C = specializer
    Interaction.Finished(
      OutputDisplay.remainder[C](Cells.output(cell, state)),
      Vector.empty,
      copy(state = Cells.nextState(cell, state))
    )

  /** An entry that evaluates nothing runs no FFI program, so it is given no value to display. */
  def displayed(value: Closed[C], source: gezi.hotspot.ExpansionSource, stop: StopSignal): (Entry[C], OutputDisplay[C]) =
    throw IllegalStateException("an entry that evaluates nothing runs no FFI program, and is given no value to display")
