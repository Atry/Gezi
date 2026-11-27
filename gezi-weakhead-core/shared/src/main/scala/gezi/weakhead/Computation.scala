package gezi.weakhead

import gezi.saturation.StopSignal
import gezi.weakhead.Trampoline
import gezi.weakhead.Trampoline.done
import gezi.weakhead.Trampoline.tailcall

/** The result of a computation over a state: its value and the state after it,
  * or a stop, with the state at the stop. A stop is what a budget gives when it
  * runs out; it ends every computation it is sequenced with.
  */
enum Computed[State, Value]:

  /** The computation finished with the value; the state after it. */
  case Done(value: Value, state: State)

  /** The computation stopped; the state at the stop. */
  case Stopped(state: State)

/** A computation that threads a state, as an immutable value: a function from
  * the state before to the result (`Computed`), trampolined on `Trampoline`, so
  * that a computation as deep as the terms it walks costs heap and not JVM
  * stack. Sequencing short-circuits on a stop.
  *
  * @param run
  *   the computation from the state before
  */
final case class Computation[State, Value](
    run: State => Trampoline[Computed[State, Value]]
):

  /** The computation followed by the one its value chooses. */
  def flatMap[Next](
      continuation: Value => Computation[State, Next]
  ): Computation[State, Next] =
    Computation(state =>
      tailcall(run(state)).flatMap {
        case Computed.Done(value, after) =>
          tailcall(continuation(value).run(after))
        case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
      }
    )

  /** The computation with its value mapped. */
  def map[Next](mapping: Value => Next): Computation[State, Next] =
    flatMap(value => Computation.pure(mapping(value)))

  /** The result from the state, run to the end of the trampoline. */
  def result(state: State): Computed[State, Value] = run(state).result

  /** The result from the state, run to the end of the trampoline, or none as
    * soon as the trampoline reads a requested stop (`Trampoline.resultUnless`):
    * the computations still pending are dropped, so no state they would have
    * made is seen, and the caller, which knows the state it started from, says
    * what a cancel leaves. A stop the computation itself gives (a budget run
    * out) is still `Computed.Stopped`, with the state at the stop.
    */
  def resultUnless(
      state: State,
      stop: StopSignal
  ): Option[Computed[State, Value]] =
    run(state)
      .map[Option[Computed[State, Value]]](Some(_))
      .resultUnless(stop, None)

/** The constructions of computations. */
object Computation:

  /** The computation that gives the value and leaves the state. */
  def pure[State, Value](value: Value): Computation[State, Value] =
    Computation(state => done(Computed.Done(value, state)))

  /** The computation that reads the state. */
  def state[State]: Computation[State, State] =
    Computation(state => done(Computed.Done(state, state)))

  /** The computation that replaces the state. */
  def replaced[State](next: State): Computation[State, Unit] =
    Computation(_ => done(Computed.Done((), next)))

  /** The computation that changes the state by the function. */
  def modified[State](change: State => State): Computation[State, Unit] =
    Computation(state => done(Computed.Done((), change(state))))

  /** The computation that stops at the state it is given. */
  def stopped[State, Value]: Computation[State, Value] =
    Computation(state => done(Computed.Stopped(state)))

  /** The values of the step on each item, in order, each step run when the
    * previous one is done (never a fold that binds them all at once, whose
    * nested continuations the trampoline calls recursively).
    */
  def traversed[State, Item, Value](items: Vector[Item])(
      step: Item => Computation[State, Value]
  ): Computation[State, Vector[Value]] =
    folded(items, Vector.empty[Value])((values, item) =>
      step(item).map(values :+ _)
    )

  /** The items folded from the start by the step, each step run when the
    * previous one is done.
    */
  def folded[State, Item, Accumulated](items: Vector[Item], start: Accumulated)(
      step: (Accumulated, Item) => Computation[State, Accumulated]
  ): Computation[State, Accumulated] =
    def from(
        index: Int,
        accumulated: Accumulated
    ): Computation[State, Accumulated] =
      if index >= items.size then pure(accumulated)
      else
        Computation(state =>
          tailcall(step(accumulated, items(index)).run(state)).flatMap {
            case Computed.Done(next, after) =>
              tailcall(from(index + 1, next).run(after))
            case Computed.Stopped(stopped) => done(Computed.Stopped(stopped))
          }
        )
    from(0, start)
