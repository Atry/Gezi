package gezi.frontend

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** Helpers for the conversions of the front end, which recurse over trees as
  * deep as the programs they convert: each is written over
  * `scala.util.control.TailCalls`, whose continuations are immutable values on
  * the heap, so that the depth of a term costs heap and not JVM stack.
  *
  * A sequence of steps binds each step to a fresh `tailcall` and makes the next
  * binding only when the previous step is done. Binding them all at once, by a
  * fold over the items, nests one continuation in the next, and `TailCalls`
  * then calls the nested continuations recursively: a body with 100,000 slots
  * overflowed the stack that way (2026-10-31).
  */
private[frontend] object Trampoline:

  /** The results of the step on each item, in order. */
  def traversed[Item, Result](items: Vector[Item])(
      step: Item => TailRec[Result]
  ): TailRec[Vector[Result]] =
    indexed(items)((item, _) => step(item))

  /** The results of the step on each item and its index, in order: what
    * `traversed` of the items zipped with their indices gives, without the
    * pairs, and with no state threaded, so no pair is made for each result
    * either (a JFR profile of the front end on 2026-11-20 put the zip at 8% of
    * `Defunctionalization.annotated`'s samples).
    */
  def indexed[Item, Result](items: Vector[Item])(
      step: (Item, Int) => TailRec[Result]
  ): TailRec[Vector[Result]] =
    def from(index: Int, results: Vector[Result]): TailRec[Vector[Result]] =
      if index >= items.size then done(results)
      else
        tailcall(step(items(index), index)).flatMap(result =>
          from(index + 1, results :+ result)
        )
    from(0, Vector.empty)

  /** The results of the step on each item, in order, a state threaded from one
    * item to the next.
    */
  def threaded[Item, Result, State](items: Vector[Item], state: State)(
      step: (Item, State) => TailRec[(Result, State)]
  ): TailRec[(Vector[Result], State)] =
    def from(
        index: Int,
        results: Vector[Result],
        current: State
    ): TailRec[(Vector[Result], State)] =
      if index >= items.size then done((results, current))
      else
        tailcall(step(items(index), current)).flatMap((result, next) =>
          from(index + 1, results :+ result, next)
        )
    from(0, Vector.empty, state)

  /** The results of the step on each item and its index, in order, a state
    * threaded from one item to the next.
    */
  def indexedThreaded[Item, Result, State](items: Vector[Item], state: State)(
      step: (Item, Int, State) => TailRec[(Result, State)]
  ): TailRec[(Vector[Result], State)] =
    def from(
        index: Int,
        results: Vector[Result],
        current: State
    ): TailRec[(Vector[Result], State)] =
      if index >= items.size then done((results, current))
      else
        tailcall(step(items(index), index, current)).flatMap((result, next) =>
          from(index + 1, results :+ result, next)
        )
    from(0, Vector.empty, state)

  /** The state after the step on each item in turn: `TailRecFolds.folded`. */
  def folded[Item, State](items: Vector[Item], start: State)(
      step: (State, Item) => TailRec[State]
  ): TailRec[State] = gezi.ir.TailRecFolds.folded(items, start)(step)
