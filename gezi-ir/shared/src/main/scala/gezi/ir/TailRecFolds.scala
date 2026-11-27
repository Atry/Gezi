package gezi.ir

import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** Folds over `scala.util.control.TailCalls`, whose continuations are immutable
  * values on the heap, so that the length of the items costs heap and not JVM
  * stack.
  *
  * A fold binds each step to a fresh `tailcall` only when the previous step is
  * done. The fold `items.foldLeft(done(start))((written, item) =>
  * written.flatMap(before => step(before, item)))` binds every step onto the
  * accumulated computation at once: `TailCalls`' `flatMap` on a `Cont` composes
  * its continuation, `Cont(c.a, x => c.f(x) flatMap f)`, so that fold nests one
  * continuation per item and running it recurses that deep on the JVM stack
  * (`ExchangeText.line` overflowed on a shared graph of 16,000 nodes that way).
  */
object TailRecFolds:

  /** The state after the step on each item in turn, each step given the state
    * the previous one left.
    */
  def folded[Item, State](items: Vector[Item], start: State)(
      step: (State, Item) => TailRec[State]
  ): TailRec[State] =
    def from(index: Int, current: State): TailRec[State] =
      if index >= items.size then done(current)
      else
        tailcall(step(current, items(index))).flatMap(next =>
          from(index + 1, next)
        )
    from(0, start)
