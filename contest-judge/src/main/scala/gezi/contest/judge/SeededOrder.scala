package gezi.contest.judge

import scala.annotation.tailrec

/** The order the seed draws, a pure function of the seed: SplitMix64 as a
  * function from a state to the next state and an output, and the
  * Fisher–Yates shuffle over an immutable `Vector`, the state folded through
  * the draws.
  *
  * SplitMix64 (Steele, Lea and Flood, "Fast splittable pseudorandom number
  * generators", OOPSLA 2014): the state advances by the odd constant
  * 0x9e3779b97f4a7c15; the output is the new state mixed by two
  * xor-shift-multiply rounds and a final xor-shift (the constants of the
  * paper's `mix64`).
  *
  * The shuffle: for a position from the last down to the second, draw an
  * output, take its unsigned remainder by the number of positions up to and
  * including this one, and exchange the elements at the two positions. The
  * remainder's slight bias toward small values (at most one part in 2^64 / n)
  * does not matter for an order.
  */
object SeededOrder:

  /** The next state and the output of the state. */
  def next(state: Long): (Long, Long) =
    val advanced = state + 0x9e3779b97f4a7c15L
    val first = (advanced ^ (advanced >>> 30)) * 0xbf58476d1ce4e5b9L
    val second = (first ^ (first >>> 27)) * 0x94d049bb133111ebL
    (advanced, second ^ (second >>> 31))

  /** The elements shuffled from the state, and the state after. */
  def shuffled[Element](elements: Vector[Element], state: Long): (Vector[Element], Long) =
    shuffledFrom(elements, elements.size - 1, state)

  @tailrec
  private def shuffledFrom[Element](elements: Vector[Element], position: Int, state: Long): (Vector[Element], Long) =
    if position < 1 then (elements, state)
    else
      val (after, output) = next(state)
      val chosen = java.lang.Long.remainderUnsigned(output, position + 1L).toInt
      val exchanged = elements.updated(position, elements(chosen)).updated(chosen, elements(position))
      shuffledFrom(exchanged, position - 1, after)
