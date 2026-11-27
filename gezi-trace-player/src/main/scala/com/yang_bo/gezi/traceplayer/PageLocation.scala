package com.yang_bo.gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.LatestEvent
import org.scalajs.dom

/** The player's state in the page's URL hash (`PlayState`): the position is in
  * the hash (`#step=42.5&speed=2`), written with `history.replaceState` on a
  * pause, a step or a change of speed, and read by LatestEvent from
  * `hashchange`.
  */
object PageLocation:

  /** The state the hash spells, as of the latest `hashchange` event of the
    * window (LatestEvent), read from `location.hash` when the binding is first
    * watched and at each such event: `Left` with the reason for a hash that
    * spells no state.
    */
  def states(rounds: TraceRounds): Binding[Either[String, PlayState]] =
    LatestEvent.hashchange(dom.window).map(_ => current(rounds))

  /** The state the hash spells now, in a trace of the rounds. */
  def current(rounds: TraceRounds): Either[String, PlayState] =
    PlayState.parsed(dom.window.location.hash, rounds)

  /** Writes the state into the hash. This is the one site of the player that
    * changes the browser's state: `history.replaceState` replaces the URL of
    * the current history entry (no entry is added per step or per change of
    * speed), and, since `replaceState` fires no `hashchange`, a `hashchange`
    * event is dispatched on the window, so that `states` reads the new hash as
    * it reads one the reader typed.
    */
  def write(state: PlayState, rounds: TraceRounds): Unit =
    dom.window.history.replaceState(null, "", state.hash(rounds))
    val _ = dom.window.dispatchEvent(new dom.Event("hashchange"))
