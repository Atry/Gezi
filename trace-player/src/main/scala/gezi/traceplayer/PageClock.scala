package gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.LatestEvent
import org.scalajs.dom

import scala.scalajs.js

/** The player's clock, a small event source that dispatches a `frame`
  * event at each `requestAnimationFrame`, which LatestEvent listens to, and
  * the time a control reads when the reader
  * acts. Times are milliseconds since the Unix epoch, the unit of the hash's
  * `since` (`PlayState`), so that a reloaded page goes on playing where it
  * was.
  */
object PageClock:

  /** The type of the events the clock dispatches. */
  private val frameType: String = "frame"

  /** The time now: the page's time origin plus `performance.now()`. The
    * facades of scalajs-dom 2.8.1 have no `timeOrigin`, so it is read
    * dynamically.
    */
  def now(): Double = timeOrigin + dom.window.performance.now()

  private def timeOrigin: Double = js.Dynamic.global.performance.timeOrigin.asInstanceOf[Double]

  /** The time of each animation frame, from the page's clock: `None` before
    * the first frame. The clock is an event target on which, from this call
    * on, every `requestAnimationFrame` callback dispatches a `frame` event
    * whose detail is the frame's time; the binding is LatestEvent's latest
    * such event. These calls of the browser's API (the target made, the
    * events dispatched, the frames requested) are this function's and no
    * other's. The frames are requested whether or not anything watches the
    * binding; when nothing does, as while the player is paused, an event
    * reaches no listener.
    */
  def frames(): Binding[Option[Double]] =
    val clock = new dom.EventTarget()
    def tick(timestamp: Double): Unit =
      val frameTime = timeOrigin + timestamp
      val _ = clock.dispatchEvent(new dom.CustomEvent(frameType, new dom.CustomEventInit { detail = frameTime }))
      val _ = dom.window.requestAnimationFrame(next => tick(next))
    val _ = dom.window.requestAnimationFrame(first => tick(first))
    new LatestEvent[dom.CustomEvent](clock, frameType).map(_.map(event => event.detail.asInstanceOf[Double]))
