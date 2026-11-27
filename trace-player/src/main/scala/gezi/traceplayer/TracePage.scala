package gezi.traceplayer

import com.yang_bo.html.render
import gezi.rewritetrace.TracePageText
import org.scalajs.dom

/** The page of the trace player: the script reads the texts of the page's two
  * `<script type="application/x-lambdalattice">` elements, the start and the
  * trace (`TracePageText`), embedded in the HTML, replays the trace from the
  * start (`TraceReading.played`), and draws the player of its steps into the
  * page's container. When a text does not read, the page shows the reader's
  * error instead of the player.
  */
object TracePage:

  /** Reads the page's trace and renders the player, or the reader's error, into
    * the page's element of the id `TracePageText.containerIdentifier`, whose
    * content html.scala's `render` then owns. Throws `IllegalStateException`
    * when the page embeds no start or trace, or more than one of either, or has
    * no such element.
    */
  def main(arguments: Array[String]): Unit =
    def embedded(role: String): String =
      val found = dom.document.querySelectorAll(
        s"""script[type="${TracePageText.traceType}"][data-role="$role"]"""
      )
      Vector.tabulate(found.length)(found(_).textContent) match
        case Vector(only) => only
        case texts        =>
          throw IllegalStateException(
            s"the page embeds ${texts.size} scripts of type ${TracePageText.traceType} and role $role, not one"
          )
    val content = TraceReading.played(
      embedded(TracePageText.startRole),
      embedded(TracePageText.traceRole)
    ) match
      case Left(unreadable) =>
        PlayerView.problem(s"The page's text is no trace: ${unreadable.error}")
      case Right(played) => PlayerView.player(played)
    val container = Option(
      dom.document.getElementById(TracePageText.containerIdentifier)
    ).getOrElse(
      throw IllegalStateException(
        s"the page has no element of the id ${TracePageText.containerIdentifier}"
      )
    )
    render(container, content)
