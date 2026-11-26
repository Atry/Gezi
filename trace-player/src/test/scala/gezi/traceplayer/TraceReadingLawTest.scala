package gezi.traceplayer

import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.rewritetrace.TraceStart
import gezi.rewritetrace.TraceText

/** The laws of `TraceReading.played` on generated traces (`TermSequences.trace`),
  * run on Node.js: the texts the writers write of the start
  * (`TraceStart.written`) and of the trace read back to the start and,
  * after it, the term each command makes of the one before; and a text cut
  * short, the start's or the trace's, reads to an error, never to terms. Its purpose is to catch a reader,
  * a replay or a printer that the Scala.js build makes behave otherwise than
  * on the JVM (Scala.js's Java library, Parsley's Scala.js build, no
  * interning of instructions under Scala.js), and a page that would draw a
  * partial trace as if it ended there.
  */
class TraceReadingLawTest extends GeneratedProperties:

  property("the texts of a start and its trace read back to the start and the term each command makes") {
    for (start, trace) <- TermSequences.trace.forAllWithLog(written)
    yield
      val expected = trace.rounds.flatten.scanLeft(start)(TermSequences.step)
      TraceReading.played(TraceStart.written(start, None), TraceText.written(trace)) match
        case Left(unreadable) => Result.failure.log(unreadable.error)
        case Right(played)    => Result.diff(Vector.tabulate(played.size)(played.term), expected)(_ == _)
  }

  property("a text cut short reads to an error") {
    for (start, trace) <- TermSequences.trace.forAllWithLog(written)
    yield
      val startText = TraceStart.written(start, None)
      val traceText = TraceText.written(trace)
      Result.all(
        List(
          unread(TraceReading.played(startText, traceText + " ("), "a trace's text cut short"),
          unread(TraceReading.played(startText + " (", traceText), "a start's text cut short")
        )
      )
  }

  /** Success for a reading that gives an error, failure for one that gives
    * terms.
    */
  private def unread(reading: Either[Unreadable, Played], texts: String): Result =
    reading match
      case Left(_)  => Result.success
      case Right(_) => Result.failure.log(s"$texts read to terms")

  /** The texts of the start and of the trace, for the log. */
  private def written(startAndTrace: (Configured[NoFacts.type], gezi.rewritetrace.Trace)): String =
    val (start, trace) = startAndTrace
    s"${TraceStart.written(start, None)}\n${TraceText.written(trace)}"
