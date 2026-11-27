package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.io.ByteArrayInputStream
import java.io.InputStream
import java.io.OutputStream
import java.nio.charset.StandardCharsets
import gezi.generatedinputs.GeneratedProperties
import scala.annotation.tailrec

/** The law of the supervisor's line reader: lines a JVM writes in one chunk are
  * read back one by one, in order, with no wait on the pipe. Its purpose is to
  * catch a reader that keeps the lines after the first of a chunk in `pending`
  * and polls the pipe for the next line, which it then never sees: the defect
  * met on a published points file, where `lifecycle_done` and a family's first
  * answer came in one chunk and the point read stopped at the family's budget.
  */
class PendingLinesLawTest extends GeneratedProperties:

  /** A process that never ends and writes nothing of its own. */
  private object Running extends Process:
    def getOutputStream: OutputStream = OutputStream.nullOutputStream()
    def getInputStream: InputStream = InputStream.nullInputStream()
    def getErrorStream: InputStream = InputStream.nullInputStream()
    def waitFor(): Int = throw UnsupportedOperationException(
      "the process never ends"
    )
    def exitValue(): Int = throw IllegalThreadStateException(
      "the process is running"
    )
    def destroy(): Unit = ()

  /** A line of ASCII, Latin-1 and CJK characters, so that the UTF-8 decoding of
    * a line split from a chunk is checked too.
    */
  private val line: Gen[String] =
    Gen.string(
      Gen.choice1(Gen.alphaNum, Gen.char('À', 'ÿ'), Gen.char('一', '龥')),
      Range.linear(0, 12)
    )

  /** The lines read from the session until the reader reports anything but a
    * line, the deadline having passed already.
    */
  @tailrec
  private def linesRead(
      session: Session,
      read: Vector[String]
  ): Vector[String] =
    Supervisor.awaitedLine(session, System.nanoTime) match
      case Awaited.Line(next, after)           => linesRead(after, read :+ next)
      case Awaited.Ended | Awaited.TimedOut(_) => read

  property("lines written in one chunk are read back in order without a wait") {
    for lines <- line.list(Range.linear(1, 6)).forAll
    yield
      val chunk = lines.map(_ + "\n").mkString.getBytes(StandardCharsets.UTF_8)
      val session = Session(
        Running,
        ByteArrayInputStream(chunk),
        OutputStream.nullOutputStream(),
        ""
      )
      Result.diff(linesRead(session, Vector.empty), lines.toVector)(_ == _)
  }
