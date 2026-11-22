package gezi.contest.runner

import java.nio.file.Path
import jdk.jfr.Configuration
import jdk.jfr.Recording

/** The flight recordings of a practice pass (the supervisor's option
  * `--flight-recordings`): one Java Flight Recorder recording a cell, with
  * the JDK's `profile` settings (method samples, garbage collections, JIT
  * compilations, allocations), written to `<directory>/<point>.jfr`, the
  * point's name with every character other than a letter, a digit, `_` and
  * `-` written `-`. A recording is started before the cell's
  * `PointStarted` and written after its answer line, so that the next
  * cell's time includes the writing: the times of a recorded pass are for
  * finding where time goes, not readings. A `Recording` is a handle on the
  * JVM's recorder, which the JDK changes in place; it is held by one cell's
  * run and closed when written.
  */
object FlightRecordings:

  /** The recording of the point's cell, started, to be written into the
    * directory.
    */
  def started(directory: Path, point: String): Recording =
    val recording = Recording(Configuration.getConfiguration("profile"))
    recording.setName(point)
    recording.setDestination(directory.resolve(fileName(point)))
    recording.start()
    recording

  /** The recording stopped, which writes it to its destination, and closed. */
  def written(recording: Recording): Unit =
    recording.stop()
    recording.close()

  /** The file of the point's recording. */
  def fileName(point: String): String =
    point.map(character => if character.isLetterOrDigit || character == '_' || character == '-' then character else '-') + ".jfr"
