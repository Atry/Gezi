package gezi.contest.runner

import java.io.BufferedReader
import java.io.FileDescriptor
import java.io.FileOutputStream
import java.io.InputStreamReader
import java.io.PrintStream
import java.nio.charset.StandardCharsets
import java.nio.file.Path
import java.nio.file.Paths
import java.util.ServiceLoader
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryProvider
import gezi.contest.entry.Interaction
import gezi.hotspot.Cache
import gezi.hotspot.CacheGuard
import gezi.hotspot.CacheNamespace
import gezi.hotspot.CacheProvider
import gezi.hotspot.ExpansionSource
import gezi.hotspot.LifecycleEvent
import gezi.ir.{NativeSpecializer, StorageAccess}
import gezi.saturation.StopSignal
import scala.annotation.tailrec
import scala.concurrent.Await
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.util.Try
import scala.jdk.CollectionConverters.*

/** The judge's side in a reader's JVM: it loads the reader, writes the line
  * `ready` on the pipe, then reads one point's line (`PipeLines`) at a time
  * from the standard input, builds the point's cell from the program's line
  * and, for a judgment, the candidate's (`PipeLines.cellRead`), and writes its
  * answer line, the entry one cell finished with running the next. Only the
  * runner reads the pipe: the entry is given the cell alone
  * (`gezi.contest.entry.Entry.run`), and no interface hands it a point's name,
  * its kind or its lines, as when the judge wrote the cell's line itself. The
  * pipe is the process's original standard output; `System.out` is pointed at
  * the standard error, so that what an entry prints cannot be read as an
  * answer. Nothing is caught: an exception, an `OutOfMemoryError` (the JVM runs
  * with `-XX:+ExitOnOutOfMemoryError`) or a stack overflow ends the JVM, which
  * the supervisor reads as stopped.
  *
  * The runner builds a cache provider, the framework's default
  * (`gezi.contest.entry.Defaults.caches`), and hands the reader, when it loads
  * it, the provider's `Cache` only, a view through which the reader cannot
  * reach the provider: the provider is outside the entry's boundary. The runner
  * itself hands the provider the lifecycle events: `PointStarted` and
  * `PointFinished` around each cell, both inside the cell's reading, of its
  * own; and each event of a lifecycle line the supervisor writes (the round's
  * and the family's), answered by the line `lifecycle_done` once the provider
  * has taken it. Each event handed to the provider is written to the standard
  * error as the line `lifecycle <event>`, which the supervisor keeps in the
  * JVM's file. It announces nothing else: a JVM the supervisor starts again
  * within a pass gives a fresh entry a fresh provider and hears no
  * `RoundStarted`.
  *
  * An entry's JVM runs `contestEntryRunner`, on the entry's classpath and this
  * module's, which hold neither the problem corpora nor the judge. The
  * reference readers' JVMs run the judge's `judgeReferenceRunner`, which serves
  * its reader with `served`.
  */
object EntryRunner:

  /** The one `EntryProvider` the loader's `META-INF/services` registers. Throws
    * `IllegalStateException` naming the implementations found when there is not
    * exactly one: the judge never picks one.
    */
  def provider(loader: ClassLoader): EntryProvider =
    ServiceLoader
      .load(classOf[EntryProvider], loader)
      .stream()
      .toList
      .asScala
      .toVector match
      case Vector(one) => one.get()
      case found       =>
        throw IllegalStateException(
          s"exactly one implementation of gezi.contest.entry.EntryProvider must be registered, found ${found.size}: " +
            found.map(_.`type`().getName).mkString(", ")
        )

  /** The reader `initial` gives of the `Cache` of a fresh cache provider,
    * served on the pipe: `System.out` pointed at the standard error, the reader
    * loaded, the ready line written, then every line read until the input ends.
    * With a directory of flight recordings, each cell's run is recorded into it
    * (`FlightRecordings`). Every cell is run under one expansion source, made
    * here: the files of the tree do not change while the judge runs
    * (`Entry.run`).
    */
  def served(initial: Cache => Entry[?], recordings: Option[Path]): Unit =
    val pipe = PrintStream(
      FileOutputStream(FileDescriptor.out),
      false,
      StandardCharsets.UTF_8
    )
    System.setOut(System.err)
    val provider = Defaults.caches()
    val entry = initial(EntryCache(provider))
    pipe.print("ready\n")
    pipe.flush()
    answeredAll(
      BufferedReader(InputStreamReader(System.in, StandardCharsets.UTF_8)),
      pipe,
      provider,
      ExpansionSource.fresh(),
      entry,
      recordings
    )

  /** The provider's `Cache` as an entry sees it: its `locked`, and no way to
    * the provider's `lifecycle`, not even by a cast.
    */
  private final class EntryCache(provider: CacheProvider) extends Cache:
    def locked[Key, Value, Result](namespace: CacheNamespace[Key, Value])(
        body: CacheGuard[Key, Value] => Result
    ): Result =
      provider.locked(namespace)(body)

  /** The event handed to the provider and written to the standard error as the
    * line `lifecycle <event>`.
    */
  private def announced(provider: CacheProvider, event: LifecycleEvent): Unit =
    provider.lifecycle(event)
    System.err.println(s"lifecycle $event")
    System.err.flush()

  /** The entry runs each cell read, in turn, under the expansion source, and
    * the provider takes each lifecycle event read, answered with
    * `lifecycle_done`, until the input ends; each answer line carries the
    * display and the phases the cell's run finished with
    * (`Interaction.Finished`).
    */
  def answeredAll(
      input: BufferedReader,
      pipe: PrintStream,
      provider: CacheProvider,
      source: ExpansionSource,
      entry: Entry[?],
      recordings: Option[Path]
  ): Unit =
    answeredFrom(
      Option(input.readLine()),
      input,
      pipe,
      provider,
      source,
      entry,
      recordings
    )

  /** `answeredAll` from the line already read. From before a cell line's term
    * is parsed until the cell's call returns, the next line is read on a thread
    * of its own (`nextLine`): the supervisor writes nothing there but the
    * cancel line ([[PipeLines.cancelLine]]), and the call's stop signal asks
    * for a stop once that line has arrived. After the answer is written, the
    * same line is the next one: a cancel that came after the answer is dropped.
    * A cancel read between cells is dropped likewise. A cell's flight
    * recording, when there is one, is written after its answer line, so that
    * writing it is not counted in the cell's time.
    */
  @tailrec
  private def answeredFrom(
      read: Option[String],
      input: BufferedReader,
      pipe: PrintStream,
      provider: CacheProvider,
      source: ExpansionSource,
      entry: Entry[?],
      recordings: Option[Path]
  ): Unit =
    read match
      case None       => ()
      case Some(line) =>
        // A cell line's next line is read from before the cell line's term is
        // parsed, so that a cancel that comes while a large cell is still
        // being parsed reaches the call's stop.
        val readAhead = Option.when(PipeLines.isCellLine(line))(nextLine(input))
        // The entry's configuration is a type the loop does not name: each line is handled by a method generic in it,
        // which opens the entry by capture conversion.
        val (next, following) = handled(
          entry,
          line,
          readAhead,
          input,
          pipe,
          provider,
          source,
          recordings
        )
        answeredFrom(following, input, pipe, provider, source, next, recordings)

  /** The capability to read a storage's view, which the runner needs to read
    * the terms of the pipe's lines in the entry's configuration and to write
    * the entry's display: the adapter's own, granted here.
    */
  private val storageAccess: StorageAccess = StorageAccess.granted()

  /** One line handled for an entry of the configuration `C`: the terms of the
    * line are read by the entry's native specializer (`Entry.specializer`), a
    * cell is run by the entry, a lifecycle event is handed to the provider. The
    * entry after it, and the line to handle next.
    */
  private def handled[C <: NativeSpecializer & Singleton](
      entry: Entry[C],
      line: String,
      readAhead: Option[Future[Option[String]]],
      input: BufferedReader,
      pipe: PrintStream,
      provider: CacheProvider,
      source: ExpansionSource,
      recordings: Option[Path]
  ): (Entry[C], Option[String]) =
    given C = entry.specializer
    given StorageAccess = storageAccess
    PipeLines.receivedRead[C](line) match
      case PipeLines.Received.Cancel =>
        (entry, Option(input.readLine()))
      case PipeLines.Received.Lifecycle(event) =>
        announced(provider, event)
        pipe.print(PipeLines.lifecycleDone + "\n")
        pipe.flush()
        (entry, Option(input.readLine()))
      case PipeLines.Received.Cell(name, cell) =>
        val recording = recordings.map(FlightRecordings.started(_, name))
        announced(provider, LifecycleEvent.PointStarted)
        val following =
          readAhead.getOrElse(
            throw AssertionError(
              s"the cell line of $name was not recognized as one before it was parsed"
            )
          )
        entry.run(cell, source, CancelRead(following)) match
          case Interaction.Finished(display, phases, next) =>
            announced(provider, LifecycleEvent.PointFinished)
            pipe.print(PipeLines.answerLine(name, phases, display) + "\n")
            pipe.flush()
            recording.foreach(FlightRecordings.written)
            (next, Await.result(following, Duration.Inf))

  /** The next line of the input, read on a daemon thread of its own, so that
    * the main thread can run a call meanwhile. The reader is used by one thread
    * at a time: the main thread reads again only after this future has
    * completed.
    */
  private def nextLine(input: BufferedReader): Future[Option[String]] =
    val line = Promise[Option[String]]()
    Thread.ofPlatform().daemon(true).start { () =>
      line.complete(Try(Option(input.readLine())))
      ()
    }
    line.future

  /** The stop signal of a call: a stop is requested once the line read
    * meanwhile is the cancel line. The future is written once, so the signal is
    * read without any state of its own.
    */
  private final case class CancelRead(following: Future[Option[String]])
      extends StopSignal:
    def stopRequested: Boolean =
      following.value.exists(_.toOption.flatten.contains(PipeLines.cancelLine))

/** The main of an entry's JVM: the registered provider's entry of the
  * directory, `gezi/contest-entries-<name>/`, served on the pipe. The execution
  * of programs is `denied`, the execution filter installed before the entry is
  * loaded (`ExecutionFilter`, the supervisor's sandbox), or `allowed` (the
  * supervisor's `--sandbox none`). The articles are `discarded` (the scored
  * pass), written into the directory given (`ArticleDestination.Written`, the
  * judge's article re-read), or, given as `traces:` and the directory, written
  * there with the trace of every point the entry extracts
  * (`ArticleDestination.WrittenWithTraces`). The flight recordings are `none`
  * (every scored pass) or written into the directory given, one a cell
  * (`FlightRecordings`, the supervisor's `--flight-recordings`). Throws
  * `IllegalArgumentException` for another execution value.
  */
@main def contestEntryRunner(
    entryDirectory: String,
    execution: String,
    articles: String,
    recordings: String
): Unit =
  execution match
    case "denied"  => ExecutionFilter.installed()
    case "allowed" => ()
    case other     =>
      throw IllegalArgumentException(
        s"the execution of programs is denied or allowed, not $other"
      )
  val destination = articles match
    case "discarded"                            => ArticleDestination.Discarded
    case traced if traced.startsWith("traces:") =>
      ArticleDestination.WrittenWithTraces(
        Paths.get(traced.stripPrefix("traces:"))
      )
    case directory => ArticleDestination.Written(Paths.get(directory))
  EntryRunner.served(
    cache =>
      EntryRunner
        .provider(EntryRunner.getClass.getClassLoader)
        .initial(Paths.get(entryDirectory), cache, destination),
    Option.when(recordings != "none")(Paths.get(recordings))
  )
