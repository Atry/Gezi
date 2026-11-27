package gezi.jmh.pipeline

import java.nio.file.Files
import java.nio.file.Path
import java.util.concurrent.TimeUnit // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
import gezi.contest.entry.ArticleDestination
import gezi.contest.entry.Defaults
import gezi.contest.entry.Entry
import gezi.contest.entry.EntryData
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.ExtractorModules
import gezi.contest.entry.generic.GenericEntry
import gezi.contest.entry.generic.GenericEntryProvider
import gezi.directorysugar.DirectoryTree
import gezi.ffi.ReplyHandler
import gezi.frontend.NameSpelling
import gezi.hotspot.ExpansionSource
import gezi.hotspot.ForeignValue
import gezi.ir.Closed
import gezi.ir.NativeSpecializer
import gezi.jit.NativesProvider
import gezi.jupyter.kernel.JvmService
import gezi.jupyter.kernel.Notebook
import gezi.jupyter.kernel.NotebookCell
import gezi.jupyter.kernel.NotebookLocation
import gezi.jupyter.kernel.OutputKey
import gezi.programfamilies.FixedPointLines
import gezi.saturation.StopSignal
import org.openjdk.jmh.annotations.Benchmark
import org.openjdk.jmh.annotations.BenchmarkMode
import org.openjdk.jmh.annotations.Fork
import org.openjdk.jmh.annotations.Measurement
import org.openjdk.jmh.annotations.Mode
import org.openjdk.jmh.annotations.OutputTimeUnit
import org.openjdk.jmh.annotations.Scope
import org.openjdk.jmh.annotations.State
import org.openjdk.jmh.annotations.Warmup

/** The foreign method the benchmark's cells call: replies with its first
  * argument as many times as its second says.
  */
object NotebookCellApi:
  def echo(value: Byte, replies: Byte, handler: ReplyHandler): Unit =
    (0 until replies.toInt).foreach(_ =>
      handler.resumed(ForeignValue.Bits(8, value.toLong & 0xff))
    )
    handler.completed()

/** A notebook whose earlier cells have run and whose last has not: the entry as
  * the earlier cells left it, and the notebook with all of them.
  */
final case class NextNotebookCell[C <: NativeSpecializer & Singleton](
    entry: Entry[C],
    notebook: Notebook[C],
    key: OutputKey
):

  /** The last cell's FFI program run under a new version of the contents, as
    * the kernel runs a cell. The state is not changed, so each call measures
    * the same cell.
    */
  def answers: Vector[Closed[C]] =
    given C = entry.specializer
    entry
      .interacted(
        notebook.member(key),
        JvmService,
        ExpansionSource.fresh(),
        StopSignal.NeverStopped
      )
      .fold(throw IllegalStateException("the entry runs no FFI program"))(run =>
        if run.finished then run.answers
        else
          throw IllegalStateException("the cell's FFI program did not finish")
      )

/** The second cell of a notebook of two FFI cells that call one method, the
  * library imports of each read through the notebook's self, on the fixture
  * entry with its instance table's answers dropped at each cell, and on the
  * same entry with them verified across cells (`gezi.jit.InstanceReuse`) and
  * the cells in a file. Built once, outside the timed calls.
  */
@State(Scope.Benchmark)
class NotebookCellInputs:

  private val buildRoot: Path =
    FixedPointLines.buildRoot.toAbsolutePath.normalize

  private val fixture: Path =
    buildRoot.resolve("tests/moore_fixtures/entry_with_moore.lambdalattice")

  /** The fixture entry with its instance reuse switched off, written under the
    * build's `target`, in the tree the entry's imports read.
    */
  private lazy val fixtureWithinVersion: Path =
    val text = Files.readString(fixture)
    val directory = Files.createDirectories(
      buildRoot.resolve("target/notebook-cell-benchmark")
    )
    val written =
      Files.createTempFile(directory, "entry", DirectoryTree.fileExtension)
    written.toFile.deleteOnExit()
    Files.writeString(
      written,
      text
        .replace("λ _ verified_across_versions", "λ within_version _")
        .replace(
          "+ instance_reuse verified_across_versions",
          "+ instance_reuse within_version"
        )
    )

  private def byteText(value: Byte): String =
    val bits = (7 to 0 by -1)
      .map(bit =>
        if ((value >> bit) & 1) == 1 then "(λt e. t)" else "(λt e. e)"
      )
      .mkString(" ")
    s"(λtuple. tuple $bits)"

  private def cellText(index: Int): String =
    val root = NameSpelling.escaped(buildRoot.getFileName.toString)
    val library = s"omega (omega (omega $root \"corpora\") \"library\")"
    val symbols =
      "[\"gezi/jmh/pipeline/NotebookCellApi\", \"echo\", \"(BBLgezi/ffi/ReplyHandler;)V\"]"
    s"(λ\"io\" \"k$index\". (λtuple. tuple λmixin. mixin mixin) λomega. " +
      s"omega (omega ($library \"java_ffi\") \"moore\") λstate finish run call new decode _. " +
      s"omega (omega ($library \"prelude\") \"list\") λnil cons _ _ _. " +
      s"state (run (call (λk. k $symbols) (cons (decode ${byteText(5)}) (cons (decode ${byteText(1)}) nil)))) " +
      "λreply. state (finish reply) λignored. ignored)"

  private def prepared(
      entryFile: Path,
      cellsFile: Option[Path],
      earlierCells: Int
  ): NextNotebookCell[?] =
    val (data, afterEntry) =
      EntryData.at(buildRoot, entryFile, Defaults.entryDataState)
    val entry = GenericEntryProvider.initialized(
      data,
      ExecutorModules.registered(buildRoot),
      ExtractorModules.registered(buildRoot),
      NativesProvider.loaded,
      ArticleDestination.Discarded,
      afterEntry,
      Defaults.caches()
    )
    preparedOf(entry, cellsFile, earlierCells)

  /** The notebook's earlier cells run through the entry and the next cell
    * written, in the entry's configuration, which the method binds.
    */
  private def preparedOf[C <: NativeSpecializer & Singleton](
      entry: GenericEntry[C],
      cellsFile: Option[Path],
      earlierCells: Int
  ): NextNotebookCell[C] =
    given C = entry.specializer
    val location =
      NotebookLocation.of(buildRoot.resolve("notebook-cell-benchmark.ipynb"))
    def keyOf(cell: NotebookCell): OutputKey =
      cell.outputs.headOption.getOrElse(
        throw IllegalStateException(s"the cell ${cell.id} has no key")
      )
    val (afterEarlier, notebookOfEarlier) =
      (1 to earlierCells).foldLeft[(Entry[C], Notebook[C])](
        (
          entry,
          Notebook[C](
            location,
            DirectoryTree.rootOf[C](buildRoot),
            Vector.empty,
            cellsFile
          )
        )
      ) { case ((current, notebook), index) =>
        val cell = NotebookCell.read(s"cell $index", cellText(index), location)
        val withCell = notebook.added(cell)
        withCell.written()
        val run = current
          .interacted(
            withCell.member(keyOf(cell)),
            JvmService,
            ExpansionSource.fresh(),
            StopSignal.NeverStopped
          )
          .getOrElse(
            throw IllegalStateException("the entry runs no FFI program")
          )
        (run.entry, withCell)
      }
    val next = NotebookCell.read("next", cellText(earlierCells + 1), location)
    val all = notebookOfEarlier.added(next)
    all.written()
    NextNotebookCell(afterEarlier, all, keyOf(next))

  private def withCellsFile(earlierCells: Int): NextNotebookCell[?] =
    val directory = Files.createTempDirectory("notebook-cell-benchmark")
    directory.toFile.deleteOnExit()
    val cellsFile = directory.resolve(s"cells${DirectoryTree.fileExtension}")
    cellsFile.toFile.deleteOnExit()
    prepared(fixture, Some(cellsFile), earlierCells)

  /** The second cell with every answer dropped at a new cell. */
  lazy val dropped: NextNotebookCell[?] =
    prepared(fixtureWithinVersion, None, 1)

  /** The second cell with the answers verified across cells. */
  lazy val verified: NextNotebookCell[?] = withCellsFile(1)

  /** The ninth cell with the answers verified across cells. */
  lazy val ninth: NextNotebookCell[?] = withCellsFile(8)

/** One small example of what `gezi.jit.InstanceReuse` is for: the second FFI
  * cell of a notebook, whose imports the first cell already read. Its purpose
  * is the time and, under `-prof gc`, the allocation of the cell with the
  * answers of the first kept and verified, against the same cell with them
  * dropped; and of the ninth cell, against the second, what a cell pays for the
  * cells before it. A cell takes tenths of a second, so each is timed once per
  * iteration (`Mode.SingleShotTime`).
  */
@BenchmarkMode(
  Array(Mode.SingleShotTime)
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Fork(
  value = 1,
  jvmArgsAppend = Array("-Xmx2g", "-XX:+UseSerialGC")
) // the JMH protocol's exception (the user, 2026-10-31: "好的，用sbt-jmh，需要配合JMH协议时，必要时可以作为例外使用可变数据结构")
@Warmup(iterations = 10)
@Measurement(iterations = 10)
class NotebookCellReuseBenchmarks:

  /** The second cell with the first cell's answers dropped. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def secondCellDropped(input: NotebookCellInputs): Vector[Closed[?]] =
    input.dropped.answers

  /** The second cell with the first cell's answers verified. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def secondCellVerified(input: NotebookCellInputs): Vector[Closed[?]] =
    input.verified.answers

  /** The ninth cell with the eight cells' answers verified. */
  @Benchmark
  @OutputTimeUnit(TimeUnit.MILLISECONDS)
  def ninthCellVerified(input: NotebookCellInputs): Vector[Closed[?]] =
    input.ninth.answers
