package gezi.jupyter.kernel

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import hedgehog.core.SuccessCount
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Literal
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Configured
import gezi.ir.NativeSpecializer
import gezi.ir.NoFacts
import gezi.jit.BackendFacts
import gezi.jit.ClosureBackend
import gezi.jit.DispatchMode
import gezi.jit.InstanceRetention
import gezi.jit.InstanceReuse
import gezi.jit.Jit
import gezi.jit.JitConfiguration
import gezi.jit.PredicatePerCode
import gezi.jit.StorageEncoding
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.ReadingExecutor
import scala.jdk.StreamConverters.*
import scala.util.Using

private given cellsFileReuseLawTestNoFacts: NoFacts.type = NoFacts

/** The law of a notebook whose cells stand in a file, read by a JIT that keeps
  * its instance tables across cells (`gezi.jit.InstanceReuse`), as a state
  * machine: a generated sequence of cells, added or run again under their id,
  * each followed by a new version of the contents and a reading of every
  * member, whose normal forms must be those a tabled weak head reads with
  * nothing kept of the same notebook with its cells' terms in the mixin. Its
  * purpose is to catch a kept table that answers after a cell changed what it
  * read, directly or through a member of another cell, and a cells file that
  * means something other than the cells.
  */
class CellsFileReuseLawTest extends GeneratedProperties:

  private val limit: Long = 100000

  private val location: NotebookLocation = NotebookLocation(Vector("file", "n", "law"))

  private val memberKeys: Vector[String] = Vector("a", "b")

  /** Under the project's `target`, not the system's temporary directory,
    * which other runs fill.
    */
  private val files: Path = Files.createDirectories(Paths.get("target", "cells-file-reuse-law").toAbsolutePath.normalize)

  private lazy val tree: Configured[NoFacts.type] = DirectoryTree.rootOf(files)

  /** The encoding of no facts, the configuration the JIT reads the members in. */
  private lazy val encoding: StorageEncoding =
    BackendFacts(StandardLibraryIndex(NoFacts, Vector.empty, Vector.empty, Vector.empty, Vector.empty)).storageEncoding

  private lazy val configuration: JitConfiguration[encoding.type] = JitConfiguration[encoding.type](
    encoding,
    10000,
    PredicatePerCode,
    ClosureBackend,
    DispatchMode.NoDispatch,
    instanceTable = true,
    instanceRetention = InstanceRetention.NeverDropped,
    instanceReuse = InstanceReuse.VerifiedAcrossVersions,
    storageAccess = gezi.ir.StorageAccess.granted()
  )

  /** A fresh JIT's reading executor of the configuration. */
  private def jitExecutor: ReadingExecutor[encoding.type] =
    val jit = Jit(configuration)
    ReadingExecutor(Mode.Jit, jit.readingConfiguration, NoJitState)

  /** The reference reading's executor, with no facts. */
  private def referenceExecutor: ReadingExecutor[NoFacts.type] =
    ReadingExecutor(Mode.TablingWeakHead, gezi.weakhead.ReadingConfiguration.withoutFacts, NoJitState)

  /** A term read with no facts in the JIT's configuration (`NativeSpecializer.crossedAllFromNoFacts`). */
  private def crossed(term: Configured[NoFacts.type]): Configured[encoding.type] = encoding.crossedAllFromNoFacts(Vector(term))(term)

  /** The JIT's normal forms and the reference's, crossed into the JIT's configuration, alike in their order. */
  private def sameNormalForms(found: Vector[Configured[encoding.type]], expected: Vector[Configured[NoFacts.type]]): Boolean =
    val crossedExpected = expected.map(crossed).sorted(gezi.ir.ContentComparison.ordering)
    found.size == crossedExpected.size && found.zip(crossedExpected).forall((left, right) => Configured.same(left, right)(using encoding))

  /** One cell's content, under the id of the slot it is run in: a partial
    * function of a member's key to a closed normal form or to another
    * member, reached through the notebook's self, so that a change of one
    * cell reaches what another cell's member read.
    */
  private final case class Written(slot: Int, key: String, body: String):
    def cell: NotebookCell = NotebookCell.read(s"cell $slot", s"(λ\"$key\". ($body))", location)

  private val written: Gen[Written] =
    for
      slot <- Gen.int(Range.constant(0, 2))
      key <- Gen.element1(memberKeys(0), memberKeys(1))
      body <- Gen.choice1(
        HoasGenerators.normalForm.map(LambdalatticeText.text),
        Gen.element1(memberKeys(0), memberKeys(1)).map(other => s"law law \"$other\"")
      )
    yield Written(slot, key, body)

  /** The cells and the name of the directory that holds their files, a name
    * the text of the cells file could bind for something else: a directory's
    * self is a name that text reads.
    */
  private val writtenInDirectory: Gen[(List[Written], String)] =
    for
      cells <- written.list(Range.linear(2, 4))
      directoryName <- Gen.element1("level0", "level1", "level2", "level3", "directory", "m", "law")
    yield (cells, directoryName)

  private def member(notebook: Notebook, key: String): Configured[NoFacts.type] =
    notebook.member(OutputKey(Vector(Literal.text(key)), Vector(key)))

  /** The normal forms the executor reads of the term, in a fixed order, and
    * the executor after. Throws `IllegalStateException` for a reading that
    * does not finish.
    */
  private def read[C <: NativeSpecializer & Singleton](
      executor: ReadingExecutor[C],
      term: Configured[C],
      cache: Cache,
      source: ExpansionSource,
      stop: StopSignal
  ): (Vector[Configured[C]], ReadingExecutor[C]) =
    val (after, _, progress) = executor.executed(term, ExecutionDependencies(cache, source), Budget(limit, countedUnits = false, stop))
    if progress.suspension.nonEmpty then throw IllegalStateException(s"the reading of $term did not finish within $limit steps")
    (progress.found.sorted(gezi.ir.ContentComparison.ordering), after)

  /** One cell read and its reading by the JIT, so that the first test does
    * not pay the loading of these classes inside its deadline.
    */
  private def classesLoaded(stop: StopSignal): Vector[Configured[encoding.type]] =
    val notebook = Notebook(location, tree, Vector.empty).added(NotebookCell.read("loaded", "(λ\"a\". (λx. x))", location))
    read(
      jitExecutor,
      crossed(member(notebook, "a")),
      BaselineCaches.provider(),
      ExpansionSource.fresh(),
      stop
    )._1

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(stopped => classesLoaded(StopSignal.completedWith(stopped)))

  // Three inputs of two to four cells, each cell parsed from its file and every member read by both readers. With six
  // inputs the suite took 1.2 to 4.4 s on two loaded cores, its shared fixture included, and the test once passed its
  // 3 s deadline (2026-11-22, seed 310410672381263, which passed when run again alone).
  stoppableProperty(
    "after each cell, a JIT that kept its tables reads every member as a fresh reading of the cells does",
    _.copy(testLimit = SuccessCount(3))
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for drawn <- writtenInDirectory.forAll
    yield
      val (cells, directoryName) = drawn
      val parent = Files.createTempDirectory(files, "cells")
      val directory = Files.createDirectory(parent.resolve(directoryName))
      val file = directory.resolve(s"cells${DirectoryTree.fileExtension}")
      val cache = BaselineCaches.provider()
      try
        val start = (
          Notebook(location, tree, Vector.empty, Some(file)),
          Notebook(location, tree, Vector.empty),
          jitExecutor,
          Vector.empty[Result]
        )
        val (_, _, _, checks) = cells.foldLeft(start) { case ((filed, plain, kept, checked), next) =>
          val cell = next.cell
          val filedNow = filed.added(cell)
          val plainNow = plain.added(cell)
          filedNow.written()
          val source = ExpansionSource.fresh()
          val (after, results) = memberKeys.foldLeft((kept, checked)) { case ((executor, found), key) =>
            val (normalForms, executorAfter) = read(executor, crossed(member(filedNow, key)), cache, source, stop)
            val (expected, _) = read(
              referenceExecutor,
              member(plainNow, key),
              BaselineCaches.provider(),
              ExpansionSource.fresh(),
              stop
            )
            (executorAfter, found :+ Result.assert(sameNormalForms(normalForms, expected)).log(s"$key: $normalForms, the reference $expected"))
          }
          (filedNow, plainNow, after, results)
        }
        Result.all(checks.toList)
      finally
        Using.resource(Files.list(directory))(_.toScala(Vector)).foreach(Files.delete)
        Files.delete(directory)
        Files.delete(parent)
  }
