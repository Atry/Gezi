package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Files
import java.nio.file.Path
import gezi.directorysugar.DirectoryTree
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.Budget
import gezi.hotspot.Cache
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ExpansionSource
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Configured
import gezi.saturation.StopSignal
import gezi.weakhead.ApplicationReading
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.ReadingExecutor
import gezi.weakhead.ReadingSuspension
import gezi.weakhead.TableRetention

/** The law of the expansion source (`gezi.hotspot.ExecutionDependencies.source`),
  * as a state machine: a
  * generated sequence of writes of a file, each followed by a new source, as
  * the Jupyter kernel gives one for each cell, and of readings of the file's
  * first member through the file's URI node, folded over an executor that
  * keeps what it reads from one call to the next. Each reading reads the
  * normal forms of the member the file holds now, read alone by an executor
  * that keeps nothing. Its purpose is to catch an executor that answers
  * under a new source from what it read of an older content: tables it
  * keeps (`TableRetention.KeptAll`), the JIT's instance table
  * (`JitRunState.instanceTables`), that table's answers kept across versions
  * and taken without their reads holding (`InstanceReuse`), or complete
  * tables kept in the cache service (`TableSharing.Shared`) under a namespace
  * that leaves the source out. The file's member is a Church numeral of 0 to 3, so two writes
  * usually differ, and every reading reads the same term, which an earlier
  * reading of the same executor kept. The term is a closure applied to the
  * file's URI node, which applies the node to as many arguments as the
  * file's scope binds and then to the selector of the first member: the node
  * is a filling of the closure's instance, which the JIT tables with the
  * node unexpanded in its key, and the reading lists no directory (a tree
  * read from the file system's root lists each directory on the path, 0.1 s
  * a reading under `target`, measured 2026-11-20 by a probe not committed,
  * against about 0.02 s for the file alone).
  */
class ExpansionSourceLawTest extends GeneratedProperties:

  private val limit: Long = 2000000

  /** Every reader of the law reads in the configuration of no facts' encoding, the JIT's included. */
  private val encoding = JitTesting.noFactsEncoding

  private given encoding.type = encoding

  private val plainConfiguration: gezi.weakhead.ReadingConfiguration[encoding.type] =
    gezi.weakhead.ReadingConfiguration[encoding.type](encoding, gezi.ir.StorageAccess.granted())

  private enum Operation:
    case Written(numeral: Int)
    case Read

  private val operations: Gen[List[Operation]] =
    Gen.frequency1(
      2 -> Gen.int(Range.constant(0, 3)).map(Operation.Written(_)),
      3 -> Gen.constant(Operation.Read)
    ).list(Range.constant(4, 12))

  /** The file's text: a tuple of one member, the numeral. */
  private def text(numeral: Int): String =
    s"λtuple. tuple (λf x. ${"f (" * numeral}x${")" * numeral})\n"

  /** The selector of a tuple's first member. */
  private val first: Configured[encoding.type] = Defunctionalization.thunkInstruction[encoding.type](Lambdalattice.term("λa. a"))

  /** Where the files are written: under the project's `target`, not the
    * system's temporary directory, which other runs fill.
    */
  private val files: Path = Files.createDirectories(java.nio.file.Paths.get("target", "expansion-source-law").toAbsolutePath.normalize)

  /** The normal forms of the numeral's member read alone, under the stop. */
  private def expected(numeral: Int, stop: StopSignal): Vector[Configured[encoding.type]] =
    read(
      ReadingExecutor(Mode.TablingWeakHead, plainConfiguration, NoJitState),
      encoding.application(Defunctionalization.thunkInstruction[encoding.type](Lambdalattice.term(text(numeral))), first),
      ExecutionDependencies(BaselineCaches.provider(), ExpansionSource.fresh()),
      stop
    )._1

  /** An executor under test, with the cache service it reads in, kept for
    * every reading of one check.
    */
  private final case class Kept(executor: Executor[encoding.type, ReadingSuspension[encoding.type]], cache: Cache)

  private val jitConfiguration = JitConfiguration[encoding.type](
    encoding,
    10000,
    PredicatePerCode,
    ClosureBackend,
    DispatchMode.NoDispatch,
    instanceTable = true,
    instanceRetention = InstanceRetention.NeverDropped,
    storageAccess = gezi.ir.StorageAccess.granted()
  )

  private val verifiedJitConfiguration = JitConfiguration[encoding.type](
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

  /** What each executor keeps between calls: the tabled weak head's tables
    * in the executor, the JIT's instance table in its state, and the tabled
    * weak head's complete tables in the cache service, by a new executor
    * for each reading.
    */
  private val kinds: Vector[(String, () => Kept, Kept => Kept)] =
    Vector(
      (
        "tables kept by the executor",
        () =>
          Kept(
            ReadingExecutor(Mode.TablingWeakHead, plainConfiguration, NoJitState, None, None, ApplicationReading.ByLayer, TableRetention.KeptAll),
            BaselineCaches.provider()
          ),
        identity
      ),
      ("the JIT's instance table", () => Kept(JitExecutor.of(Jit(jitConfiguration)), BaselineCaches.provider()), identity),
      (
        "the JIT's instance table verified across versions",
        () => Kept(JitExecutor.of(Jit(verifiedJitConfiguration)), BaselineCaches.provider()),
        identity
      ),
      (
        "complete tables shared in the cache service",
        () => Kept(ReadingExecutor(Mode.TablingWeakHead, plainConfiguration, NoJitState, Some(Retention.Strong)), BaselineCaches.provider()),
        kept => kept.copy(executor = ReadingExecutor(Mode.TablingWeakHead, plainConfiguration, NoJitState, Some(Retention.Strong)))
      )
    )

  /** The normal forms the executor reads of the term under the dependencies, in
    * a fixed order, and the executor after. Throws `IllegalStateException`
    * for a reading the limit or the stop stops.
    */
  private def read(
      executor: Executor[encoding.type, ReadingSuspension[encoding.type]],
      term: Configured[encoding.type],
      dependencies: ExecutionDependencies,
      stop: StopSignal
  ): (Vector[Configured[encoding.type]], Executor[encoding.type, ReadingSuspension[encoding.type]]) =
    val (after, _, progress) = executor.executed(term, dependencies, Budget(limit, countedUnits = false, stop))
    if progress.suspension.nonEmpty then
      throw IllegalStateException(s"the reading of $term did not finish within $limit steps")
    (progress.found.sorted(gezi.ir.ContentComparison.ordering), after)

  kinds.foreach((name, made, next) =>
    stoppableProperty(s"under a new source after a write, an executor that keeps $name reads what the file holds") { stopped =>
      val stop = StopSignal.completedWith(stopped)
      for
        drawn <- operations.forAll
        rewritten <- Gen.int(Range.constant(0, 3)).forAll
      yield
        // The case the law must reach, by construction every iteration: a
        // reading, a write, and a reading after it.
        val steps = drawn ++ List(Operation.Read, Operation.Written(rewritten), Operation.Read)
        val directory = Files.createTempDirectory(files, "tree")
        val file = directory.resolve("value" + DirectoryTree.fileExtension)
        Files.writeString(file, text(0))
        val applier = Lambdalattice.term("λu. u" + " (λa. a)" * (DirectoryTree.scope(file).size + 1))
        val term = encoding.application(Defunctionalization.thunkInstruction[encoding.type](applier), encoding.uri(file.toAbsolutePath.normalize.toUri))
        try
          val (_, _, _, checks) = steps.foldLeft((made(), ExpansionSource.fresh(), 0, Vector.empty[Result])) {
            case ((kept, _, _, checked), Operation.Written(numeral)) =>
              Files.writeString(file, text(numeral))
              (kept, ExpansionSource.fresh(), numeral, checked)
            case ((kept, source, numeral, checked), Operation.Read) =>
              val (found, after) = read(kept.executor, term, ExecutionDependencies(kept.cache, source), stop)
              (next(kept.copy(executor = after)), source, numeral, checked :+ Result.assert(JitTesting.sameTerms(found, expected(numeral, stop))))
          }
          Result.all(checks.toList)
        finally
          Files.delete(file)
          Files.delete(directory)
    }
  )
