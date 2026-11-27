package gezi.contest.modules.solo

import java.nio.file.Paths
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.contest.entry.ApplicationOption
import gezi.contest.entry.BackendOption
import gezi.contest.entry.CheckpointOption
import gezi.contest.entry.LookaheadOption
import gezi.contest.entry.InstanceReuseOption
import gezi.contest.entry.CompilationPlaceOption
import gezi.contest.entry.OccurrenceTaggingOption
import gezi.contest.entry.ContinuationOption
import gezi.contest.entry.GroupBlocksOption
import gezi.contest.entry.Defaults
import gezi.contest.entry.DispatchOption
import gezi.contest.entry.EntryData
import gezi.contest.entry.EntryText
import gezi.contest.entry.ExecutorModules
import gezi.contest.entry.GranularityOption
import gezi.contest.entry.InstanceRetentionOption
import gezi.contest.entry.JitOptions
import gezi.contest.entry.NativeBlocksOption
import gezi.contest.entry.ParallelOption
import gezi.contest.entry.ReadingOptions
import gezi.contest.entry.TableRetentionOption
import gezi.contest.entry.TableSharingOption
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ArtifactKey
import gezi.hotspot.Budget
import gezi.hotspot.CompilationUnit
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.Executor
import gezi.hotspot.ExpansionSource
import gezi.hotspot.NormalForm
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.JitConfiguration
import gezi.jit.NativeBackend
import gezi.narrowblocks.ProgramArtifacts
import gezi.narrowblocks.ProgramCompilation
import gezi.narrowblocks.ProgramCompiler
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.ReadingSuspension

private given tieredExecutorLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of the tiered executor (`TieredExecutor` under `InterpretFirst`),
  * on generated programs and a drawn number of interpretation steps. Its
  * purpose is to catch a tiered execution that changes what is read rather than
  * how: a normal form lost, added or repeated across the switch from the
  * interpretation to the compiled program, and a policy that compiles a program
  * whose interpretation finished, or reads a program it has not compiled.
  *
  * The compiler's configuration has no lemma round, so a program's artifact is
  * the program itself (`ProgramCompiler.compiledProgram`): what the rounds give
  * is the program compiler's own law (`ProgramCompilerLawTest`), and here the
  * compiled tier reads the program again from its root, which is where normal
  * forms would be repeated.
  */
class TieredExecutorLawTest extends GeneratedProperties:

  private val buildRoot =
    Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  /** The library of no knowledge (tests/library_fixtures/no_knowledge). */
  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/no_knowledge.lambdalattice"),
      Vector(BackendChecks)
    )

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = true,
    instanceTableTrial = 1024,
    instanceRetention = InstanceRetentionOption.NeverDropped,
    budget = JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily,
    instanceReuse = InstanceReuseOption.WithinVersion
  )

  /** The JIT over the library, with the instance table on. */
  private lazy val encoding: gezi.jit.StorageEncoding =
    gezi.jit.BackendFacts.of(library).storageEncoding

  private lazy val jit = Defaults.jit(
    encoding,
    jitOptions,
    GroupBlocksOption.None,
    gezi.ir.StorageAccess.granted()
  )

  private lazy val modules: ExecutorModules =
    ExecutorModules.registered(buildRoot)

  private val readingOptions =
    ReadingOptions(
      ApplicationOption.ByLayer,
      TableSharingOption.Local,
      TableRetentionOption.KeptAll,
      ContinuationOption.Substituted,
      ParallelOption.BothSides
    )

  /** The compilation of no lemma round over the library's index. */
  private lazy val compilation =
    ProgramCompilation(
      gezi.standardlibrary.StandardLibraryIndex
        .crossed(library.index, encoding),
      Vector.empty,
      NativeBackend(Map.empty, Vector.empty),
      encoding
    )

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => encoding, _ => jit, _ => compilation, _ => modules)

  /** The steps each program may take. */
  private val limit: Long = 20000

  /** The framework's reading executor of the JIT. */
  private def reading
      : Executor[encoding.type, ReadingSuspension[encoding.type]] =
    Defaults.executor(jit, readingOptions)

  /** A closed term of about `size` nodes with abstractions, applications,
    * choices of none to three members and parallels, its variables bound by the
    * `bound` abstractions around it.
    */
  private def term(size: Int, bound: Int): Gen[DeBruijnTerm] =
    val leaf: Gen[DeBruijnTerm] =
      if bound == 0 then
        Gen.constant(DeBruijnTerm.Lambda(DeBruijnTerm.Variable(0)))
      else Gen.int(Range.constant(0, bound - 1)).map(DeBruijnTerm.Variable(_))
    if size <= 1 then leaf
    else
      Gen.int(Range.constant(1, 20)).flatMap { kind =>
        val smaller = size - 1
        if kind <= 7 then term(smaller, bound + 1).map(DeBruijnTerm.Lambda(_))
        else if kind <= 15 then
          Gen
            .int(Range.constant(1, smaller))
            .flatMap(left =>
              for
                function <- term(left, bound)
                argument <- term(1.max(smaller - left), bound)
              yield DeBruijnTerm.Apply(function, argument)
            )
        else if kind <= 17 then
          Gen
            .int(Range.constant(0, 3))
            .flatMap(count =>
              term(1.max(smaller / 1.max(count)), bound)
                .list(Range.singleton(count))
                .map(members =>
                  if members.isEmpty then Literals.top
                  else DeBruijnTerm.nestedChoice(members.toVector)
                )
            )
        else if kind <= 19 then
          Gen
            .int(Range.constant(1, smaller))
            .flatMap(left =>
              for
                first <- term(left, bound)
                second <- term(1.max(smaller - left), bound)
              yield DeBruijnTerm.Parallel(first, second)
            )
        else leaf
      }

  /** A closed application, the shape of a program. */
  private val application: Gen[DeBruijnTerm] =
    for
      size <- Gen.int(Range.linear(4, 24))
      left <- Gen.int(Range.constant(1, size - 2))
      function <- term(left, 0)
      argument <- term(1.max(size - 1 - left), 0)
    yield DeBruijnTerm.Apply(function, argument)

  /** A choice of one to four applications, so that a program often has several
    * normal forms, read one after another.
    */
  private val program: Gen[Configured[NoFacts.type]] =
    application
      .list(Range.linear(1, 4))
      .map(members =>
        Defunctionalization.thunkInstruction(
          DeBruijnTerm.nestedChoice(members.toVector)
        )(using gezi.ir.NoFacts)
      )

  stoppableProperty(
    "theTieredExecutorReadsTheReadingExecutorsNormalFormsOnceAndCompilesOnlyWhatItsInterpretationDidNotFinish"
  ) { stopped =>
    for
      root <- program.forAll
      // The share of the reading's own steps the interpretation may spend, so that the switch to the compiled
      // program falls before, inside and after the reading as often.
      share <- Gen.double(Range.linearFrac(0.0, 1.5)).forAll
    yield
      val stop = StopSignal.completedWith(stopped)
      val (_, _, alone) =
        reading.executed(
          root,
          ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
          Budget(limit, countedUnits = false, stop)
        )
      val interpretationSteps = (alone.spent.steps * share).toLong
      val dependencies =
        ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh())
      val tiered = TieredExecutor(
        reading,
        ProgramCompiler(compilation),
        InterpretFirst(compilation, interpretationSteps)
      )
      val (_, after, progress) = tiered.executed(
        root,
        dependencies,
        Budget(limit, countedUnits = false, stop)
      )
      val compiled =
        after.cache
          .locked(ProgramArtifacts)(
            _.tryGet(
              ArtifactKey[Configured[NoFacts.type]](
                CompilationUnit.Program(root),
                compilation
              )
            )
          )
          .isDefined
      val bothFinished = alone.suspension.isEmpty && progress.suspension.isEmpty
      Result
        .all(
          List(
            Result
              .diff(progress.found.distinct.size, progress.found.size)(_ == _)
              .log("the tiered executor's normal forms read once"),
            if bothFinished then
              Result
                .diff(progress.found.toSet, alone.found.toSet)(_ == _)
                .log("the two readings' normal forms")
            else Result.success,
            if alone.suspension.isEmpty && alone.spent.steps <= interpretationSteps
            then
              Result
                .assert(!compiled)
                .log(
                  s"compiled a program its interpretation finished in ${alone.spent.steps} steps"
                )
            else Result.success
          )
        )
        .log(
          s"interpretation steps $interpretationSteps, the reading alone ${alone.spent.steps} steps"
        )
  }

  /** Its purpose is to catch a selector the entry writes that reads as another
    * instruction than the one the module registers, and parameters the module
    * reads otherwise than the entry wrote them: an entry whose executor writes
    * the term of corpora/modules/solo_tiering with a number of steps gets this
    * module's tiered executor, interpreting first within that number.
    */
  test("anEntryWritingTheSelectorGetsTheTieredExecutorWithItsSteps") {
    val steps = BigInt(12345)
    val selector = "((λ\"$tiering\". λx. x) \"$tiering\")"
    val parameters =
      s"λs. s (${Lambdalattice.text(Literals.integerTerm(steps), Map.empty)})"
    val data = EntryData.lambdalatticeRead(
      EntryText.entry(
        Vector.empty,
        Vector.empty,
        Vector(
          EntryText.contribution(
            EntryData.backendGroupWidths,
            EntryText.backendSlots(
              jitOptions,
              readingOptions,
              EntryText.moduleExecutor(selector, parameters),
              CompilationPlaceOption.ByExecutor,
              OccurrenceTaggingOption.Untagged
            )
          )
        )
      )
    )
    Defaults.executor(
      jit,
      data.reading,
      compilation,
      data.executor,
      modules
    ) match
      case TieredExecutor(_, _, InterpretFirst(_, found)) =>
        assertEquals(BigInt(found), steps)
      case other => fail(s"the executor chosen is $other")
  }
