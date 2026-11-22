package gezi.contest.entry

import java.nio.file.Paths
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Lambdalattice
import gezi.frontend.Literals
import gezi.generatedinputs.GeneratedProperties
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.JitConfiguration
import gezi.jit.NativeBackend
import gezi.jit.TableCost
import gezi.narrowblocks.ProgramCompilation
import gezi.standardlibrary.StandardLibrary

/** The laws of choosing an executor module by the identity of its selector
  * (`ExecutorModules`, `Defaults.executor`),
  * with the module of
  * these tests (`TestExecutorModule`), registered with
  * `java.util.ServiceLoader` in the tests' resources. Their purpose is to
  * catch a lookup that finds a module by anything but its selector's term, a
  * module that does not get the parameters the entry wrote or the
  * compilation the framework was given, a selector the
  * entry imports that is another instruction than the one the module
  * registers, a selector no module gives that is answered by some module or
  * by the framework's executor, and two modules that give one selector
  * answered by either.
  */
class ExecutorModuleLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot")).toAbsolutePath.normalize

  /** The modules the tests' class path registers, read off the tree whose
    * visible subtree is Gezi's directory.
    */
  private lazy val modules: ExecutorModules = ExecutorModules.registered(buildRoot)

  /** The library of no knowledge (tests/library_fixtures/no_knowledge). */
  private lazy val library =
    StandardLibrary.compiledAt(buildRoot, buildRoot.resolve("tests/library_fixtures/no_knowledge.lambdalattice"), Vector(BackendChecks))

  /** The framework's JIT over the library, what a module's executor is
    * built over.
    */
  private lazy val jit = Defaults.jit(BackendFacts.of(library), jitOptions)

  /** A compilation of no round over the library, what a module is handed
    * beside the JIT.
    */
  private lazy val compilation = ProgramCompilation(library.index, Vector.empty, NativeBackend.standard)

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(JitConfiguration.defaultInstanceTableGeneration),
    budget = JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily
  )

  private val readingOptions =
    ReadingOptions(ApplicationOption.ByLayer, TableSharingOption.Local, TableRetentionOption.NoneKept, ContinuationOption.Substituted, ParallelOption.BothSides)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => modules, _ => jit, _ => compilation)

  /** The test module's selector written out, the term its selector file
    * tests/executor_module_fixtures/test_executor gives: α-equivalent terms
    * are one term.
    */
  private val testSelector: String = "((λ\"$test\". λx. x) \"$test\")"

  /** The text of the library's Scott integer of the value. */
  private def number(value: BigInt): String = s"(${Lambdalattice.text(Literals.integerTerm(value), Map.empty)})"

  /** An entry of no round and no knowledge whose executor is the text
    * given, its other options those above.
    */
  private def entryText(executor: String): String =
    EntryText.entry(
      Vector.empty,
      Vector.empty,
      Vector(EntryText.contribution(EntryData.backendGroupWidths, EntryText.backendSlots(jitOptions, readingOptions, executor, CompilationPlaceOption.Upfront)))
    )

  property("anEntrySelectingTheTestModuleGetsItsExecutorWithTheParametersItWrote") {
    for parameter <- Gen.long(Range.linearFrom(0L, Long.MinValue, Long.MaxValue)).map(BigInt(_)).forAll
    yield
      val data = EntryData.lambdalatticeRead(entryText(EntryText.moduleExecutor(testSelector, s"λs. s ${number(parameter)}")))
      Defaults.executor(jit, data.reading, compilation, data.executor, modules) match
        case ParameterCarryingExecutor(read, handed, _) =>
          Result.diff(read, parameter)(_ == _).and(Result.diff(handed, compilation)(_ eq _).log("the compilation handed"))
        case other => Result.failure.log(s"the executor chosen is $other")
  }

  /** Its purpose is to catch a selector the entry imports from the module's
    * selector file that reads as another instruction than the module's: the
    * entry of tests/executor_module_fixtures/entry_with_test_executor, read
    * through the tree as the generic entry reads one, gets the test module's
    * executor with its parameter, 7.
    */
  test("anEntryImportingTheSelectorFileGetsTheTestModule") {
    val (data, _) = EntryData.at(
      buildRoot,
      buildRoot.resolve("tests/executor_module_fixtures/entry_with_test_executor.lambdalattice"),
      Defaults.entryDataState
    )
    Defaults.executor(jit, data.reading, compilation, data.executor, modules) match
      case ParameterCarryingExecutor(read, _, _) => assertEquals(read, BigInt(7))
      case other                                 => fail(s"the executor chosen is $other")
  }

  property("aSelectorNoModuleGivesIsRefused") {
    for count <- Gen.int(Range.linear(0, 6)).forAll
    yield
      val selector = s"(λa. λb. a${" b" * count})"
      val data = EntryData.lambdalatticeRead(entryText(EntryText.moduleExecutor(selector, s"λs. s ${number(1)}")))
      Result.assert(scala.util.Try(Defaults.executor(jit, data.reading, compilation, data.executor, modules)).failed.toOption.exists {
        case _: EntryDataError => true
        case _                 => false
      })
  }

  /** Its purpose is to catch a table that keeps one of two modules whose
    * selector files give one term: the test module registered twice is
    * refused.
    */
  test("twoModulesGivingOneSelectorAreRefused") {
    intercept[EntryDataError](ExecutorModules.registered(buildRoot, Vector(TestExecutorModule(), TestExecutorModule())))
  }
