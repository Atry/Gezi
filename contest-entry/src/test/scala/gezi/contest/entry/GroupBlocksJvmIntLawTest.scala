package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.ir.Closed
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.StorageAccess
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.JitValue
import gezi.jit.JvmIntNatives
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.ScottADTChoices

/** The laws of group blocks over 32-bit words (productions I1 to I3 of the
  * group grammar), through the JIT, on the scalar and on the JVM array group
  * backend, over the library of `tests/library_fixtures/jvm_int.lambdalattice`,
  * J the criterion `jvm_int_type`. Derived from the productions' guarantees:
  *
  *  - `(λx. f (x ∥ J) (x ∥ J)) (s₁ + … + sₖ)`, the sᵢ storages of distinct
  *    ints and f `int32_add` or `int32_less_than`, compiles to a block (I1,
  *    I2) the reading keeps, and its normal forms are those of f on every
  *    pair: those the same program reads with no group blocks, where the
  *    native computes its define on each pair (`JvmIntStorageLawTest`), the
  *    sums wrapped modulo 2³² or the comparisons' truth values;
  *  - `(λx. int32_add (x ∥ J) c) (s₁ + … + sₖ)`, c a storage written in the
  *    block (I3), gives the normal forms of `int32_add sᵢ c` for each i, those
  *    the program reads with no group blocks.
  *
  * Their purpose is to catch a 32-bit word that enters or leaves a block as
  * another value, a kernel or a static method that computes another result
  * than the native, and a constant column that is not the storage written.
  */
class GroupBlocksJvmIntLawTest extends GeneratedProperties:

  /** A reading of a block of 32-bit words takes 0.1 s to 0.4 s, most of it
    * reading back 32-cell words (measured 2026-11-24 on 6 cores at nice 10);
    * a property reads its program three times on each of 5 inputs.
    */
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(20, "s")

  private def fewInputs(config: hedgehog.core.PropertyConfig): hedgehog.core.PropertyConfig =
    config.copy(testLimit = hedgehog.core.SuccessCount(5))

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(buildRoot, buildRoot.resolve("tests/library_fixtures/jvm_int.lambdalattice"), Vector(BackendChecks))

  private lazy val facts = BackendFacts.of(library)

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/jvm_int_terms.lambdalattice",
          Vector(
            "true", "false", "boolean_type", "word_end", "word_cell", "word_type", "int32_type", "jvm_int_type",
            "int32_add", "int32_subtract", "int32_multiply", "int32_negate", "int32_equal", "int32_less_than"
          )
        ),
        Expansions.none
      )
      ._1

  /** The library compiled and its terms read before the first test, not
    * charged to it.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] = Vector(_ => terms, _ => facts)

  /** The backend's encoding, the configuration every program and storage of these laws is a term of. */
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private def operations: StorageEncodingOperations[encoding.type] = encoding.operations

  /** A library member as a term of the encoding: the same object as the member read with no facts. */
  private def term(name: String): Configured[encoding.type] =
    Configured.fromPure(encoding)(Pure.required(terms.getOrElse(name, throw IllegalArgumentException(s"no member $name"))))

  /** A closed value of the encoding as its term: a storage holds no neutral value. */
  private def closedTerm(found: JitValue[encoding.type]): Configured[encoding.type] =
    Closed.configured(found).getOrElse(throw IllegalStateException(s"a storage is closed: $found"))

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = gezi.jit.TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(gezi.jit.JitConfiguration.defaultInstanceTableGeneration),
    budget = gezi.jit.JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily,
    instanceReuse = InstanceReuseOption.WithinVersion
  )

  private val readingOptions =
    ReadingOptions(ApplicationOption.ByLayer, TableSharingOption.Local, TableRetentionOption.NoneKept, ContinuationOption.Substituted, ParallelOption.BothSides)

  private def reading(program: Configured[encoding.type], groupBlocks: GroupBlocksOption, stop: StopSignal) =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments.read(executor, ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()), program, 1000000L, stop, jit.readingConfiguration)

  /** The normal forms of the program under the group blocks given, and
    * whether the reading kept a compiled block.
    */
  private def readOnce(program: Configured[encoding.type], groupBlocks: GroupBlocksOption, stop: StopSignal): (Option[ScottADTChoices.Read[encoding.type]], Boolean) =
    val read = reading(program, groupBlocks, stop)
    val kept = read.executor match
      case executor: gezi.weakhead.ReadingExecutor[?] =>
        executor.jitState match
          case state: gezi.jit.JitRunState[?] => state.groupBlocks.values.exists(_.isDefined)
          case other                       => throw IllegalStateException(s"a reading of the JIT leaves its run state, not $other")
      case other => throw IllegalStateException(s"the framework's executor is a reading executor, not $other")
    (read.read, kept)

  private def storage(bits: Int): Configured[encoding.type] =
    closedTerm(operations.storageOf(JvmIntNatives.jvmInt, JvmIntNatives.value(bits)))

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  /** `λx. f (x ∥ J) (x ∥ J)`: x at slot 0, f at slot 1, J at slot 2. */
  private def doubledBlock(function: String): Configured[encoding.type] =
    val filtered = Code.Parallel(slot(0), slot(2))
    encoding.thunkOrInstance(applied(slot(1), filtered, filtered), Vector(Hole.Bound(0)), Vector(term(function), term("jvm_int_type")))

  /** `λx. int32_add (x ∥ J) c`: x at slot 0, int32_add at 1, J at 2, c at 3. */
  private def withConstant(constant: Int): Configured[encoding.type] =
    encoding.thunkOrInstance(
      applied(slot(1), Code.Parallel(slot(0), slot(2)), slot(3)),
      Vector(Hole.Bound(0)),
      Vector(term("int32_add"), term("jvm_int_type"), storage(constant))
    )

  private def chosen(values: Vector[Int]): Configured[encoding.type] = values.map(storage).reduceRight(encoding.choice(_, _))

  /** Every backend's reading is the expected one and kept a compiled block. */
  private def sameBackendReadings(found: Vector[(Option[ScottADTChoices.Read[encoding.type]], Boolean)], expected: Option[ScottADTChoices.Read[encoding.type]]): Boolean =
    found.forall((read, kept) => kept && ScottReadingComparison.sameReadings(read, expected))

  private val ints: Gen[Vector[Int]] =
    Gen
      .frequency1(3 -> Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)), 1 -> Gen.element1(0, 1, -1, Int.MinValue, Int.MaxValue))
      .list(Range.linear(1, 3))
      .map(_.distinct.toVector)

  private val backends: Vector[GroupBlocksOption] =
    Vector(GroupBlocksOption.Enabled(), GroupBlocksOption.Enabled(backend = GroupBackendOption.JvmArray))

  stoppableProperty("a block of a 32-bit native on every pair gives the native's results on each pair, on both backends", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      function <- Gen.element1("int32_add", "int32_less_than").forAll
      group <- ints.forAll
    yield
      val program = encoding.application(doubledBlock(function), chosen(group))
      val (expected, _) = readOnce(program, GroupBlocksOption.None, stop)
      Result.assert(sameBackendReadings(backends.map(readOnce(program, _, stop)), expected))
  }

  stoppableProperty("a storage written in the block is its constant, as the same value given alone", fewInputs) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      group <- ints.forAll
      constant <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)).forAll
    yield
      val program = encoding.application(withConstant(constant), chosen(group))
      val (expected, _) = readOnce(program, GroupBlocksOption.None, stop)
      Result.assert(sameBackendReadings(backends.map(readOnce(program, _, stop)), expected))
  }
