package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
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
import gezi.jit.BackendFacts
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalFamily
import gezi.jit.BinaryNaturalNatives
import gezi.jit.BooleanFamily
import gezi.jit.DeclaredFamilies
import gezi.jit.JitValue
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.NativesProvider
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.saturation.StopSignal
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.ScottADTChoices

private given groupBlocksJitLawTestNoFacts: NoFacts.type = NoFacts

/** The static method of the law's sum native. Public, since a block calls it
  * by its name.
  */
object GroupBlocksJitSum:
  def summed(left: BigInteger, right: BigInteger): BigInteger = left.add(right)

/** The law's sum native as a block calls it. Its implementation on an
  * argument vector throws: the JIT runs it only where no group block ran the
  * application.
  */
private object GroupBlocksJitSumMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[GroupBlocksJitSum.type].getName.stripSuffix("$")
  val methodName: String = "summed"
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("group_blocks_jit_sum", arguments)

/** The laws of the JIT's group block slot with the scalar group blocks
  * (`GroupBlocksOption.Enabled` with its defaults), over a library bound by hand: the binary
  * naturals' and the booleans' constructors by the `data_family` and the
  * `native_specialization` of `binary_set` and of `boolean_type`, `plus`
  * bound to `wren_binary_plus`, `equality` to `wren_binary_equality`, and
  * `sum` bound to a native whose implementation on an argument vector throws. The program
  * is `(λx. f (x ∥ N) (x ∥ N)) (s₁ + … + sₙ)`, N the canonical naturals'
  * criterion `binary_set true`, the sᵢ storages of canonical naturals.
  * Derived from the slot's and the grammar's guarantees: the written thunk
  * applied to one argument, a choice of storages of the canonical
  * representation, is a block that admits it, so the JIT runs the block and
  * continues from the choice of its results, the sums of every pair, each
  * once; so
  *
  *  - with `sum`, the reading finishes, which it could not if the JIT read
  *    the application itself, and its normal forms are those of the sums'
  *    storages read alone, on the scalar and on the JVM array group backend
  *    (`GroupBackendOption`), which gives the scalar backend's rows;
  *  - with `sum` and the argument written `(λy. y) (s₁ + … + sₙ)`, an
  *    application and no storage, the reading finishes too with the same
  *    sums: the JIT reads the argument through the decode point `a ∥ N` at
  *    the block's entry, the choice of the storages;
  *  - with `plus`, the normal forms equal those of the same program read with
  *    no group blocks;
  *  - with `equality`, a block whose values are truth values, the same: its
  *    rows' truth values come back as the truth values' storages, as the
  *    native's results do;
  *  - a specialization choice `plus (x ∥ N) (x ∥ N) ∥ N + plus x x`, whose
  *    untyped member is no expression of the grammar (its parameter stands
  *    outside a filter), is read as its typed member alone, a refinement,
  *    so its normal forms are those of the typed member read with no group
  *    blocks, the choice's own by the specialization lemma (with no group
  *    blocks the whole choice reads no answer: its untyped member, operands
  *    a choice and no storage, is read by interpreting `plus`'s define,
  *    which on {0, 1} did not finish in 1,000,000 steps);
  *  - the reading's state keeps the block of the written thunk, compiled once
  *    for the reading and carried to the next (`JitRunState.groupBlocks`), and
  *    with no group blocks it keeps none, the mechanism never asked;
  *  - with `sum` and a truth parameter, `(λb. (b ∥ boolean_type) (sum 1 2) (sum 2 2)) t`,
  *    t a truth value's storage, the reading finishes with 3 for true and 4
  *    for false: the block, entered on the truth storage, selects the case;
  *  - under the instance retention's `Generations(1)`, a reading that meets
  *    the thunks of `plus` and of `equality` in this order keeps the second
  *    in the young generation and the first in the old one.
  *
  * Their purpose is to catch a slot that does not enter a block the grammar
  * compiles, an argument written as a choice of storages that the mechanism
  * does not read as a group, a block's value that differs from the
  * application's, and a block of truth values whose results the mechanism
  * cannot give back.
  */
class GroupBlocksJitLawTest extends GeneratedProperties:

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  private def thunk(code: Code, holes: Int): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(code, (0 until holes).map(Hole.Bound(_)).toVector, Vector.empty)

  /** λx. x x, bound to zero. */
  private val zero: Configured[NoFacts.type] = thunk(applied(slot(0), slot(0)), 1)

  /** λx y. y x, bound to even. */
  private val even: Configured[NoFacts.type] = thunk(applied(slot(1), slot(0)), 2)

  /** λx y z. z y x, bound to odd. */
  private val odd: Configured[NoFacts.type] = thunk(applied(slot(2), slot(1), slot(0)), 3)

  /** λx y. y y x, bound to `wren_binary_plus`. */
  private val plus: Configured[NoFacts.type] = thunk(applied(slot(1), slot(1), slot(0)), 2)

  /** λx y. x y x, bound to `wren_binary_equality`. */
  private val equality: Configured[NoFacts.type] = thunk(applied(slot(0), slot(1), slot(0)), 2)

  /** λx y. x x y, bound to the law's sum native. */
  private val sum: Configured[NoFacts.type] = thunk(applied(slot(0), slot(0), slot(1)), 2)

  /** λx y. x, the Scott true. */
  private val truth: Configured[NoFacts.type] = NoFacts.thunkOrInstance(slot(0), Vector(Hole.Bound(0), Hole.Ignored), Vector.empty)

  /** λx y. y, the Scott false. */
  private val falsity: Configured[NoFacts.type] = NoFacts.thunkOrInstance(slot(0), Vector(Hole.Ignored, Hole.Bound(0)), Vector.empty)

  /** λx. x x (x x), bound to boolean_type by its native_specialization and
    * its data_family, true and false.
    */
  private val booleanType: Configured[NoFacts.type] = thunk(applied(applied(slot(0), slot(0)), applied(slot(0), slot(0))), 1)

  /** λx y. x (y y), bound to binary_set by its native_specialization. */
  private val binarySet: Configured[NoFacts.type] = thunk(applied(slot(0), applied(slot(1), slot(1))), 2)

  private val index = StandardLibraryIndex(NoFacts, Vector.empty,
    Vector.empty,
    Vector(
      NativeBound(Pure.required(plus), "wren_binary_plus"),
      NativeBound(Pure.required(equality), "wren_binary_equality"),
      NativeBound(Pure.required(sum), "group_blocks_jit_sum")
    ),
    Vector(
      CombinatorProperty(Pure.required(binarySet), Property.NativeSpecialization("binary_natural")),
      CombinatorProperty(Pure.required(binarySet), Property.DataFamily(0, Vector(zero, even, odd).map(Pure.required))),
      CombinatorProperty(Pure.required(booleanType), Property.NativeSpecialization(BooleanFamily.identity.name)),
      CombinatorProperty(Pure.required(booleanType), Property.DataFamily(0, Vector(truth, falsity).map(Pure.required)))
    )
  )

  private val natives: NativeBackend = NativesProvider.loaded.extended(
    NativeBackend.functions(
      Map(
        "group_blocks_jit_sum" -> Native(
          Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical), NativePlace.Fixed(BinaryNaturalNatives.canonical)),
          NativePlace.Fixed(BinaryNaturalNatives.canonical),
          GroupBlocksJitSumMethod
        )
      ),
      Vector.empty
    )
  )

  private val facts = BackendFacts(index, DeclaredFamilies.extended(index, natives))

  /** The backend's encoding, the configuration every program and storage of these laws is a term of. */
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private def operations: StorageEncodingOperations[encoding.type] = encoding.operations

  /** A library term bound by hand above, as a term of the encoding: the same object (`Configured.fromPure`). */
  private def crossed(term: Configured[NoFacts.type]): Configured[encoding.type] = Configured.fromPure(encoding)(Pure.required(term))

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

  /** The reading of the program under the group blocks given. */
  private def reading(program: Configured[encoding.type], groupBlocks: GroupBlocksOption, stop: StopSignal) =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments.read(executor, ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()), program, 1000000L, stop, jit.readingConfiguration)

  /** The Scott ADT values of the program read under the group blocks given. */
  private def normalForms(program: Configured[encoding.type], groupBlocks: GroupBlocksOption, stop: StopSignal): Option[ScottADTChoices.Read[encoding.type]] =
    reading(program, groupBlocks, stop).read

  private def storage(value: BigInteger): Configured[encoding.type] =
    closedTerm(operations.storageOf(BinaryNaturalNatives.canonical, BinaryNatural(BigInt(value))))

  /** `λx. f (x ∥ N) (x ∥ N)`: x at slot 0, f at slot 1, N at slot 2. */
  private def doubledBlock(function: Configured[NoFacts.type]): Configured[encoding.type] =
    val filtered = Code.Parallel(slot(0), slot(2))
    encoding.thunkOrInstance(
      applied(slot(1), filtered, filtered),
      Vector(Hole.Bound(0)),
      Vector(crossed(function), encoding.application(crossed(binarySet), crossed(truth)))
    )

  private def chosen(values: Vector[BigInteger]): Configured[encoding.type] = values.map(storage).reduceRight(encoding.choice(_, _))

  /** `(λx. f (x ∥ N) (x ∥ N)) (s₁ + … + sₙ)`. */
  private def doubled(function: Configured[NoFacts.type], values: Vector[BigInteger]): Configured[encoding.type] = encoding.application(doubledBlock(function), chosen(values))

  /** The thunk of the code over x at slot 0, plus at slot 1, N at slot 2,
    * applied to the choice of the values' storages.
    */
  private def overPlus(code: Code, values: Vector[BigInteger]): Configured[encoding.type] =
    encoding.application(
      encoding.thunkOrInstance(code, Vector(Hole.Bound(0)), Vector(crossed(plus), encoding.application(crossed(binarySet), crossed(truth)))),
      chosen(values)
    )

  /** `plus (x ∥ N) (x ∥ N) ∥ N`, the typed member. */
  private val typedCode: Code =
    val filtered = Code.Parallel(slot(0), slot(2))
    Code.Parallel(applied(slot(1), filtered, filtered), slot(2))

  /** `(λx. plus (x ∥ N) (x ∥ N) ∥ N + plus x x) (s₁ + … + sₙ)`, a
    * specialization choice as the typed rounds leave one at a call, its
    * typed member first.
    */
  private def specialized(values: Vector[BigInteger]): Configured[encoding.type] =
    overPlus(Code.Choice(typedCode, applied(slot(1), slot(0), slot(0))), values)

  /** `(λx. plus (x ∥ N) (x ∥ N) ∥ N) (s₁ + … + sₙ)`, the typed member alone. */
  private def typedMember(values: Vector[BigInteger]): Configured[encoding.type] = overPlus(typedCode, values)

  private val values: Gen[Vector[BigInteger]] =
    Gen.int(Range.linear(0, 30)).list(Range.linear(1, 3)).map(_.distinct.toVector.map(value => BigInteger.valueOf(value.toLong)))

  stoppableProperty("the block runs the application whose native has no argument-vector implementation: the sums of every pair") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield
      val sums = (for
        left <- group
        right <- group
      yield left.add(right)).distinct
      val expected = sums.map(sum => normalForms(storage(sum), GroupBlocksOption.None, stop))
      Result.assert(
        ScottReadingComparison.sameAsUnion(normalForms(doubled(sum, group), GroupBlocksOption.Enabled(), stop), expected) &&
          ScottReadingComparison.sameAsUnion(normalForms(doubled(sum, group), GroupBlocksOption.Enabled(backend = GroupBackendOption.JvmArray), stop), expected)
      )
  }

  /** λy. y. */
  private val identity: Configured[NoFacts.type] = thunk(slot(0), 1)

  stoppableProperty("an argument written as an application is decoded at the block's entry: the reading finishes with the sums") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield
      val sums = (for
        left <- group
        right <- group
      yield left.add(right)).distinct
      val expected = sums.map(sum => normalForms(storage(sum), GroupBlocksOption.None, stop))
      Result.assert(
        ScottReadingComparison.sameAsUnion(
          normalForms(encoding.application(doubledBlock(sum), encoding.application(crossed(identity), chosen(group))), GroupBlocksOption.Enabled(), stop),
          expected
        )
      )
  }

  stoppableTest("a block of a truth parameter is entered on a truth value's storage") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    // λb. (b ∥ B) (sum 1 2) (sum 2 2): b 0, B 1, sum 2, 1 at 3, 2 at 4.
    val block = encoding.thunkOrInstance(
      applied(Code.Parallel(slot(0), slot(1)), applied(slot(2), slot(3), slot(4)), applied(slot(2), slot(4), slot(4))),
      Vector(Hole.Bound(0)),
      Vector(crossed(booleanType), crossed(sum), storage(BigInteger.ONE), storage(BigInteger.TWO))
    )
    def truthStorage(value: Boolean): Configured[encoding.type] =
      closedTerm(operations.storageOf(Representation.Truth, NativeValue.Truth(value)))
    val obtained = Vector(true, false).map(value => normalForms(encoding.application(block, truthStorage(value)), GroupBlocksOption.Enabled(), stop))
    val expected = Vector(3L, 4L).map(value => normalForms(storage(BigInteger.valueOf(value)), GroupBlocksOption.None, stop))
    assert(obtained.size == expected.size && obtained.zip(expected).forall((found, wanted) => ScottReadingComparison.sameReadings(found, wanted)))
  }

  stoppableProperty("the scalar group blocks give the normal forms the JIT gives with no group blocks") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield Result.assert(
      ScottReadingComparison.sameReadings(
        normalForms(doubled(plus, group), GroupBlocksOption.Enabled(), stop),
        normalForms(doubled(plus, group), GroupBlocksOption.None, stop)
      )
    )
  }

  stoppableProperty("a block of truth values gives the normal forms the JIT gives with no group blocks") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield Result.assert(
      ScottReadingComparison.sameReadings(
        normalForms(doubled(equality, group), GroupBlocksOption.Enabled(), stop),
        normalForms(doubled(equality, group), GroupBlocksOption.None, stop)
      )
    )
  }

  stoppableProperty("a specialization choice gives the normal forms of its typed member read with no group blocks") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield Result.assert(
      ScottReadingComparison.sameReadings(normalForms(specialized(group), GroupBlocksOption.Enabled(), stop), normalForms(typedMember(group), GroupBlocksOption.None, stop))
    )
  }

  stoppableTest("the reading's state keeps the written thunk's block, and none with no group blocks") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    def kept(groupBlocks: GroupBlocksOption) =
      reading(doubled(plus, Vector(BigInteger.ONE, BigInteger.TWO)), groupBlocks, stop).executor match
        case executor: gezi.weakhead.ReadingExecutor[?] =>
          executor.jitState match
            case state: gezi.jit.JitRunState[?] => state.groupBlocks.map((thunk, block) => (thunk, block.isDefined))
            case other                       => fail(s"a reading of the JIT leaves its run state, not $other")
        case other => fail(s"the framework's executor is a reading executor, not $other")
    assertEquals((kept(GroupBlocksOption.Enabled()), kept(GroupBlocksOption.None)), (Map(doubledBlock(plus) -> true), Map.empty))
  }

  stoppableTest("the blocks are kept in two generations of the instance retention's size") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val options = jitOptions.copy(instanceRetention = InstanceRetentionOption.Generations(1))
    val jit = Defaults.jit(encoding, options, GroupBlocksOption.Enabled(), access)
    val executor = Defaults.executor(jit, readingOptions)
    val group = Vector(BigInteger.ONE, BigInteger.TWO)
    val program = encoding.choice(doubled(plus, group), doubled(equality, group))
    Judgments.read(executor, ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()), program, 1000000L, stop, jit.readingConfiguration).executor match
      case read: gezi.weakhead.ReadingExecutor[?] =>
        read.jitState match
          case state: gezi.jit.JitRunState[?] =>
            assertEquals((state.groupBlocks.keySet, state.olderGroupBlocks.keySet), (Set(doubledBlock(equality)), Set(doubledBlock(plus))))
          case other => fail(s"a reading of the JIT leaves its run state, not $other")
      case other => fail(s"the framework's executor is a reading executor, not $other")
  }
