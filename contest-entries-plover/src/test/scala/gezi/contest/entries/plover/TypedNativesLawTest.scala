package gezi.contest.entries.plover

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.nio.file.Paths
import gezi.contest.entry.BackendOption
import gezi.contest.entry.CheckpointOption
import gezi.contest.entry.GroupBlocksOption
import gezi.contest.entry.Defaults
import gezi.contest.entry.DispatchOption
import gezi.contest.entry.GranularityOption
import gezi.contest.entry.InstanceRetentionOption
import gezi.contest.entry.InstanceReuseOption
import gezi.contest.entry.JitOptions
import gezi.contest.entry.LookaheadOption
import gezi.contest.entry.NativeBlocksOption
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.Budget
import gezi.hotspot.ExecutionDependencies
import gezi.hotspot.ExpansionSource
import gezi.ir.Configured
import gezi.ir.Pure
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.BinaryNatural
import gezi.jit.JitConfiguration
import gezi.jit.JitCounts
import gezi.jit.JitRunState
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativeName
import gezi.jit.NativeValue
import gezi.jit.NativesProvider
import gezi.jit.StorageEncoding
import gezi.jit.TableCost
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.weakhead.Expansions
import gezi.weakhead.Mode
import gezi.weakhead.NoJitState
import gezi.weakhead.Reading
import gezi.weakhead.ReadingExecutor
import gezi.weakhead.ScottADTChoices

/** The laws of the typed versions of `plover_typed_natives`: on generated
  * operands, zero and equal operands included, each typed version reads as the
  * native bound to it computes, its result admitted by its result filter. Their
  * purpose is to catch a typed version whose filter rejects a value the native
  * returns (a result filter that excludes zero, say) or that passes its
  * operands in the wrong order, a binding the JIT never calls, so that the
  * define's body alone answers, and a module whose bindings the backend's check
  * refuses. Each call is written as a typed branch writes it, its operands
  * filtered, so each is a decode point and a working binding calls its native
  * at least once; the fixture binds these natives through the typed versions
  * only. The product's native belongs to another entry's project and is not on
  * this classpath, so its call is read and not counted. The reader is the JIT,
  * whose filters are decode points: the reference evaluator reads both sides of
  * a filter, and the type's side of a recursive define over a filtered operand
  * is an unbounded reading.
  */
class TypedNativesLawTest extends GeneratedProperties:

  // The first property compiles the fixture's knowledge, past the 3 s default.
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(90, "s")

  private lazy val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** A field of a library file, read with no facts and crossed into the
    * encoding by its pure key.
    */
  private def field(
      file: String,
      arity: Int,
      position: Int
  ): Configured[encoding.type] =
    Configured.fromPure(encoding)(
      Pure.required(
        StandardLibrary
          .entryFields(
            buildRoot,
            buildRoot.resolve(file),
            Expansions.none,
            arity
          )
          ._1(position)
      )
    )

  private val typedFile =
    "corpora/library/plover_compositions/plover_typed_natives.lambdalattice"
  private val binaryFile = "corpora/library/binary/natural.lambdalattice"
  private val booleanFile = "corpora/library/native_types/boolean.lambdalattice"
  private val naturalFile = "corpora/library/native_types/natural.lambdalattice"

  private lazy val typedIncrement = field(typedFile, 5, 0)
  private lazy val typedEquality = field(typedFile, 5, 1)
  private lazy val typedTimes = field(typedFile, 5, 2)
  private lazy val typedDouble = field(typedFile, 5, 3)
  private lazy val typedEven = field(typedFile, 5, 4)
  private lazy val binaryZero = field(binaryFile, 5, 0)
  private lazy val binaryEven = field(binaryFile, 5, 1)
  private lazy val binaryOdd = field(binaryFile, 5, 2)
  private lazy val booleanTrue = field(booleanFile, 4, 0)
  private lazy val booleanFalse = field(booleanFile, 4, 1)
  private lazy val unaryZero = field(naturalFile, 4, 0)
  private lazy val unarySuccessor = field(naturalFile, 4, 1)
  private lazy val naturalType = field(naturalFile, 4, 3)
  private lazy val canonical =
    encoding.application(field(binaryFile, 5, 4), booleanTrue)

  private lazy val library = StandardLibrary.compiledAt(
    buildRoot,
    buildRoot.resolve(
      "tests/library_fixtures/plover_typed_natives.lambdalattice"
    ),
    Vector(BackendChecks(NativesProvider.loaded))
  )

  /** The backend's encoding of the fixture's facts, the configuration the
    * programs are read in.
    */
  private lazy val encoding: StorageEncoding =
    BackendFacts.of(library).storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: gezi.ir.StorageAccess = gezi.ir.StorageAccess.granted()

  private lazy val jit =
    Defaults.jit(
      encoding,
      JitOptions(
        DispatchOption.Fallback,
        BackendOption.Closure,
        GranularityOption.PredicatePerCode,
        instanceTable = false,
        instanceTableTrial = TableCost.trial,
        instanceRetention = InstanceRetentionOption.Generations(
          JitConfiguration.defaultInstanceTableGeneration
        ),
        budget = JitConfiguration.defaultBudget,
        checkpoints = CheckpointOption.Profitable,
        nativeBlocks = NativeBlocksOption.None,
        lookahead = LookaheadOption.Lazily,
        instanceReuse = InstanceReuseOption.WithinVersion
      ),
      GroupBlocksOption.None,
      access
    )

  private lazy val executor =
    ReadingExecutor(Mode.Jit, jit.readingConfiguration, NoJitState)

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => executor)

  /** The program's Scott ADT values, none when the reading stopped, and the
    * JIT's counts of the reading.
    */
  private def reading(
      program: Configured[encoding.type],
      stop: StopSignal
  ): (Option[ScottADTChoices[encoding.type]], JitCounts) =
    val (after, _, progress) = executor.executed(
      program,
      ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
      Budget(Reading.budgetSteps(1), countedUnits = false, stop)
    )
    val counts = JitRunState
      .held(after.jitState, jit.configuration)
      .getOrElse(
        throw AssertionError(
          s"the JIT's reading left the state ${after.jitState}"
        )
      )
      .counts
    (
      Option.when(progress.suspension.isEmpty)(
        ScottADTChoices.ofNormalForms(progress.found).choices
      ),
      counts
    )

  private def applied(
      function: Configured[encoding.type],
      arguments: Configured[encoding.type]*
  ): Configured[encoding.type] =
    arguments.foldLeft(function)(encoding.application(_, _))

  private def binary(value: BigInt): Configured[encoding.type] =
    if value == 0 then binaryZero
    else
      applied(
        if value.testBit(0) then binaryOdd else binaryEven,
        binary(value >> 1)
      )

  private def unary(value: Int): Configured[encoding.type] =
    (0 until value).foldLeft(unaryZero)((number, _) =>
      applied(unarySuccessor, number)
    )

  private def bool(value: Boolean): Configured[encoding.type] =
    if value then booleanTrue else booleanFalse

  private def filteredBinary(value: BigInt): Configured[encoding.type] =
    encoding.parallel(binary(value), canonical)

  private def filteredUnary(value: Int): Configured[encoding.type] =
    encoding.parallel(unary(value), naturalType)

  private def native(
      name: String,
      operands: Vector[NativeArgument]
  ): NativeValue =
    NativeBackend.standard
      .natives(NativeName.Function(name))
      .implementation(operands)

  private def binaryOperand(value: BigInt): NativeArgument =
    NativeArgument.Represented(BinaryNatural(value))

  private def unaryOperand(value: Int): NativeArgument =
    NativeArgument.Represented(NativeValue.Natural(BigInt(value)))

  /** The typed call reads as the expected value, which has a normal form. */
  private def readsAs(
      call: Configured[encoding.type],
      expected: Configured[encoding.type],
      stop: StopSignal
  ): Result =
    val (wanted, _) = reading(expected, stop)
    val found = reading(call, stop)._1
    val same = (found, wanted) match
      case (None, None)                => true
      case (Some(first), Some(second)) => ScottADTChoices.same(first, second)
      case _                           => false
    Result.all(
      List(
        Result
          .assert(wanted.exists(ScottADTChoices.members(_).nonEmpty))
          .log("the expected value has no normal form"),
        Result
          .assert(same)
          .log(s"the call reads $found, the expected value $wanted")
      )
    )

  /** The typed call reads as the expected value, and the reading called the
    * native.
    */
  private def readsThroughNative(
      call: Configured[encoding.type],
      expected: Configured[encoding.type],
      nativeName: String,
      stop: StopSignal
  ): Result =
    val (_, counts) = reading(call, stop)
    Result.all(
      List(
        readsAs(call, expected, stop),
        Result
          .assert(counts.callsOf(NativeName.Function(nativeName)) > 0)
          .log(s"$nativeName was not called: $counts")
      )
    )

  private val operand: Gen[BigInt] =
    Gen.long(Range.linear(0L, 255L)).map(BigInt(_))

  stoppableProperty("the typed increment and equality read as their natives") {
    stopped =>
      val stop = StopSignal.completedWith(stopped)
      for
        first <- operand.forAll
        drawn <- operand.forAll
        repeated <- Gen.boolean.forAll
      yield
        val second = if repeated then first else drawn
        val next =
          native("wren_binary_increment", Vector(binaryOperand(first))) match
            case BinaryNatural(value) => value
            case other => throw AssertionError(s"the increment gave $other")
        val same = native(
          "wren_binary_equality",
          Vector(binaryOperand(first), binaryOperand(second))
        ) match
          case NativeValue.Truth(value) => value
          case other => throw AssertionError(s"the equality gave $other")
        Result
          .all(
            List(
              Result
                .diff(next, first + 1)(_ == _)
                .log("the increment's native"),
              readsThroughNative(
                applied(typedIncrement, filteredBinary(first)),
                binary(next),
                "wren_binary_increment",
                stop
              ),
              Result
                .diff(same, first == second)(_ == _)
                .log("the equality's native"),
              readsThroughNative(
                applied(
                  typedEquality,
                  filteredBinary(first),
                  filteredBinary(second)
                ),
                bool(same),
                "wren_binary_equality",
                stop
              )
            )
          )
          .log(s"the operands $first and $second")
  }

  stoppableProperty("the typed product reads as the product") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      first <- operand.forAll
      second <- operand.forAll
    yield readsAs(
      applied(typedTimes, filteredBinary(first), filteredBinary(second)),
      binary(first * second),
      stop
    ).log(s"the operands $first and $second")
  }

  stoppableProperty("the typed double and even read as their natives") {
    stopped =>
      val stop = StopSignal.completedWith(stopped)
      for number <- Gen.int(Range.linear(0, 40)).forAll
      yield
        val doubled =
          native("natural_double", Vector(unaryOperand(number))) match
            case NativeValue.Natural(value) => value
            case other => throw AssertionError(s"the double gave $other")
        val parity = native("natural_even", Vector(unaryOperand(number))) match
          case NativeValue.Truth(value) => value
          case other => throw AssertionError(s"the even gave $other")
        Result
          .all(
            List(
              Result
                .diff(doubled, BigInt(2 * number))(_ == _)
                .log("the double's native"),
              readsThroughNative(
                applied(typedDouble, filteredUnary(number)),
                unary(doubled.toInt),
                "natural_double",
                stop
              ),
              Result
                .diff(parity, number % 2 == 0)(_ == _)
                .log("the even's native"),
              readsThroughNative(
                applied(typedEven, filteredUnary(number)),
                bool(parity),
                "natural_even",
                stop
              )
            )
          )
          .log(s"the number $number")
  }

  test("the product's module reads") {
    // Its native belongs to another entry's project, so the backend's check cannot run here.
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve(
        "corpora/compiler/solo_typed_times_native.lambdalattice"
      ),
      Vector.empty
    )
  }
