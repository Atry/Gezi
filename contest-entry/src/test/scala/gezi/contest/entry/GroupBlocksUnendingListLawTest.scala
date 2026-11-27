package gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
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
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.narrowblocks.groups.GroupGrammar
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.ScottADTChoices

/** The law of a list without end at a group block's entry, over the library of
  * `tests/library_fixtures/array_list.lambdalattice` (the library's own `nil`,
  * `cons`, `list_type` and `array_list`), N the canonical naturals' criterion
  * `binary_set true` and A the array lists' `array_list N`:
  * `(λx. (x ∥ A) 0 (λh t. h ∥ N)) ones`, ones the list of v's without end
  * (`fixpoint (λself. cons v self)` by value, v a storage of a canonical
  * natural), reads the one normal form of v without the group blocks within
  * 20,000 steps, and with them, at a share of 10%, within 22,223 steps, since
  * the block's entry may spend its share walking the list before it gives the
  * block up and leaves the machine the rest.
  *
  * The expectation follows from the β rule and the λ-lattice laws: A is
  * `list_type N` by the β rule (lemma 24.1 of
  * `docs/design/gezi-set-equations-proofs.md`), which is L with
  * `L = cons N L + nil` (corpora/library/native_types/list.lambdalattice), so
  * `L 0 c = c N L + 0`; ones is `cons v ones`, so `ones 0 c = c v ones`; a
  * parallel applied is the parallel of the applications, and with
  * `c = λh t. h ∥ N` the program is `(v ∥ N) ∥ ((N ∥ N) + 0)`, by
  * distributivity `(v ∥ N) + (v ∥ N ∥ 0)`. v is in N, so the first member reads
  * v; the second reads v when v is 0 and nothing otherwise, two distinct
  * numerals having no common normal form.
  *
  * Its purpose is to catch an entry, or a decode point, whose reading of a list
  * without end does not stop: the block's entry would decode `ones ∥ A` to its
  * end, and a decode point that reads every cell would too. At v = 0, the zero
  * constructor's storage, both members read v, so it catches as well a reader
  * that gives the one normal form twice instead of once.
  */
class GroupBlocksUnendingListLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/array_list.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/array_list_terms.lambdalattice",
          Vector("binary_set", "true", "nil", "cons", "list_type", "array_list")
        ),
        Expansions.none
      )
      ._1

  /** The library compiled before the first test, about 2.5 s, past a test's 3 s
    * deadline, and a JIT made of its facts as the tests make it, whose
    * construction checks the facts once for the facts (the unique spelling's
    * premise, 0.4 to 1 s, 2026-11-25).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(
      _ => terms,
      _ => facts,
      _ => Defaults.jit(encoding, jitOptions, GroupBlocksOption.None, access)
    )

  /** The backend's encoding, the configuration every program and storage of
    * this law is a term of.
    */
  private lazy val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  private given access: StorageAccess = StorageAccess.granted()

  private def operations: StorageEncodingOperations[encoding.type] =
    encoding.operations

  /** A library member as a term of the encoding: the same object as the member
    * read with no facts.
    */
  private def term(name: String): Configured[encoding.type] =
    Configured.fromPure(encoding)(
      Pure.required(
        terms.getOrElse(
          name,
          throw IllegalArgumentException(s"no member $name")
        )
      )
    )

  /** A closed value of the encoding as its term: a storage holds no neutral
    * value.
    */
  private def closedTerm(
      found: JitValue[encoding.type]
  ): Configured[encoding.type] =
    Closed
      .configured(found)
      .getOrElse(throw IllegalStateException(s"a storage is closed: $found"))

  private def slot(index: Int): Code = Code.Slot(index)

  private def storage(value: BigInteger): Configured[encoding.type] =
    closedTerm(
      operations.storageOf(
        BinaryNaturalNatives.canonical,
        BinaryNatural(BigInt(value))
      )
    )

  /** The list of v's without end, `fixpoint (λself. cons v self)` by value:
    * self 0, cons 1, v 2.
    */
  private def unending(value: BigInteger): Configured[encoding.type] =
    encoding.application(
      Configured.fromPure(encoding)(GroupGrammar.fixpointByValue),
      encoding.thunkOrInstance(
        Code.Apply(Code.Apply(slot(1), slot(2)), slot(0)),
        Vector(Hole.Bound(0)),
        Vector(term("cons"), storage(value))
      )
    )

  /** `λx. (x ∥ A) 0 (λh t. h ∥ N)`: x 0, A 1, 0 at 2, N 3; the case reads h 0,
    * t 1, N 2.
    */
  private lazy val head: Configured[encoding.type] =
    val naturals = encoding.application(term("binary_set"), term("true"))
    encoding.thunkOrInstance(
      Code.Apply(
        Code.Apply(Code.Parallel(slot(0), slot(1)), slot(2)),
        Code.Thunk(
          Code.Parallel(slot(0), slot(2)),
          Vector(Hole.Bound(0), Hole.Bound(1)),
          Vector(slot(3))
        )
      ),
      Vector(Hole.Bound(0)),
      Vector(
        encoding.application(term("array_list"), naturals),
        storage(BigInteger.ZERO),
        naturals
      )
    )

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = gezi.jit.TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(
      gezi.jit.JitConfiguration.defaultInstanceTableGeneration
    ),
    budget = gezi.jit.JitConfiguration.defaultBudget,
    checkpoints = CheckpointOption.Profitable,
    nativeBlocks = NativeBlocksOption.None,
    lookahead = LookaheadOption.Lazily,
    instanceReuse = InstanceReuseOption.WithinVersion
  )

  private val readingOptions =
    ReadingOptions(
      ApplicationOption.ByLayer,
      TableSharingOption.Local,
      TableRetentionOption.NoneKept,
      ContinuationOption.Substituted,
      ParallelOption.BothSides
    )

  private def normalForms(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      steps: Long,
      stop: StopSignal
  ): Option[ScottADTChoices.Read[encoding.type]] =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments
      .read(
        executor,
        ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
        program,
        steps,
        stop,
        jit.readingConfiguration
      )
      .read

  /** The steps the reading without group blocks is given. */
  private val machineSteps: Long = 20000L

  /** The share of a reading's budget the group blocks may waste, in percent. */
  private val blockShare: Int = 10

  /** The steps the reading with group blocks is given: its blocks waste at most
    * their share of it, so the machine keeps at least `machineSteps`.
    */
  private val blockSteps: Long =
    (machineSteps * 100 + (100 - blockShare) - 1) / (100 - blockShare)

  /** The program of the head applied to the list of v's without end, read with
    * the group blocks and without them, against v alone.
    */
  private def checked(value: BigInteger, stop: StopSignal): Result =
    val program = encoding.application(head, unending(value))
    val expected =
      normalForms(storage(value), GroupBlocksOption.None, machineSteps, stop)
    Result
      .assert(
        ScottReadingComparison.sameReadings(
          normalForms(
            program,
            GroupBlocksOption.Enabled(sharePercent = blockShare),
            blockSteps,
            stop
          ),
          expected
        ) &&
          ScottReadingComparison.sameReadings(
            normalForms(program, GroupBlocksOption.None, machineSteps, stop),
            expected
          ) &&
          ScottReadingComparison.memberCount(expected).contains(1)
      )
      .log(s"v = $value")

  /** v drawn from 1 to 40, where only the first member reads v. Five
    * iterations: every value exercises the same entry and the same decode
    * point, v's storage being opaque inside them, and a cold JVM's first
    * readings with group blocks cost up to 0.65 s each (2026-11-25), so the
    * default twenty overran the 3 s deadline when the suite ran alone.
    */
  stoppableProperty(
    "a list without end at a block's entry reads its first element, with the group blocks and without them",
    _.copy(testLimit = hedgehog.core.SuccessCount(5))
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for value <- Gen
        .int(Range.linear(1, 40))
        .map(drawn => BigInteger.valueOf(drawn.toLong))
        .forAll
    yield checked(value, stop)
  }

  /** v = 0, one input: the zero constructor's storage, where both members of
    * `(v ∥ N) + (v ∥ N ∥ 0)` read v, so that the one normal form is read once.
    */
  stoppableTest(
    "a list without end of zeros at a block's entry reads zero once, with the group blocks and without them"
  ) { stopped =>
    val result = checked(BigInteger.ZERO, StopSignal.completedWith(stopped))
    assert(result.success, result.logs.mkString("; "))
  }
