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
import gezi.ir.Value
import java.nio.file.Paths
import gezi.jit.BackendChecks
import gezi.jit.BackendFacts
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.NativeName
import gezi.jit.Representation
import gezi.jit.StorageEncoding
import gezi.jit.StorageEncodingOperations
import gezi.narrowblocks.groups.GroupGrammar
import gezi.saturation.StopSignal
import gezi.standardlibrary.StandardLibrary
import gezi.standardlibrary.TermTable
import gezi.weakhead.Expansions
import gezi.weakhead.ScottADTChoices

/** The laws of the JIT's group blocks on lists written as terms, over the
  * library of tests/library_fixtures/array_list_sums.lambdalattice: the binary
  * naturals and their natives, `merge_binary_plus` bound to the native
  * `wren_binary_plus`, the lists and the array lists, every term the library's
  * own, read from tests/jit_fixtures/array_list_sum_terms.lambdalattice. N is
  * `binary_set true` and A `array_list N`. The program is
  * `(λx. fixpoint S (x ∥ A) 0 ∥ N) L`, S summing a list by its branch with an
  * accumulator through `merge_binary_plus`, and L a list written as the term
  * `cons s₁ (… (cons sₙ nil))`, each sᵢ a storage of a canonical natural. By
  * the β rule the program is the sum of the sᵢ. Derived from the entry's
  * guarantee: the JIT reads L at the block's entry, one head at every layer,
  * into the array list's storage, and the block runs on it and calls the native
  * itself; so the reading finishes with the sum and the machine calls
  * `wren_binary_plus` no time: the sum is the block's.
  *
  * Within the share of a reading's budget the blocks may waste together (half
  * of it), so that the machine reads on from the application when the block
  * does not finish:
  *   - `(λx. (λy. x ∥ N) (fixpoint U (x ∥ N) ∥ N)) s`, U calling itself on
  *     `sum (n ∥ N) 1` without end, reads s within 20,000 steps, as with no
  *     group blocks: the block evaluates its let's value, a new call each
  *     round, until its share runs out, and the machine, which never reads y,
  *     reads s with the rest; with a share of all of them, the block spends
  *     them all and the reading gives no normal form;
  *   - `λx. fixpoint (λself y. self (y ∥ N) ∥ N) (x ∥ N) ∥ N` waits on itself,
  *     a cycle that stops the block, and the JIT reads the application as with
  *     no group blocks;
  *   - sixteen applications of the first block above to sixteen storages, in
  *     one reading of 20,000 steps, read all sixteen, as with no group blocks,
  *     whether the sixteen are one thunk or sixteen thunks (each capturing
  *     another constant, as closures the JIT builds do): the blocks of the
  *     reading spend together at most half its budget, 10,000 steps, and the
  *     machine reads each application in the rest (were each block's share half
  *     of what is left, the sixteenth would have under one step).
  *
  * The waste and the give-ups count against one reading's budget: on one
  * executor, a reading of the summing block on `ones`, whose entry wastes its
  * share (at most 10,000 of the 20,000 steps) and gives the block up, leaves
  * the next reading (a fresh budget) its whole share and the block, so the same
  * summing block is entered on a written list there, wasting nothing, as a
  * reading of blocks that all give a value does.
  *
  * An array list's storage s crosses its own filter whole: the decode point
  * `s ∥ A`, and `((λy. y) s) ∥ A` whose value's head is s, have one head, s
  * itself, so a block's entry hands it over with no cell made and no element
  * read, a block's result to the next block included; and `B (R L)`, R a block
  * reversing the written list L into an array list and B the summing block,
  * reads the sum of L.
  *
  * Their purpose is to catch an entry that does not decode a list written as a
  * term, the case of every list a program writes literally, a block or an entry
  * that spends the steps the machine needs, and a decoding that does not stop.
  */
class GroupBlocksJitListLawTest extends GeneratedProperties:

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code =
    arguments.foldLeft(function)(Code.Apply(_, _))

  private def filtered(value: Code, criterion: Code): Code =
    Code.Parallel(value, criterion)

  private def thunk(code: Code, holes: Int): Configured[encoding.type] =
    encoding.thunkOrInstance(
      code,
      (0 until holes).map(Hole.Bound(_)).toVector,
      Vector.empty
    )

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/array_list_sums.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/array_list_sum_terms.lambdalattice",
          Vector(
            "binary_set",
            "merge_binary_plus",
            "true",
            "nil",
            "cons",
            "list_type",
            "array_list"
          )
        ),
        Expansions.none
      )
      ._1

  /** The library and its facts, compiled before the first test and not charged
    * to it (FailFastSuite).
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => facts)

  /** The backend's encoding, the configuration every program and storage of
    * these laws is a term of.
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

  private lazy val fixpoint: Configured[encoding.type] =
    Configured.fromPure(encoding)(GroupGrammar.fixpointByValue)

  private lazy val cons: Configured[encoding.type] = term("cons")
  private lazy val nil: Configured[encoding.type] = term("nil")
  private lazy val sum: Configured[encoding.type] = term("merge_binary_plus")

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

  /** The reading of the program under the group blocks given, the terms as
    * written.
    */
  private def reading(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      stop: StopSignal,
      steps: Long
  ) =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments.read(
      executor,
      ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
      program,
      steps,
      stop,
      jit.readingConfiguration
    )

  /** The Scott ADT values of the program read under the group blocks given. */
  private def normalForms(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      stop: StopSignal,
      steps: Long = 1000000L
  ): Option[ScottADTChoices.Read[encoding.type]] =
    reading(program, groupBlocks, stop, steps).read

  /** The machine's calls of `wren_binary_plus` in the reading of the program: a
    * block calls its natives itself, out of the machine's counts.
    */
  private def machineSums(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      stop: StopSignal
  ): Long =
    reading(program, groupBlocks, stop, 1000000L).executor match
      case read: gezi.weakhead.ReadingExecutor[?] =>
        read.jitState match
          case state: gezi.jit.JitRunState[?] =>
            state.counts.callsOf(NativeName.Function("wren_binary_plus"))
          case other =>
            throw IllegalStateException(
              s"a reading of the JIT leaves its run state, not $other"
            )
      case other =>
        throw IllegalStateException(
          s"the framework's executor is a reading executor, not $other"
        )

  private def storage(value: BigInteger): Configured[encoding.type] =
    closedTerm(
      operations.storageOf(
        BinaryNaturalNatives.canonical,
        BinaryNatural(BigInt(value))
      )
    )

  private lazy val naturals: Configured[encoding.type] =
    encoding.application(term("binary_set"), term("true"))
  private lazy val lists: Configured[encoding.type] =
    encoding.application(term("array_list"), naturals)

  /** S: self 0, l 1, acc 2, N 3, A 4, sum 5; its cons case reads h 0, t 1, self
    * 2, acc 3, N 4, A 5, sum 6.
    */
  private lazy val summing: Configured[encoding.type] =
    val call = filtered(
      applied(
        slot(2),
        filtered(slot(1), slot(5)),
        applied(slot(6), filtered(slot(0), slot(4)), filtered(slot(3), slot(4)))
      ),
      slot(4)
    )
    encoding.thunkOrInstance(
      applied(
        filtered(slot(1), slot(4)),
        filtered(slot(2), slot(3)),
        Code.Thunk(
          call,
          Vector(Hole.Bound(0), Hole.Bound(1)),
          Vector(0, 2, 3, 4, 5).map(slot)
        )
      ),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, lists, sum)
    )

  /** `λx. fixpoint S (x ∥ A) 0 ∥ N`: x 0, fixpoint 1, S 2, A 3, N 4, 0 at 5. */
  private lazy val block: Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(
        applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3)), slot(5)),
        slot(4)
      ),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, summing, lists, naturals, storage(BigInteger.ZERO))
    )

  private def written(values: Vector[BigInteger]): Configured[encoding.type] =
    values.foldRight(nil)((value, rest) =>
      encoding.application(encoding.application(cons, storage(value)), rest)
    )

  stoppableProperty(
    "a list written as a term is decoded at the block's entry: the reading finishes with its sum"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- Gen
        .int(Range.linear(0, 40))
        .list(Range.linear(0, 6))
        .map(_.toVector.map(value => BigInteger.valueOf(value.toLong)))
        .forAll
    yield
      val program = encoding.application(block, written(values))
      Result.assert(
        ScottReadingComparison.sameReadings(
          normalForms(program, GroupBlocksOption.Enabled(), stop),
          normalForms(
            storage(values.foldLeft(BigInteger.ZERO)(_.add(_))),
            GroupBlocksOption.None,
            stop
          )
        ) && machineSums(program, GroupBlocksOption.Enabled(), stop) == 0L
      )
  }

  /** U: self 0, n 1, N 2, sum 3, 1 at 4. */
  private lazy val unending: Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(
        applied(slot(0), applied(slot(3), filtered(slot(1), slot(2)), slot(4))),
        slot(2)
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, sum, storage(BigInteger.ONE))
    )

  /** `λx. (λy. x ∥ N) (fixpoint U (x ∥ N) ∥ N)`: x 0, N 1, fixpoint 2, U 3; the
    * let's body reads y 0, x 1, N 2.
    */
  private lazy val divergingLet: Configured[encoding.type] =
    encoding.thunkOrInstance(
      applied(
        Code.Thunk(
          filtered(slot(1), slot(2)),
          Vector(Hole.Bound(0)),
          Vector(slot(0), slot(1))
        ),
        filtered(
          applied(applied(slot(2), slot(3)), filtered(slot(0), slot(1))),
          slot(1)
        )
      ),
      Vector(Hole.Bound(0)),
      Vector(naturals, fixpoint, unending)
    )

  stoppableTest(
    "a block whose let's value does not end stops within its share, and the machine reads on"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val program = encoding.application(divergingLet, storage(BigInteger.TWO))
    val found = normalForms(program, GroupBlocksOption.Enabled(), stop, 20000L)
    val whole = normalForms(
      program,
      GroupBlocksOption.Enabled(sharePercent = 100),
      stop,
      20000L
    )
    assertEquals(
      (
        ScottReadingComparison.sameReadings(
          found,
          normalForms(program, GroupBlocksOption.None, stop, 20000L)
        ),
        ScottReadingComparison.memberCount(found).exists(_ > 0),
        ScottReadingComparison.memberCount(whole).exists(_ > 0)
      ),
      (true, true, false)
    )
  }

  /** The list of 1s without end, `fixpoint (λself. cons 1 self)` by value. */
  private lazy val ones: Configured[encoding.type] =
    encoding.application(
      fixpoint,
      encoding.thunkOrInstance(
        applied(slot(1), slot(2), slot(0)),
        Vector(Hole.Bound(0)),
        Vector(cons, storage(BigInteger.ONE))
      )
    )

  /** `divergingLet` with one more filling, the constant v, which its code never
    * reads: another thunk for every v.
    */
  private def divergingLetCapturing(value: Long): Configured[encoding.type] =
    divergingLet.layer match
      case gezi.ir.Thunk(code, holes, fillings) =>
        encoding.thunkOrInstance(
          code,
          holes,
          fillings :+ storage(BigInteger.valueOf(value))
        )
      case other => throw IllegalStateException(s"a thunk, not $other")

  /** The steps the group blocks wasted in the reading the executor ran last. */
  private def waste(executor: Any): Long = executor match
    case reading: gezi.weakhead.ReadingExecutor[?] =>
      reading.jitState match
        case state: gezi.jit.JitRunState[?] => state.wastedGroupBlockSteps
        case other                          =>
          throw IllegalStateException(
            s"a reading of the JIT leaves its run state, not $other"
          )
    case other =>
      throw IllegalStateException(
        s"the framework's executor is a reading executor, not $other"
      )

  /** The readings of two programs in turn on one executor, each within the
    * steps given: each one's normal forms and the steps the group blocks wasted
    * in it.
    */
  private def readingsInTurn(
      first: Configured[encoding.type],
      second: Configured[encoding.type],
      steps: Long,
      stop: StopSignal
  ) =
    val dependencies =
      ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh())
    val jit =
      Defaults.jit(encoding, jitOptions, GroupBlocksOption.Enabled(), access)
    val executor = Defaults.executor(jit, readingOptions)
    val firstRead = Judgments.read(
      executor,
      dependencies,
      first,
      steps,
      stop,
      jit.readingConfiguration
    )
    val secondRead = Judgments.read(
      firstRead.executor,
      dependencies,
      second,
      steps,
      stop,
      jit.readingConfiguration
    )
    Vector(
      (firstRead.read, waste(firstRead.executor)),
      (secondRead.read, waste(secondRead.executor))
    )

  stoppableTest(
    "a reading's waste and give-ups are cleared for the next: the same block is entered there"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val values = Vector(3L, 4L, 5L).map(BigInteger.valueOf)
    val found = readingsInTurn(
      encoding.application(block, ones),
      encoding.application(block, written(values)),
      20000L,
      stop
    )
    assertEquals(
      (
        ScottReadingComparison.sameReadings(
          found(1)._1,
          normalForms(
            storage(BigInteger.valueOf(12L)),
            GroupBlocksOption.None,
            stop
          )
        ),
        found(0)._2 > 0 && found(0)._2 <= 10000L,
        found(1)._2
      ),
      (true, true, 0L)
    )
  }

  stoppableTest(
    "sixteen applications of blocks that stop, of one thunk or of sixteen, leave the machine half the steps"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    def applications(thunk: Long => Configured[encoding.type]) =
      (1 to 16)
        .map(value =>
          encoding.application(
            thunk(value.toLong),
            storage(BigInteger.valueOf(value.toLong))
          )
        )
        .reduceRight(encoding.choice(_, _))
    val found = Vector(
      applications(_ => divergingLet),
      applications(divergingLetCapturing)
    ).map(program =>
      val read = normalForms(program, GroupBlocksOption.Enabled(), stop, 20000L)
      (
        ScottReadingComparison.sameReadings(
          read,
          normalForms(program, GroupBlocksOption.None, stop, 20000L)
        ),
        ScottReadingComparison.memberCount(read)
      )
    )
    assertEquals(found, Vector((true, Some(16)), (true, Some(16))))
  }

  /** The JIT's machine, whose heads are the JIT's own (a storage left a
    * storage, not encoded as the evaluator's heads are).
    */
  private lazy val rulesJit =
    Defaults.jit(encoding, jitOptions, GroupBlocksOption.Enabled(), access)

  private lazy val rules = gezi.jit.JitRules(rulesJit.configuration)

  property(
    "an array list's storage, written or a value's head, is its own decode point's one head"
  ) {
    for values <- Gen
        .int(Range.linear(0, 40))
        .list(Range.linear(0, 6))
        .map(_.toVector.map(value => BigInteger.valueOf(value.toLong)))
        .forAll
    yield
      val representation =
        Representation.ArrayListOf(BinaryNaturalNatives.canonical)
      val stored = operations.storageOf(
        representation,
        operations.arrayList(representation, values)
      )
      val storage = stored match
        case JitValue.Stored(found) => found
        case other                  =>
          throw IllegalStateException(s"an array list is a storage, not $other")
      def onlyItself(written: Configured[encoding.type]): Boolean =
        rules
          .heads(Value.Parallel(Value.of(written), Value.of(lists)))
          .collected
          .result(
            gezi.weakhead.ReadingState
              .knowingTop(1000L, rulesJit.readingConfiguration)
          ) match
          case gezi.weakhead.Computed.Done(found, _) =>
            found.size == 1 && found.forall(head =>
              (head: AnyRef) eq (storage: AnyRef)
            )
          case _ => false
      val identity =
        encoding.thunkOrInstance(slot(0), Vector(Hole.Bound(0)), Vector.empty)
      Result.assert(
        onlyItself(closedTerm(stored)) && onlyItself(
          encoding.application(identity, closedTerm(stored))
        )
      )
  }

  /** R: self 0, l 1, acc 2, A 3, N 4, cons 5; its cons case reads h 0, t 1,
    * self 2, acc 3, A 4, N 5, cons 6.
    */
  private lazy val reversing: Configured[encoding.type] =
    val consed = filtered(
      applied(slot(6), filtered(slot(0), slot(5)), filtered(slot(3), slot(4))),
      slot(4)
    )
    encoding.thunkOrInstance(
      applied(
        filtered(slot(1), slot(3)),
        filtered(slot(2), slot(3)),
        Code.Thunk(
          filtered(
            applied(slot(2), filtered(slot(1), slot(4)), consed),
            slot(4)
          ),
          Vector(Hole.Bound(0), Hole.Bound(1)),
          Vector(0, 2, 3, 4, 5).map(slot)
        )
      ),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(lists, naturals, cons)
    )

  /** `λx. fixpoint R (x ∥ A) (nil ∥ A) ∥ A`: x 0, fixpoint 1, R 2, A 3, nil 4.
    */
  private lazy val reverse: Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(
        applied(
          applied(slot(1), slot(2)),
          filtered(slot(0), slot(3)),
          filtered(slot(4), slot(3))
        ),
        slot(3)
      ),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, reversing, lists, nil)
    )

  stoppableProperty(
    "a block's array list result enters the next block: the reading finishes with the sum"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- Gen
        .int(Range.linear(0, 40))
        .list(Range.linear(0, 6))
        .map(_.toVector.map(value => BigInteger.valueOf(value.toLong)))
        .forAll
    yield Result.assert(
      ScottReadingComparison.sameReadings(
        normalForms(
          encoding
            .application(block, encoding.application(reverse, written(values))),
          GroupBlocksOption.Enabled(),
          stop
        ),
        normalForms(
          storage(values.foldLeft(BigInteger.ZERO)(_.add(_))),
          GroupBlocksOption.None,
          stop
        )
      )
    )
  }

  /** `λx. fixpoint (λself y. self (y ∥ N) ∥ N) (x ∥ N) ∥ N`. */
  private lazy val cycle: Configured[encoding.type] =
    val waiting = encoding.thunkOrInstance(
      filtered(applied(slot(0), filtered(slot(1), slot(2))), slot(2)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals)
    )
    encoding.thunkOrInstance(
      filtered(
        applied(applied(slot(1), slot(2)), filtered(slot(0), slot(3))),
        slot(3)
      ),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, waiting, naturals)
    )

  stoppableTest(
    "a cycle stops the block, and the JIT reads the application as with no group blocks"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val program = encoding.application(cycle, storage(BigInteger.TWO))
    assert(
      ScottReadingComparison.sameReadings(
        normalForms(program, GroupBlocksOption.Enabled(), stop, 20000L),
        normalForms(program, GroupBlocksOption.None, stop, 20000L)
      )
    )
  }
