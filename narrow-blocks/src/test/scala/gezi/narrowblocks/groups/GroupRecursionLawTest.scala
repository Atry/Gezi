package gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult
import gezi.narrowblocks.lists.NarrowListLibrary
import gezi.saturation.StopSignal
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property

private given groupRecursionLawTestNoFacts: NoFacts.type = NoFacts

/** The static method of the decrement native: a natural less one, and no
  * answer (null) on zero. Public, since a block calls it by its name.
  */
object GroupRecursionDecrement:
  def decremented(value: BigInteger): BigInteger = if value.signum == 0 then null else value.subtract(BigInteger.ONE)

/** The decrement native as a block calls it; the laws never run it on an
  * argument vector.
  */
private object GroupRecursionDecrementMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[GroupRecursionDecrement.type].getName.stripSuffix("$")
  val methodName: String = "decremented"
  override val result: StaticBlockResult = StaticBlockResult.NaturalOrNoAnswer
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("group_recursion_decrement", arguments)

/** The laws of a recursion in a group block (`GroupProgram`), over the
  * narrow lists' test library with a decrement native bound by hand and the
  * booleans' constructors by their `data_family`. N is
  * the naturals' criterion `binary_set true`; every parameter of a recursion
  * is under N at its every occurrence, and every call's result under N, the
  * kinds the filters written in the term give. Derived from the program's
  * schedule: a call runs when the calls it waits on have finished, a key
  * once, and an empty round with the entry unfinished is a cycle.
  *
  *  - The countdown `fixpoint G (x ∥ N) 0 ∥ N`,
  *    `G = λself n a. (n ∥ N) (a ∥ N) (λh. c) (λh. c)` with
  *    `c = self (decrement (n ∥ N)) (increment (a ∥ N)) ∥ N`, adds one n
  *    times: it gives n, and finishes the n + 1 calls (n, 0) … (0, n), one key
  *    per level, whatever the depth, on no JVM stack.
  *  - fib, `fixpoint F (x ∥ N) ∥ N` with
  *    `F = λself n. (n ∥ N) 0 (λh. d) (λh. d)` and
  *    `d = (decrement (n ∥ N) ∥ N) 1 (λh. s) (λh. s)`,
  *    `s = plus (self (decrement (n ∥ N)) ∥ N) (self (decrement (decrement (n ∥ N))) ∥ N)`:
  *    it gives fib(n), and finishes the keys 0 … n, n + 1 calls for n ≥ 2
  *    (one for n < 2), a key asked for by two siblings of one round computed
  *    once: siblings waiting on each other are no cycle.
  *  - `fixpoint (λself y. self (y ∥ N) ∥ N) (x ∥ N) ∥ N` waits on itself: a
  *    cycle, which stops the block with no value.
  *
  *  - The countdown reads back from its backend only what the program's
  *    schedule asks, on the scalar and on the JVM array backend alike: with
  *    keys K_i = (n − i, i), 2n + 3 rounds (the entry and each call missing
  *    its callee, the last call finishing, each woken call finishing, the
  *    entry finishing), one column for the argument, one identity call and
  *    one (row, identity) pair in each of the n + 1 rounds with a miss, one
  *    key table in each of the 2n + 1 rounds that evaluate a call, one parent
  *    row read in each of the n rounds whose waiting row is in a branch's
  *    case, and one exit;
  *  - At depth 10⁵ the countdown still finishes its 10⁵ + 1 calls: a
  *    recursion on the JVM's stack, a few frames per level, overflows the
  *    default stack near 10⁴ levels.
  *
  * Their purpose is to catch a recursion run on the JVM's stack, a key
  * computed twice, siblings taken for a cycle, and a cycle not stopped.
  */
class GroupRecursionLawTest extends GeneratedProperties:

  /** The depth law's run, past the default 3 s. Measured 2026-11-24 on 6
    * cores at nice 10, after the memo moved into the backend and the run
    * counts its read backs: warm, 1.7 s, 3.6 s and 7.0 s at depths 25 000,
    * 50 000 and 10⁵, linear, about 70 µs a level (two evaluations of the
    * body and their tables, a lookup, an identity and a store); the cold run
    * at 10⁵ took 11.2 s to 14.3 s with the suite alone and 17.6 s beside two
    * other suites in the same test JVM. The limit is the slowest reading
    * with a margin of a third.
    *
    * Where the time goes, by a JFR profile of the suite (2026-11-24, 555
    * samples in the group code): the program's own frames, those with no
    * frame of the backend above them (`GroupProgram`'s rounds, schedule,
    * relations and waits) 43%; the scalar backend's table operations (joins,
    * filters' computations, the rows, selections, the deduplication of every
    * relation the program makes, table construction) about 45%; the memo's lookups, identities and stores 5%;
    * looking up a native's method handle at every call of a table 3%, which
    * is now looked up once per method (`GroupMethod.handle`). No other part
    * is overhead that can go: the levels' cost is the scalar backend's
    * table per level.
    */
  override val munitTimeout: scala.concurrent.duration.Duration = scala.concurrent.duration.Duration(24, "s")

  import NarrowListLibrary.*

  /** λx y z. z (y x) x, a term of no other name of the library, bound to the
    * decrement native.
    */
  private val decrement: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Apply(Code.Slot(2), Code.Apply(Code.Slot(1), Code.Slot(0))), Code.Slot(0)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector.empty
    )

  private val compilation = GroupCompilation(gezi.jit.BackendFacts(
    NarrowListLibrary.compilation.index.copy(
      nativeBound = NarrowListLibrary.compilation.index.nativeBound :+ NativeBound(Pure.required(decrement), "group_recursion_decrement"),
      // The booleans' constructors, which a storage's criterion `binary_set true` is spelled with.
      combinatorProperties = NarrowListLibrary.compilation.index.combinatorProperties :+
        CombinatorProperty(Pure.required(booleanType), Property.DataFamily(0, Vector(truth, falsity).map(Pure.required)))
    ),
    gezi.jit.NativesProvider.loaded.extended(
      NativeBackend.functions(
        Map(
          "group_recursion_decrement" -> Native(
            Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical)),
            NativePlace.Fixed(BinaryNaturalNatives.canonical),
            GroupRecursionDecrementMethod
          )
        ),
        Vector.empty
      )
    )
  ))

  private val encoding: gezi.jit.StorageEncoding = compilation.facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  /** A pure term of the library as a term of the backend's encoding: the same object. */
  private def crossed(term: Configured[NoFacts.type]): Configured[encoding.type] = Configured.fromPure(encoding)(Pure.required(term))

  private lazy val fixpoint: Configured[encoding.type] = Configured.fromPure(encoding)(GroupGrammar.fixpointByValue)

  private val naturals: Configured[encoding.type] = encoding.application(crossed(binarySet), crossed(truth))

  private def storage(value: Long): Configured[encoding.type] =
    gezi.ir.Closed
      .configured(encoding.operations.storageOf(BinaryNaturalNatives.canonical, BinaryNatural(BigInt(value))))
      .getOrElse(throw IllegalStateException(s"the storage of $value holds a suspension"))

  private def applied(function: Code, arguments: Code*): Code = arguments.foldLeft(function)(Code.Apply(_, _))

  private def filtered(value: Code, criterion: Code): Code = Code.Parallel(value, criterion)

  /** `λh. b`, h unread, the code b over the enclosing code's slots given as
    * the inner thunk's fillings, in order.
    */
  private def branchCase(body: Code, enclosing: Int*): Code =
    Code.Thunk(body, Vector(Hole.Ignored), enclosing.toVector.map(Code.Slot(_)))

  /** The countdown's G: self at slot 0, n at 1, a at 2, N at 3, decrement at
    * 4, increment at 5; its cases read self, n, a, N, decrement and
    * increment at their slots 0 to 5.
    */
  private val countdown: Configured[encoding.type] =
    val call = filtered(
      applied(Code.Slot(0), applied(Code.Slot(4), filtered(Code.Slot(1), Code.Slot(3))), applied(Code.Slot(5), filtered(Code.Slot(2), Code.Slot(3)))),
      Code.Slot(3)
    )
    encoding.thunkOrInstance(
      applied(filtered(Code.Slot(1), Code.Slot(3)), filtered(Code.Slot(2), Code.Slot(3)), branchCase(call, 0, 1, 2, 3, 4, 5), branchCase(call, 0, 1, 2, 3, 4, 5)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, crossed(decrement), crossed(increment))
    )

  /** fib's F: self at slot 0, n at 1, N at 2, decrement at 3, plus at 4,
    * zero at 5, one at 6; its cases read them at the same slots.
    */
  private val fibonacci: Configured[encoding.type] =
    val lessOne = applied(Code.Slot(3), filtered(Code.Slot(1), Code.Slot(2)))
    val sum = applied(
      Code.Slot(4),
      filtered(applied(Code.Slot(0), lessOne), Code.Slot(2)),
      filtered(applied(Code.Slot(0), applied(Code.Slot(3), lessOne)), Code.Slot(2))
    )
    val afterZero = applied(filtered(lessOne, Code.Slot(2)), Code.Slot(6), branchCase(sum, 0, 1, 2, 3, 4, 5, 6), branchCase(sum, 0, 1, 2, 3, 4, 5, 6))
    encoding.thunkOrInstance(
      applied(filtered(Code.Slot(1), Code.Slot(2)), Code.Slot(5), branchCase(afterZero, 0, 1, 2, 3, 4, 5, 6), branchCase(afterZero, 0, 1, 2, 3, 4, 5, 6)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, crossed(decrement), crossed(plus), storage(0), storage(1))
    )

  /** `λself y. self (y ∥ N) ∥ N`: self at slot 0, y at 1, N at 2. */
  private val looping: Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(applied(Code.Slot(0), filtered(Code.Slot(1), Code.Slot(2))), Code.Slot(2)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals)
    )

  /** `λx. fixpoint G (x ∥ N) c⃗ ∥ N`, the constants c⃗ after x: x at slot 0,
    * fixpoint at 1, G at 2, N at 3, the constants from 4.
    */
  private def called(recursion: Configured[encoding.type], constants: Configured[encoding.type]*): Configured[encoding.type] =
    val arguments = filtered(Code.Slot(0), Code.Slot(3)) +: constants.indices.map(position => Code.Slot(4 + position))
    encoding.thunkOrInstance(
      filtered(applied(applied(Code.Slot(1), Code.Slot(2)), arguments*), Code.Slot(3)),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, recursion, naturals) ++ constants
    )

  private def outcome(stop: StopSignal, block: Configured[encoding.type], value: Long): GroupOutcome =
    val compiled = compilation.compiled(block, encoding.operations).getOrElse(throw IllegalStateException(s"the block compiles: $block"))
    GroupRun.run(compiled, Vector(Vector(GroupValue.Natural(BigInteger.valueOf(value)))), ScalarGroupBackend, 1000000000L, stop)

  private def fibonacciOf(n: Int): BigInteger =
    (0 until n).foldLeft((BigInteger.ZERO, BigInteger.ONE))((pair, _) => (pair._2, pair._1.add(pair._2)))._1

  stoppableProperty("the countdown adds one n times, finishing one call per level") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for n <- Gen.int(Range.linear(0, 200)).forAll
    yield
      val found = outcome(stop, called(countdown, storage(0)), n.toLong)
      Result.diff((found.results, found.finishedCalls), (Some(Vector(GroupValue.Natural(BigInteger.valueOf(n.toLong)))), n + 1))(_ == _)
  }

  stoppableProperty("the countdown reads back only control data, the counts derived from its schedule, on both backends") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for n <- Gen.int(Range.linear(0, 60)).forAll
    yield
      val compiled = compilation.compiled(called(countdown, storage(0)), encoding.operations).getOrElse(throw IllegalStateException("the countdown compiles"))
      def readBacks(backend: GroupBackend) =
        GroupRun.run(compiled, Vector(Vector(GroupValue.Natural(BigInteger.valueOf(n.toLong)))), backend, 1000000000L, stop).readBacks
      // The keys are K_i = (n − i, i). Round 1: the entry misses K_0 and
      // waits. Rounds 2 to n + 1: K_(i−1) misses K_i in its branch's case and
      // waits. Round n + 2: K_n takes the zero branch and finishes. Rounds
      // n + 3 to 2n + 2: each woken call finds its callee and finishes. Round
      // 2n + 3: the entry finds K_0 and gives its result.
      val expected = GroupReadBacks(
        rounds = 2L * n + 3,
        entryColumns = 1,
        identityCalls = n + 1L,
        identityPairs = n + 1L,
        keyTables = 2L * n + 1,
        parentReads = n.toLong,
        parentRows = n.toLong,
        exits = 1
      )
      Result.diff((readBacks(ScalarGroupBackend), readBacks(JvmArrayGroupBackend)), (expected, expected))(_ == _)
  }

  stoppableProperty("fib computes each key once: siblings waiting on each other are no cycle") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for n <- Gen.int(Range.linear(0, 30)).forAll
    yield
      val found = outcome(stop, called(fibonacci), n.toLong)
      Result.diff((found.results, found.finishedCalls), (Some(Vector(GroupValue.Natural(fibonacciOf(n)))), if n >= 2 then n + 1 else 1))(_ == _)
  }

  /** A's G, A k = k: self at slot 0, k at 1, N at 2, decrement at 3,
    * increment at 4, zero at 5; zero gives 0, the other cases
    * `increment (self (decrement (k ∥ N)) ∥ N)`, reading the same slots.
    */
  private val identityRecursion: Configured[encoding.type] =
    val call = applied(Code.Slot(4), filtered(applied(Code.Slot(0), applied(Code.Slot(3), filtered(Code.Slot(1), Code.Slot(2)))), Code.Slot(2)))
    encoding.thunkOrInstance(
      applied(filtered(Code.Slot(1), Code.Slot(2)), Code.Slot(5), branchCase(call, 0, 1, 2, 3, 4, 5), branchCase(call, 0, 1, 2, 3, 4, 5)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, crossed(decrement), crossed(increment), storage(0))
    )

  /** B's G, B k = A (increment k): self at slot 0 (unread), k at 1, fixpoint
    * at 2, A's G at 3, N at 4, increment at 5.
    */
  private val shiftedRecursion: Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(applied(applied(Code.Slot(2), Code.Slot(3)), applied(Code.Slot(5), filtered(Code.Slot(1), Code.Slot(4)))), Code.Slot(4)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(fixpoint, identityRecursion, naturals, crossed(increment))
    )

  /** `λx. fixpoint A (x ∥ N) ∥ N + fixpoint B (x ∥ N) ∥ N`: x at slot 0,
    * fixpoint at 1, A at 2, B at 3, N at 4.
    */
  private val twoRecursions: Configured[encoding.type] =
    def call(recursion: Int): Code = filtered(applied(applied(Code.Slot(1), Code.Slot(recursion)), filtered(Code.Slot(0), Code.Slot(4))), Code.Slot(4))
    encoding.thunkOrInstance(
      Code.Choice(call(2), call(3)),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, identityRecursion, shiftedRecursion, naturals)
    )

  stoppableTest("two recursions in one block, one calling the other, give A 1 and B 1 = A 2, on both backends") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    // A k = k, B k = A (k + 1); at x = 1 the results are {1, 2}, and the
    // finished calls A 0, A 1, A 2 and B 1, A 1 shared by both paths.
    val compiled = compilation.compiled(twoRecursions, encoding.operations).getOrElse(throw IllegalStateException("the two recursions compile as one block"))
    val found = Vector[GroupBackend](ScalarGroupBackend, JvmArrayGroupBackend).map(backend =>
      val outcome = GroupRun.run(compiled, Vector(Vector(GroupValue.Natural(BigInteger.ONE))), backend, 1000000L, stop)
      (outcome.results, outcome.finishedCalls)
    )
    val expected = (Some(Vector(GroupValue.Natural(BigInteger.ONE), GroupValue.Natural(BigInteger.TWO))), 4)
    assertEquals(found, Vector(expected, expected))
  }

  stoppableTest("a call waiting on itself is a cycle, which stops the block with no value") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    assertEquals(outcome(stop, called(looping), 3L).results, None)
  }

  stoppableTest("at depth 10⁵ the countdown finishes, on no JVM stack") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val found = outcome(stop, called(countdown, storage(0)), 100000L)
    assertEquals((found.results, found.finishedCalls), (Some(Vector(GroupValue.Natural(BigInteger.valueOf(100000L)))), 100001))
  }
