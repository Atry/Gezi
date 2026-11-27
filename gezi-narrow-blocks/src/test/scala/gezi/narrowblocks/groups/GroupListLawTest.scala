package gezi.narrowblocks.groups

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Pure
import gezi.ir.Value
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.jit.BinaryNatural
import gezi.jit.BinaryNaturalNatives
import gezi.jit.JitValue
import gezi.jit.Native
import gezi.jit.NativeArgument
import gezi.jit.NativeBackend
import gezi.jit.NativePlace
import gezi.jit.NativeValue
import gezi.jit.Representation
import gezi.jit.StaticBlockMethod
import gezi.jit.StaticBlockResult
import gezi.narrowblocks.lists.NarrowListLibrary
import gezi.saturation.StopSignal
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property

private given groupListLawTestNoFacts: NoFacts.type = NoFacts

/** The laws of lists in a group block (`GroupGrammar`'s array list
  * productions), over the list laws' library (`GroupListLibrary`): among its
  * natives `sum_list` at a place of lists of the canonical naturals,
  * `sum_positive` at one of the positive naturals', and `range`, whose result
  * is a list. N is `binary_set true`, P `binary_set false`, A `array_list N`
  * and A⁺ `array_list P`. Derived from the productions' guarantees and the
  * program's schedule:
  *
  *   - `fixpoint S (x ∥ A) 0 ∥ N`, S summing by a list's branch with an
  *     accumulator, gives the sum, and finishes one call per suffix, n + 1 for
  *     a list of n elements (each call's list is another suffix);
  *   - `fixpoint R (x ∥ A) (nil ∥ A) ∥ A`, R consing each head onto an
  *     accumulator, gives the reversed list, equal by its elements to the list
  *     made of them, n + 1 calls; and the same with a dense table beside the
  *     map (`GroupMemoOption.Dense`), whatever calls it finds in either;
  *   - `cons (x ∥ N) (nil ∥ A⁺) ∥ A⁺` on a group of naturals gives the lists
  *     [v] of its positive members only, and `x ∥ A⁺` on a group of lists the
  *     lists whose every element is positive, deduplicated;
  *   - `sum_list (x ∥ A⁺)` sums a list of positive naturals at a place of the
  *     canonical naturals' lists; `sum_positive (x ∥ A)` compiles no block, a
  *     list of the canonical naturals filling no place of the positive ones';
  *   - `sum_list (range (x ∥ N))` is n (n − 1) / 2, a native's list result read
  *     by another native;
  *   - the JVM array backend gives the scalar backend's outcome, the steps and
  *     the finished calls included, every operation's rows being the scalar
  *     backend's (`JvmArrayGroupBackendLawTest`);
  *   - through the JIT's mechanism, `x ∥ A` on an array list's storage gives
  *     that very storage, and the list's branch's tail `t ∥ A` the very storage
  *     of the suffix after the first element: a list enters and leaves a block
  *     shared, never copied.
  *
  * Their purpose is to catch a list's branch or constructor that does not
  * follow the Scott lists' β rule, a positive list that keeps a zero, a list
  * place filled against its criterion, and a list copied at a block's boundary.
  */
class GroupListLawTest extends GeneratedProperties:

  import NarrowListLibrary.*
  import GroupListLibrary.*

  private given encodingConfiguration: GroupListLibrary.encoding.type =
    GroupListLibrary.encoding

  private lazy val fixpoint: Configured[encoding.type] =
    Configured.fromPure(encoding)(GroupGrammar.fixpointByValue)

  // The library's constants as terms of the backend's encoding: the same objects.
  private lazy val naturalsIn: Configured[encoding.type] = crossed(naturals)
  private lazy val listsIn: Configured[encoding.type] = crossed(lists)
  private lazy val positiveListsIn: Configured[encoding.type] = crossed(
    positiveLists
  )
  private lazy val plusIn: Configured[encoding.type] = crossed(
    NarrowListLibrary.plus
  )
  private lazy val consIn: Configured[encoding.type] = crossed(
    NarrowListLibrary.cons
  )
  private lazy val nilIn: Configured[encoding.type] = crossed(
    NarrowListLibrary.nil
  )
  private lazy val sumListIn: Configured[encoding.type] = crossed(sumList)
  private lazy val sumPositiveIn: Configured[encoding.type] = crossed(
    sumPositive
  )
  private lazy val rangeIn: Configured[encoding.type] = crossed(range)

  /** S: self at slot 0, l at 1, acc at 2, N at 3, A at 4, plus at 5; its cons
    * case reads h 0, t 1, self 2, acc 3, N 4, A 5, plus 6.
    */
  private lazy val summing: Configured[encoding.type] =
    val call = filtered(
      applied(
        Code.Slot(2),
        filtered(Code.Slot(1), Code.Slot(5)),
        applied(
          Code.Slot(6),
          filtered(Code.Slot(0), Code.Slot(4)),
          filtered(Code.Slot(3), Code.Slot(4))
        )
      ),
      Code.Slot(4)
    )
    encoding.thunkOrInstance(
      applied(
        filtered(Code.Slot(1), Code.Slot(4)),
        filtered(Code.Slot(2), Code.Slot(3)),
        consCase(call, 0, 2, 3, 4, 5)
      ),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturalsIn, listsIn, plusIn)
    )

  /** R: self at slot 0, l at 1, acc at 2, N at 3, A at 4, cons at 5; its cons
    * case reads h 0, t 1, self 2, acc 3, N 4, A 5, cons 6.
    */
  private lazy val reversing: Configured[encoding.type] =
    val consed = filtered(
      applied(
        Code.Slot(6),
        filtered(Code.Slot(0), Code.Slot(4)),
        filtered(Code.Slot(3), Code.Slot(5))
      ),
      Code.Slot(5)
    )
    val call = filtered(
      applied(Code.Slot(2), filtered(Code.Slot(1), Code.Slot(5)), consed),
      Code.Slot(5)
    )
    encoding.thunkOrInstance(
      applied(
        filtered(Code.Slot(1), Code.Slot(4)),
        filtered(Code.Slot(2), Code.Slot(4)),
        consCase(call, 0, 2, 3, 4, 5)
      ),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturalsIn, listsIn, consIn)
    )

  /** `λx. fixpoint G (x ∥ A) c ∥ S`: x at slot 0, fixpoint at 1, G at 2, A at
    * 3, S at 4, c at 5.
    */
  private def called(
      recursion: Configured[encoding.type],
      start: Code,
      startFillings: Vector[Configured[encoding.type]],
      result: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.thunkOrInstance(
      filtered(
        applied(
          applied(Code.Slot(1), Code.Slot(2)),
          filtered(Code.Slot(0), Code.Slot(3)),
          start
        ),
        Code.Slot(4)
      ),
      Vector(Hole.Bound(0)),
      Vector(fixpoint, recursion, listsIn, result) ++ startFillings
    )

  private val elements: Gen[Vector[BigInteger]] =
    Gen
      .int(Range.linear(0, 40))
      .list(Range.linear(0, 8))
      .map(_.toVector.map(value => BigInteger.valueOf(value.toLong)))

  stoppableProperty("a sum by a list's branch finishes one call per suffix") {
    stopped =>
      val stop = StopSignal.completedWith(stopped)
      for values <- elements.forAll
      yield
        val found = run(
          stop,
          called(summing, Code.Slot(5), Vector(storage(0)), naturalsIn),
          Vector(listOf(values))
        )
        Result.diff(
          (found.results, found.finishedCalls),
          (
            Some(
              Vector(
                GroupValue.Natural(values.foldLeft(BigInteger.ZERO)(_.add(_)))
              )
            ),
            values.size + 1
          )
        )(_ == _)
  }

  stoppableProperty(
    "a reverse by cons onto an accumulator gives the reversed list"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- elements.forAll
    yield
      // The accumulator's start `nil ∥ A`, at slots 5 and 6.
      val found = run(
        stop,
        called(
          reversing,
          filtered(Code.Slot(5), Code.Slot(6)),
          Vector(nilIn, listsIn),
          listsIn
        ),
        Vector(listOf(values))
      )
      Result.diff(
        (found.results, found.finishedCalls),
        (Some(Vector(listOf(values.reverse))), values.size + 1)
      )(_ == _)
  }

  stoppableProperty(
    "a dense table beside the map gives the outcome of the map alone"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- elements.forAll
    yield
      val reverse = compiled(
        called(
          reversing,
          filtered(Code.Slot(5), Code.Slot(6)),
          Vector(nilIn, listsIn),
          listsIn
        )
      )
      def outcome(memo: GroupMemoOption) =
        val found = GroupRun.run(
          reverse,
          Vector(Vector(listOf(values))),
          ScalarGroupBackend,
          100000000L,
          stop,
          memo
        )
        (found.results, found.finishedCalls)
      Result.diff(
        outcome(GroupMemoOption.Dense(1L << 16)),
        outcome(GroupMemoOption.Mapped)
      )(_ == _)
  }

  stoppableProperty(
    "the JVM array backend gives the scalar backend's outcome, steps and calls included"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- elements.forAll
    yield
      val programs = Vector(
        compiled(called(summing, Code.Slot(5), Vector(storage(0)), naturalsIn)),
        compiled(
          called(
            reversing,
            filtered(Code.Slot(5), Code.Slot(6)),
            Vector(nilIn, listsIn),
            listsIn
          )
        )
      )
      def outcome(backend: GroupBackend) =
        for
          program <- programs
          memo <- Vector(
            GroupMemoOption.Mapped,
            GroupMemoOption.Dense(1L << 16)
          )
        yield
          val found = GroupRun.run(
            program,
            Vector(Vector(listOf(values))),
            backend,
            100000000L,
            stop,
            memo
          )
          (found.results, found.steps, found.finishedCalls, found.denseCalls)
      Result.diff(outcome(JvmArrayGroupBackend), outcome(ScalarGroupBackend))(
        _ == _
      )
  }

  stoppableProperty(
    "under the positive naturals' lists, a zero head or a list holding zero stops the block"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      naturalsGroup <- Gen
        .int(Range.linear(0, 5))
        .list(Range.linear(1, 5))
        .forAll
      listsGroup <- Gen
        .int(Range.linear(0, 5))
        .list(Range.linear(0, 3))
        .list(Range.linear(1, 4))
        .forAll
    yield
      val numbers =
        naturalsGroup.toVector.map(value => BigInteger.valueOf(value.toLong))
      val written = listsGroup.toVector.map(
        _.toVector.map(value => BigInteger.valueOf(value.toLong))
      )
      // cons (x ∥ N) (nil ∥ A⁺) ∥ A⁺: x 0, cons 1, N 2, nil 3, A⁺ 4.
      val consing = block(
        filtered(
          applied(
            Code.Slot(1),
            filtered(Code.Slot(0), Code.Slot(2)),
            filtered(Code.Slot(3), Code.Slot(4))
          ),
          Code.Slot(4)
        ),
        consIn,
        naturalsIn,
        nilIn,
        positiveListsIn
      )
      val filtering =
        block(filtered(Code.Slot(0), Code.Slot(1)), positiveListsIn)
      def ordered(values: Vector[GroupValue]) =
        values.distinct.sorted(using GroupBackend.valueOrdering)
      Result.diff(
        (
          run(stop, consing, numbers.map(GroupValue.Natural(_))).results,
          run(stop, filtering, written.map(listOf)).results
        ),
        (
          // A rejected row is not dropped: the block stops, giving no value.
          Option.when(numbers.forall(_.signum > 0))(
            ordered(numbers.map(value => listOf(Vector(value))))
          ),
          Option.when(written.forall(_.forall(_.signum > 0)))(
            ordered(written.map(listOf))
          )
        )
      )(_ == _)
  }

  stoppableTest(
    "a list of positive naturals fills a place of the canonical naturals' lists, not the other way"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val positiveSum = block(
      applied(Code.Slot(1), filtered(Code.Slot(0), Code.Slot(2))),
      sumListIn,
      positiveListsIn
    )
    val canonicalAtPositive = block(
      applied(Code.Slot(1), filtered(Code.Slot(0), Code.Slot(2))),
      sumPositiveIn,
      listsIn
    )
    val values = Vector(3L, 4L, 5L).map(BigInteger.valueOf)
    assertEquals(
      (
        run(stop, positiveSum, Vector(listOf(values))).results,
        GroupListLibrary.compilation
          .compiled(canonicalAtPositive, encoding.operations)
      ),
      (Some(Vector(GroupValue.Natural(BigInteger.valueOf(12L)))), None)
    )
  }

  stoppableProperty(
    "a native's list result is read by another native: the sum of range n is n (n − 1) / 2"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for n <- Gen.int(Range.linear(0, 50)).forAll
    yield
      // sum_list (range (x ∥ N)): x 0, sum_list 1, range 2, N 3.
      val program = block(
        applied(
          Code.Slot(1),
          applied(Code.Slot(2), filtered(Code.Slot(0), Code.Slot(3)))
        ),
        sumListIn,
        rangeIn,
        naturalsIn
      )
      Result.diff(
        run(
          stop,
          program,
          Vector(GroupValue.Natural(BigInteger.valueOf(n.toLong)))
        ).results,
        Some(
          Vector(GroupValue.Natural(BigInteger.valueOf(n.toLong * (n - 1) / 2)))
        )
      )(
        _ == _
      )
  }

  stoppableProperty(
    "a list enters and leaves the JIT's block as the very storages of its suffixes"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for values <- elements.forAll
    yield
      val representation =
        Representation.ArrayListOf(BinaryNaturalNatives.canonical)
      val operations = encoding.operations
      val written = operations.storageOf(
        representation,
        operations.arrayList(representation, values)
      )
      val mechanism = GroupBlockMechanism(
        GroupListLibrary.compilation,
        facts,
        ScalarGroupBackend
      )
      def blockValue(
          thunk: Configured[encoding.type]
      ): Option[JitValue[encoding.type]] =
        mechanism
          .compiled(thunk, operations)
          .flatMap(artifact => artifact.run(Vector(written), 1000000L, stop))
          .flatMap(_.value)
      // A block of one result gives that result itself, the choice of one member being the member.
      // (x ∥ A) (nil ∥ A) (λh t. t ∥ A): x 0, A 1, nil 2; the case reads h 0, t 1, A 2.
      val tail = block(
        applied(
          filtered(Code.Slot(0), Code.Slot(1)),
          filtered(Code.Slot(2), Code.Slot(1)),
          consCase(filtered(Code.Slot(1), Code.Slot(2)), 1)
        ),
        listsIn,
        nilIn
      )
      val (same, suffix) = (
        blockValue(block(filtered(Code.Slot(0), Code.Slot(1)), listsIn)),
        blockValue(tail)
      )
      val expectedSuffix =
        if values.isEmpty then
          operations.storageOf(
            representation,
            operations.arrayList(representation, Vector.empty)
          )
        else
          written match
            case JitValue.Stored(stored: gezi.jit.ArrayListStorage) =>
              operations.storageOf(
                representation,
                NativeValue.ArrayListed(
                  stored.listed.elements,
                  stored.listed.start + 1
                )
              )
            case other =>
              throw IllegalStateException(
                s"an array list's storage, not $other"
              )
      Result.assert(
        same.exists(Value.same(_, written)) && suffix.exists(
          Value.same(_, expectedSuffix)
        )
      )
  }
