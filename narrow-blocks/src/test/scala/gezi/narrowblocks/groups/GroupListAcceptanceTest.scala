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
import gezi.saturation.StopSignal

private given groupListAcceptanceTestNoFacts: NoFacts.type = NoFacts

/** The acceptance of recursions over lists in a group block, over the list
  * laws' library (`GroupListLibrary`), each run with the map alone
  * (`GroupMemoOption.Mapped`) and with a dense table beside it
  * (`GroupMemoOption.Dense`), on the scalar backend and on the JVM array
  * backend, which give the same results and counts. Derived from the schedule (a call runs once per
  * key, only a call some row asks for is made, and no branch is entered on a
  * waiting condition) and from the productions' guarantees:
  *
  *  - edit distance, `D a b` reading the head of a then of b and, where they
  *    differ, 1 + the least of `D as b`, `D a bs`, `D as bs`: on lists of 5
  *    and of 7 elements all distinct (④) every pair of suffixes is reached,
  *    6 × 8 = 48 calls under either memo, all 48 in the dense table under
  *    the dense one (every call's lists are suffixes of the two the first
  *    call bound) and none in a dense table under the map; on two equal
  *    lists of 5 (⑤) only the pairs of equal suffixes, 6 calls; on
  *    generated lists, the distance, the same under both memos with the
  *    same calls;
  *  - interleaving, `I a b` the head of a before `I b as`, its arguments
  *    swapped at each call: the interleaved list under both memos, so that a
  *    call whose lists stand in the other dimensions is never found in
  *    another's cell;
  *  - a dense table bound late: `L (cons (L (cons (L (x ∥ A) ∥ N) (nil ∥ A) ∥ A) ∥ N) (nil ∥ A) ∥ A) ∥ N`,
  *    L a list's length by recursion, on x = [5, 6, 7] with a dense table of
  *    3 cells: x's suffixes need 4, so its 4 calls finish in the map; the
  *    call on [3] finds its tail's call there and binds the table, 2 cells;
  *    the call on [1], whose tail is by its elements a suffix of [3] at the
  *    cell no call filled, still finds that tail's call in the map. It gives
  *    1, 6 calls, 1 of them in the dense table, as the map alone does with
  *    none there;
  *  - an accumulator built by cons from a native's results (case G):
  *    `distinct_count (fixpoint G (x ∥ N) (nil ∥ A) ∥ A)`, G consing
  *    `residue n` onto the accumulator for n down to 1, is the count of the
  *    residues modulo 3 of 1 … n, n + 1 calls.
  *
  * Their purpose is to catch a dense table that finds a call in another's
  * cell or misses one the map finds, a schedule that makes calls no row asks
  * for, and an accumulator built inside a block that a list place does not
  * read as its elements.
  */
class GroupListAcceptanceTest extends GeneratedProperties:

  import gezi.narrowblocks.lists.NarrowListLibrary.*
  import GroupListLibrary.*

  private def slot(index: Int): Code = Code.Slot(index)

  /** `λh. b`, h unread, b reading the enclosing code's slots given in order. */
  private def branchCase(body: Code, enclosing: Int*): Code = Code.Thunk(body, Vector(Hole.Ignored), enclosing.toVector.map(slot))

  /** D: self 0, a 1, b 2, N 3, A 4, length 5, equality 6, increment 7,
    * minimum 8. Its case of a cons a reads x 0, as 1, self 2, a 3, b 4, N 5,
    * A 6, length 7, equality 8, increment 9, minimum 10; within it, its case
    * of a cons b reads y 0, bs 1, x 2, as 3, self 4, a 5, b 6, N 7, A 8,
    * equality 9, increment 10, minimum 11.
    */
  private val editDistance: Configured[NoFacts.type] =
    def call(first: Code, second: Code): Code = filtered(applied(slot(4), filtered(first, slot(8)), filtered(second, slot(8))), slot(7))
    val diagonal = call(slot(3), slot(1))
    val bodyB = applied(
      slot(9),
      filtered(slot(2), slot(7)),
      filtered(slot(0), slot(7)),
      diagonal,
      applied(slot(10), applied(slot(11), call(slot(3), slot(6)), applied(slot(11), call(slot(5), slot(1)), diagonal)))
    )
    val bodyA = applied(filtered(slot(4), slot(6)), applied(slot(7), filtered(slot(3), slot(6))), consCase(bodyB, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10))
    NoFacts.thunkOrInstance(
      applied(filtered(slot(1), slot(4)), applied(slot(5), filtered(slot(2), slot(4))), consCase(bodyA, 0, 1, 2, 3, 4, 5, 6, 7, 8)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, lists, length, equality, increment, minimum)
    )

  /** I: self 0, a 1, b 2, N 3, A 4, cons 5; its case of a cons a reads h 0,
    * t 1, self 2, b 3, N 4, A 5, cons 6.
    */
  private val interleaving: Configured[NoFacts.type] =
    val bodyC = filtered(applied(slot(6), filtered(slot(0), slot(4)), filtered(applied(slot(2), filtered(slot(3), slot(5)), filtered(slot(1), slot(5))), slot(5))), slot(5))
    NoFacts.thunkOrInstance(
      applied(filtered(slot(1), slot(4)), filtered(slot(2), slot(4)), consCase(bodyC, 0, 2, 3, 4, 5)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, lists, cons)
    )

  /** G: self 0, n 1, acc 2, N 3, A 4, decrement 5, residue 6, cons 7; its
    * cases read the same slots.
    */
  private val accumulating: Configured[NoFacts.type] =
    val step = filtered(
      applied(slot(0), applied(slot(5), filtered(slot(1), slot(3))), filtered(applied(slot(7), filtered(applied(slot(6), filtered(slot(1), slot(3))), slot(3)), filtered(slot(2), slot(4))), slot(4))),
      slot(4)
    )
    NoFacts.thunkOrInstance(
      applied(filtered(slot(1), slot(3)), filtered(slot(2), slot(4)), branchCase(step, 0, 1, 2, 3, 4, 5, 6, 7), branchCase(step, 0, 1, 2, 3, 4, 5, 6, 7)),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, lists, decrement, residue, cons)
    )

  /** `λx y. fixpoint G (x ∥ A) (y ∥ A) ∥ S`: x 0, y 1, fixpoint 2, G 3, A 4,
    * S 5.
    */
  private def overTwoLists(recursion: Configured[NoFacts.type], result: Configured[NoFacts.type]): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      filtered(applied(applied(slot(2), slot(3)), filtered(slot(0), slot(4)), filtered(slot(1), slot(4))), slot(5)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(GroupGrammar.fixpointByValue, recursion, lists, result)
    )

  /** `λx. distinct_count (fixpoint G (x ∥ N) (nil ∥ A) ∥ A)`: x 0,
    * distinct_count 1, fixpoint 2, G 3, N 4, nil 5, A 6.
    */
  private val countedResidues: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      applied(slot(1), filtered(applied(applied(slot(2), slot(3)), filtered(slot(0), slot(4)), filtered(slot(5), slot(6))), slot(6))),
      Vector(Hole.Bound(0)),
      Vector(distinctCount, GroupGrammar.fixpointByValue, accumulating, naturals, nil, lists)
    )

  /** L: self 0, l 1, N 2, A 3, increment 4, 0 at 5; its cons case reads
    * h 0, t 1, self 2, N 3, A 4, increment 5.
    */
  private val lengthOf: Configured[NoFacts.type] =
    val rest = applied(slot(5), filtered(applied(slot(2), filtered(slot(1), slot(4))), slot(3)))
    NoFacts.thunkOrInstance(
      applied(filtered(slot(1), slot(3)), slot(5), consCase(rest, 0, 2, 3, 4)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, lists, increment, storage(0))
    )

  /** `λx. L (cons (L (cons (L (x ∥ A) ∥ N) (nil ∥ A) ∥ A) ∥ N) (nil ∥ A) ∥ A) ∥ N`:
    * x 0, fixpoint 1, L 2, N 3, A 4, cons 5, nil 6.
    */
  private val nestedLengths: Configured[NoFacts.type] =
    def length(argument: Code): Code = filtered(applied(applied(slot(1), slot(2)), argument), slot(3))
    def single(element: Code): Code = filtered(applied(slot(5), filtered(element, slot(3)), filtered(slot(6), slot(4))), slot(4))
    NoFacts.thunkOrInstance(
      length(single(length(single(length(filtered(slot(0), slot(4))))))),
      Vector(Hole.Bound(0)),
      Vector(GroupGrammar.fixpointByValue, lengthOf, naturals, lists, cons, nil)
    )

  stoppableTest("a dense table bound late still finds the calls the map holds") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val block = compiled(nestedLengths)
    val found = Vector[GroupBackend](ScalarGroupBackend, JvmArrayGroupBackend).map(backend =>
      Vector(GroupMemoOption.Mapped, GroupMemoOption.Dense(3)).map(memo =>
        val outcome = GroupRun.run(block, Vector(Vector(listOf(numbers(Vector(5, 6, 7))))), backend, 1000000L, stop, memo)
        (outcome.results, outcome.finishedCalls, outcome.denseCalls)
      )
    )
    val expected = Vector((Some(Vector(GroupValue.Natural(BigInteger.ONE))), 6, 0), (Some(Vector(GroupValue.Natural(BigInteger.ONE))), 6, 1))
    assertEquals(found, Vector(expected, expected))
  }

  private val memos: Vector[GroupMemoOption] = Vector(GroupMemoOption.Mapped, GroupMemoOption.Dense(1L << 16))

  /** The block's outcomes on the groups, under each memo in order, on the
    * scalar backend, checked to be the JVM array backend's too: results,
    * finished calls and those in a dense table.
    */
  private def runs(stop: StopSignal, thunk: Configured[NoFacts.type], groups: Vector[Vector[GroupValue]]): Vector[GroupOutcome] =
    val block = compiled(thunk)
    def on(backend: GroupBackend) = memos.map(memo => GroupRun.run(block, groups, backend, 100000000L, stop, memo))
    val scalarOutcomes = on(ScalarGroupBackend)
    def counted(found: Vector[GroupOutcome]) = found.map(outcome => (outcome.results, outcome.finishedCalls, outcome.denseCalls))
    assertEquals(counted(on(JvmArrayGroupBackend)), counted(scalarOutcomes))
    scalarOutcomes

  /** The results and finished calls of the block on the groups, under each
    * memo in order.
    */
  private def outcomes(stop: StopSignal, thunk: Configured[NoFacts.type], groups: Vector[Vector[GroupValue]]): Vector[(Option[Vector[GroupValue]], Int)] =
    runs(stop, thunk, groups).map(found => (found.results, found.finishedCalls))

  private def numbers(values: Seq[Int]): Vector[BigInteger] = values.toVector.map(value => BigInteger.valueOf(value.toLong))

  /** Levenshtein's distance, by the same recurrence on suffixes. */
  private def distance(first: Vector[BigInteger], second: Vector[BigInteger]): Int =
    val rows = first.indices.reverse.foldLeft(Vector.tabulate(second.size + 1)(column => second.size - column)) { (below, row) =>
      second.indices.reverse.foldLeft(Vector(first.size - row)) { (built, column) =>
        val value =
          if first(row) == second(column) then below(column + 1)
          else 1 + math.min(below(column), math.min(built.head, below(column + 1)))
        value +: built
      }
    }
    rows.head

  private def interleaved(first: Vector[BigInteger], second: Vector[BigInteger]): Vector[BigInteger] =
    if first.isEmpty then second else first.head +: interleaved(second, first.tail)

  stoppableTest("④ edit distance on lists of 5 and of 7 distinct elements reaches all 48 pairs of suffixes") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val (first, second) = (numbers(0 until 5), numbers(10 until 17))
    assertEquals(
      runs(stop, overTwoLists(editDistance, naturals), Vector(Vector(listOf(first)), Vector(listOf(second))))
        .map(found => (found.results, found.finishedCalls, found.denseCalls)),
      Vector((Some(Vector(GroupValue.Natural(BigInteger.valueOf(7)))), 48, 0), (Some(Vector(GroupValue.Natural(BigInteger.valueOf(7)))), 48, 48))
    )
  }

  stoppableTest("⑤ edit distance on two equal lists of 5 reaches only the 6 pairs of equal suffixes") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val same = numbers(0 until 5)
    assertEquals(
      outcomes(stop, overTwoLists(editDistance, naturals), Vector(Vector(listOf(same)), Vector(listOf(same)))),
      memos.map(_ => (Some(Vector(GroupValue.Natural(BigInteger.ZERO))), 6))
    )
  }

  private val shortLists: Gen[Vector[BigInteger]] = Gen.int(Range.linear(0, 3)).list(Range.linear(0, 5)).map(numbers)

  stoppableProperty("edit distance on generated lists is the distance, the same under both memos") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      first <- shortLists.forAll
      second <- shortLists.forAll
    yield
      val found = outcomes(stop, overTwoLists(editDistance, naturals), Vector(Vector(listOf(first)), Vector(listOf(second))))
      Result.diff(found.map(_._1), memos.map(_ => Some(Vector(GroupValue.Natural(BigInteger.valueOf(distance(first, second).toLong))))))(_ == _)
        .and(Result.diff(found.map(_._2).distinct.size, 1)(_ == _))
  }

  stoppableProperty("interleaving, its arguments swapped at each call, is the interleaved list under both memos") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      first <- shortLists.forAll
      second <- shortLists.forAll
    yield
      val found = outcomes(stop, overTwoLists(interleaving, lists), Vector(Vector(listOf(first)), Vector(listOf(second))))
      Result.diff(found.map(_._1), memos.map(_ => Some(Vector(listOf(interleaved(first, second))))))(_ == _)
  }

  stoppableProperty("case G: an accumulator consed from a native's results is read whole at a list place") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for n <- Gen.int(Range.linear(0, 40)).forAll
    yield Result.diff(
      outcomes(stop, countedResidues, Vector(Vector(GroupValue.Natural(BigInteger.valueOf(n.toLong))))),
      memos.map(_ => (Some(Vector(GroupValue.Natural(BigInteger.valueOf(math.min(n, 3).toLong)))), n + 1))
    )(_ == _)
  }
