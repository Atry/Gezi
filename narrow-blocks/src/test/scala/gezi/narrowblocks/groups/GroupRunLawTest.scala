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
import gezi.standardlibrary.NativeBound

private given groupRunLawTestNoFacts: NoFacts.type = NoFacts

/** The static method of the halving native: half of an even natural, and no
  * answer (null) on an odd one. Public, since a block calls it by its name.
  */
object GroupRunHalf:
  def halved(value: BigInteger): BigInteger = if value.testBit(0) then null else value.shiftRight(1)

/** The halving native as a block calls it; the laws never run it on an
  * argument vector.
  */
private object GroupRunHalfMethod extends (Vector[NativeArgument] => NativeValue), StaticBlockMethod:
  val className: String = classOf[GroupRunHalf.type].getName.stripSuffix("$")
  val methodName: String = "halved"
  override val result: StaticBlockResult = StaticBlockResult.NaturalOrNoAnswer
  def apply(arguments: Vector[NativeArgument]): NativeValue = Native.outsidePlaces("group_run_half", arguments)

/** The laws of a group block's compilation and run (`GroupCompilation`,
  * `GroupRun`) on the scalar backend, over the narrow lists' test library
  * (`NarrowListLibrary`, whose `plus` is bound to the native
  * `wren_binary_plus` with a static method), and its block
  * `λx. plus (x ∥ N) (x ∥ N)`, N the canonical naturals' criterion
  * `binary_set true`. Derived from the grammar's guarantees: the thunk is a
  * function of one parameter whose body is a native call on two filtered
  * occurrences of x, so it compiles; each occurrence branches over x's
  * group on its own and the native is called on the outer product, so on a
  * group G the block's results are the sums {a + b | a, b ∈ G}, each once:
  * on {1, 2} the four combinations give {2, 3, 4}. And of a native whose
  * static method may answer that there is no normal form
  * (`StaticBlockResult.NaturalOrNoAnswer`), here a half that has none on an
  * odd natural: `λx. half (x ∥ N)` compiles, a group block holding such a
  * result (`GroupCompilation.resultHeld`), and a row on an odd member stops
  * the block (the application has no normal form, but a context consuming
  * it can have an answer), so on a group G of even members it gives their
  * halves, each once, and on a group with an odd member no value. And of the
  * run's steps: an operation's rows are counted before they are made, and a
  * run stops, with the steps spent so far, before an operation whose rows
  * would pass its allowance, or at a stop asked for. On a group of three, the
  * block `λx. plus (x ∥ N) (x ∥ N)` makes 3 rows for each occurrence of x
  * and 3 for each filter, 12; then the join of the two operands within the
  * row, 9, 21; then the native's results, 9: 30 in all. With an allowance
  * of 29 it stops before the native, having spent 21, and with a stop asked
  * for it stops at its first operation, having spent none. Their purpose is to catch a run that ties the two occurrences of one
  * parameter together (giving {2, 4}), keeps duplicates, or loses a
  * combination, a row with no answer dropped or kept as a value, and a run
  * that makes rows past its allowance or past a stop.
  */
class GroupRunLawTest extends GeneratedProperties:

  private val compilation = GroupCompilation(gezi.jit.BackendFacts(NarrowListLibrary.compilation.index, gezi.jit.NativesProvider.loaded))

  /** λx. x (x (x x)), a term of no other name of the library, bound to the
    * halving native.
    */
  private val half: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(0), Code.Apply(Code.Slot(0), Code.Slot(0)))),
      Vector(Hole.Bound(0)),
      Vector.empty
    )

  private val halving = GroupCompilation(gezi.jit.BackendFacts(
    NarrowListLibrary.compilation.index.copy(nativeBound =
      NarrowListLibrary.compilation.index.nativeBound :+ NativeBound(Pure.required(half), "group_run_half")
    ),
    gezi.jit.NativesProvider.loaded.extended(
      NativeBackend.functions(
        Map(
          "group_run_half" -> Native(
            Vector(NativePlace.Fixed(BinaryNaturalNatives.canonical)),
            NativePlace.Fixed(BinaryNaturalNatives.canonical),
            GroupRunHalfMethod
          )
        ),
        Vector.empty
      )
    )
  ))

  private val canonicalCriterion: Configured[NoFacts.type] = NoFacts.application(NarrowListLibrary.binarySet, NarrowListLibrary.truth)

  /** `λx. plus (x ∥ N) (x ∥ N)`: x at slot 0, plus at slot 1, N at slot 2. */
  private val doubled: Configured[NoFacts.type] =
    val filtered = Code.Parallel(Code.Slot(0), Code.Slot(2))
    NoFacts.thunkOrInstance(Code.Apply(Code.Apply(Code.Slot(1), filtered), filtered), Vector(Hole.Bound(0)), Vector(NarrowListLibrary.plus, canonicalCriterion))

  stoppableProperty("a parameter's two occurrences branch apart: the block gives the sums of every pair, each once") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- Gen.int(Range.linear(0, 30)).list(Range.linear(1, 4)).forAll
    yield
      val values = group.distinct.toVector.map(value => BigInteger.valueOf(value.toLong))
      val block = compilation.compiled(doubled)
      val outcome = block.map(compiled =>
        GroupRun.run(compiled, Vector(values.map(GroupValue.Natural(_))), ScalarGroupBackend, 1000000L, stop)
      )
      val sums = (for
        left <- values
        right <- values
      yield left.add(right)).distinct.sorted
      Result.diff(
        outcome.flatMap(_.results),
        Some(sums.map(GroupValue.Natural(_)))
      )(_ == _)
  }

  stoppableTest("on {1, 2} the block gives {2, 3, 4}") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val block = compilation.compiled(doubled).getOrElse(fail("the block compiles"))
    val outcome = GroupRun.run(
      block,
      Vector(Vector(1L, 2L).map(value => GroupValue.Natural(BigInteger.valueOf(value)))),
      ScalarGroupBackend,
      1000000L,
      stop
    )
    assertEquals(outcome.results, Some(Vector(2L, 3L, 4L).map(value => GroupValue.Natural(BigInteger.valueOf(value)))))
  }

  /** `λx. half (x ∥ N)`: x at slot 0, half at slot 1, N at slot 2. */
  private val halved: Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      Code.Apply(Code.Slot(1), Code.Parallel(Code.Slot(0), Code.Slot(2))),
      Vector(Hole.Bound(0)),
      Vector(half, canonicalCriterion)
    )

  stoppableProperty("a row on which a native has no answer stops the block; else the halves of the members") { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- Gen.int(Range.linear(0, 30)).list(Range.linear(1, 4)).forAll
    yield
      val values = group.distinct.toVector.map(value => BigInteger.valueOf(value.toLong))
      val outcome = halving.compiled(halved).map(block =>
        GroupRun.run(block, Vector(values.map(GroupValue.Natural(_))), ScalarGroupBackend, 1000000L, stop)
      )
      Result.diff(
        outcome.flatMap(_.results),
        Option.when(values.forall(!_.testBit(0)))(values.map(_.shiftRight(1)).distinct.sorted.map(GroupValue.Natural(_)))
      )(_ == _)
  }

  stoppableTest("a run stops before an operation whose rows pass its allowance, and at a stop asked for") { stopped =>
    val notStopped = StopSignal.completedWith(stopped)
    val block = compilation.compiled(doubled).getOrElse(fail("the block compiles"))
    val group = Vector(Vector(1L, 2L, 3L).map(value => GroupValue.Natural(BigInteger.valueOf(value))))
    object Stopped extends StopSignal:
      def stopRequested: Boolean = true
    def outcome(allowance: Long, stop: StopSignal) =
      val found = GroupRun.run(block, group, ScalarGroupBackend, allowance, stop)
      (found.results.map(_.size), found.steps)
    assertEquals(
      (outcome(30L, notStopped), outcome(29L, notStopped), outcome(1000000L, Stopped)),
      ((Some(5), 30L), (None, 21L), (None, 0L))
    )
  }
