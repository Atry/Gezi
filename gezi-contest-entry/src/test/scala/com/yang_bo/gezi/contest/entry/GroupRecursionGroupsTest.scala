package com.yang_bo.gezi.contest.entry

import java.math.BigInteger
import java.nio.file.Paths
import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalNatives
import com.yang_bo.gezi.jit.JitValue
import com.yang_bo.gezi.jit.JvmIntFamily
import com.yang_bo.gezi.jit.JvmIntNatives
import com.yang_bo.gezi.jit.StorageEncoding
import com.yang_bo.gezi.jit.StorageEncodingOperations
import com.yang_bo.gezi.narrowblocks.groups.GroupBackend
import com.yang_bo.gezi.narrowblocks.groups.GroupBlock
import com.yang_bo.gezi.narrowblocks.groups.GroupCompilation
import com.yang_bo.gezi.narrowblocks.groups.GroupGrammar
import com.yang_bo.gezi.narrowblocks.groups.GroupRun
import com.yang_bo.gezi.narrowblocks.groups.GroupValue
import com.yang_bo.gezi.narrowblocks.groups.JvmArrayGroupBackend
import com.yang_bo.gezi.narrowblocks.groups.ScalarGroupBackend
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions

/** A recursion's parameters are group valued: each call is the call on its
  * arguments' groups, every read of a parameter its own member, by the β rule.
  * The expectations are derived before the run from that rule and the schedule
  * (a call runs once per group key; a row whose argument waits makes no call; a
  * row a filter rejects stops the block with no value; a call waiting on a
  * waiting call with nothing ready is a cycle, which stops the block with no
  * value), the same on the scalar and the JVM array group backends. N is the
  * canonical naturals' criterion, P the positive naturals', J `jvm_int_type`;
  * `+` is a choice, `plus` the library's `merge_binary_plus`.
  *
  *   - S k = (k ∥ N) 0 (λh. plus (k ∥ N) (S (h ∥ N) ∥ N)) (the same), which
  *     reads k twice, on {0, 2}: S{0,2} = {0} ∪ {k′ + s | k′ ∈ {0,2}, s ∈
  *     S{1}}, S{1} = {1 + s | s ∈ S{0}} = {1}, so {0, 1, 3}, with the 3 calls
  *     {0,2}, {1}, {0}; per value the blocks gave {0, 3}.
  *   - The words' S k = int32_less_than (k ∥ J) one zero (int32_add (k ∥ J) (S
  *     (int32_subtract (k ∥ J) one ∥ J) ∥ J)), whose test, sum and difference
  *     each read k, on {0, 2}: S{-2,0} = {0} (no call), S{-1,1} = {0} ∪ ({-1,1}
  *     plus S{-2,0}) = {-1, 0, 1}, S{0,2} = {0} ∪ ({0,2} plus {-1,0,1}) = {-1,
  *     0, 1, 2, 3}, with the 3 calls {0,2}, {-1,1}, {-2,0}; -1 the word 2³² −
  *     1, ordered signed by the test.
  *   - S (S (x ∥ N) + 5 ∥ N) on {2}: the argument waits on S{2} = {3}, so it
  *     makes no call before S{2} finishes, then calls S{3,5}: m = 3 gives {3,5}
  *     plus S{1} = {4, 6}, m = 5 gives {3,5} plus S{2} = {6, 8}; so {4, 6, 8}
  *     with the 4 calls {2}, {1}, {0}, {3,5} (a call made in the waiting row
  *     would be a fifth, {5}; the answers would not change, since the waiting
  *     entry is evaluated again).
  *   - T m e = (m ∥ N) 7 (λh. plus (e ∥ N) (T (h ∥ N) (e ∥ P) ∥ N)) (the same)
  *     on m's group {0, 2} and e = 0 ∥ P: the filter P rejects 0 while the
  *     entry computes the call's operands, before any call is made, and a
  *     rejected row stops the block (its term has no answer, but a context
  *     consuming it can have one), so no value and no finished call, marked
  *     rejected.
  *   - f n = (n ∥ N) 0 (λh. f (h ∥ N + 6 ∥ N) ∥ N) (the same), each case's call
  *     on the group {m div 2, 6}: on {0, 4} it asks {2,6}, which asks {1,6} and
  *     {3,6}, which ask {0,6} and {3,6} again; {3,6} waits on itself, every
  *     call waits, so the block stops with no value and no finished call, not
  *     marked rejected: the JIT gives the thunk's block up for a cycle, which
  *     costs a later call that would finish (f on {0} gives {0} with no call)
  *     its speed, not its answers. Per value it cycles too (f 6 calls f 6); a
  *     cycle that only group keys make needs an argument computed from the
  *     whole group by a branch, which the grammar reads neither as an argument
  *     nor through a let.
  *
  * Its purpose is to catch a recursion called per value, a call made in a
  * waiting row, a rejected row dropped instead of stopping the block or a
  * rejection not marked as one (the machine would give the block up), a key
  * that confuses two groups, and a cycle that gives a value.
  */
class GroupRecursionGroupsTest extends com.yang_bo.gezi.generatedinputs.FailFastSuite:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  /** One backend's library read for the laws: its facts' encoding, the
    * configuration the library's terms, the storages and the blocks are terms
    * of, and the compilation of its blocks.
    */
  private class Library(
      val facts: BackendFacts,
      terms: Map[String, Configured[NoFacts.type]]
  ):

    /** The backend's encoding. */
    val encoding: StorageEncoding = facts.storageEncoding

    given encodingConfiguration: encoding.type = encoding

    given access: StorageAccess = StorageAccess.granted()

    def operations: StorageEncodingOperations[encoding.type] =
      encoding.operations

    lazy val compilation: GroupCompilation = GroupCompilation(facts)

    /** A library member as a term of the encoding: the same object as the
      * member read with no facts.
      */
    def term(name: String): Configured[encoding.type] =
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
    def closedTerm(found: JitValue[encoding.type]): Configured[encoding.type] =
      Closed
        .configured(found)
        .getOrElse(throw IllegalStateException(s"a storage is closed: $found"))

    lazy val fixpoint: Configured[encoding.type] =
      Configured.fromPure(encoding)(GroupGrammar.fixpointByValue)

    def compiled(block: Configured[encoding.type]): GroupBlock[encoding.type] =
      compilation
        .compiled(block, operations)
        .getOrElse(throw IllegalStateException(s"the block compiles: $block"))

  private lazy val naturalLibrary =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/group_blocks.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val naturalFacts = BackendFacts.of(naturalLibrary)

  private lazy val naturalTerms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/group_block_terms.lambdalattice",
          Vector(
            "binary_set",
            "merge_binary_plus",
            "true",
            "plover_pair",
            "plover_pair_type",
            "false"
          )
        ),
        Expansions.none
      )
      ._1

  /** The library of the binary naturals, with the terms the laws about them
    * use.
    */
  private final class Naturals(
      facts: BackendFacts,
      terms: Map[String, Configured[NoFacts.type]]
  ) extends Library(facts, terms):

    lazy val naturals: Configured[encoding.type] =
      encoding.application(term("binary_set"), term("true"))

    lazy val positives: Configured[encoding.type] =
      encoding.application(term("binary_set"), term("false"))

    lazy val plus: Configured[encoding.type] = term("merge_binary_plus")

    def natural(value: Long): Configured[encoding.type] =
      closedTerm(
        operations.storageOf(
          BinaryNaturalNatives.canonical,
          BinaryNatural(BigInt(value))
        )
      )

    /** S: self 0, k 1, N 2, plus 3, the constant 0 at 4, the half at 5. */
    lazy val halvesSum: Configured[encoding.type] =
      val step = withHalf(
        applied(
          slot(3),
          filtered(slot(1), slot(2)),
          filtered(applied(slot(0), filtered(slot(5), slot(2))), slot(2))
        ),
        5
      )
      encoding.thunkOrInstance(
        applied(filtered(slot(1), slot(2)), slot(4), step, step),
        Vector(Hole.Bound(0), Hole.Bound(1)),
        Vector(naturals, plus, natural(0))
      )

  private lazy val naturalLibraryRead: Naturals =
    Naturals(naturalFacts, naturalTerms)

  private lazy val wordLibrary =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/jvm_int.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val wordFacts = BackendFacts.of(wordLibrary)

  private lazy val wordTerms: Map[String, Configured[NoFacts.type]] =
    StandardLibrary
      .entryMembers(
        buildRoot,
        TermTable(
          "tests/jit_fixtures/jvm_int_terms.lambdalattice",
          Vector(
            "true",
            "false",
            "boolean_type",
            "word_end",
            "word_cell",
            "word_type",
            "int32_type",
            "jvm_int_type",
            "int32_add",
            "int32_subtract",
            "int32_multiply",
            "int32_negate",
            "int32_equal",
            "int32_less_than"
          )
        ),
        Expansions.none
      )
      ._1

  /** The library of the 32-bit words. */
  private final class Words(
      facts: BackendFacts,
      terms: Map[String, Configured[NoFacts.type]]
  ) extends Library(facts, terms):

    def word(bits: Int): Configured[encoding.type] =
      closedTerm(
        operations.storageOf(JvmIntNatives.jvmInt, JvmIntNatives.value(bits))
      )

  private lazy val wordLibraryRead: Words = Words(wordFacts, wordTerms)

  /** The libraries compiled before the first test, not charged to it. */
  override def beforeAll(): Unit =
    val _ = (naturalLibraryRead.compilation, wordLibraryRead.compilation)

  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(30, "s")

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code =
    arguments.foldLeft(function)(Code.Apply(_, _))

  private def filtered(value: Code, criterion: Code): Code =
    Code.Parallel(value, criterion)

  /** A branch's case binding its half at `half`, the enclosing slots below it
    * read at the same slots.
    */
  private def withHalf(body: Code, half: Int): Code =
    Code.Thunk(body, Vector(Hole.Bound(half)), Vector.tabulate(half)(slot))

  /** The outcome's results as a set, its finished calls, and whether it stopped
    * on a rejected row, on each backend.
    */
  private def outcomes[C <: NativeSpecializer & Singleton](
      stop: StopSignal,
      block: GroupBlock[C],
      arguments: Vector[Vector[GroupValue]]
  ): Vector[(Option[Set[GroupValue]], Int, Boolean)] =
    Vector[GroupBackend](ScalarGroupBackend, JvmArrayGroupBackend).map(
      backend =>
        val outcome = GroupRun.run(block, arguments, backend, 10000000L, stop)
        (outcome.results.map(_.toSet), outcome.finishedCalls, outcome.rejected)
    )

  private def naturalValue(value: Long): GroupValue =
    GroupValue.Natural(BigInteger.valueOf(value))

  private def wordValue(bits: Int): GroupValue =
    GroupValue.IntBits(JvmIntFamily.identity, bits)

  stoppableTest(
    "S on {0, 2} reads k twice, each read its own member: {0, 1, 3} in 3 calls"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    import naturalLibraryRead.{*, given}
    // x 0, N 1, fixpoint 2, S 3.
    val block = encoding.thunkOrInstance(
      filtered(applied(slot(2), slot(3), filtered(slot(0), slot(1))), slot(1)),
      Vector(Hole.Bound(0)),
      Vector(naturals, fixpoint, halvesSum)
    )
    val expected = (Some(Set(0L, 1L, 3L).map(naturalValue)), 3, false)
    assertEquals(
      outcomes(
        stop,
        compiled(block),
        Vector(Vector(naturalValue(0), naturalValue(2)))
      ),
      Vector(expected, expected)
    )
  }

  stoppableTest(
    "the words' S on {0, 2}: {-1, 0, 1, 2, 3} in 3 calls, keyed by groups of ints"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    import wordLibraryRead.{*, given}
    // S: self 0, k 1, J 2, less 3, add 4, subtract 5, one 6, zero 7.
    val wordType = term("jvm_int_type")
    val k = filtered(slot(1), slot(2))
    val recursive = filtered(
      applied(slot(0), filtered(applied(slot(5), k, slot(6)), slot(2))),
      slot(2)
    )
    val sum = encoding.thunkOrInstance(
      applied(slot(3), k, slot(6), slot(7), applied(slot(4), k, recursive)),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(
        wordType,
        term("int32_less_than"),
        term("int32_add"),
        term("int32_subtract"),
        word(1),
        word(0)
      )
    )
    // x 0, J 1, fixpoint 2, S 3.
    val block = encoding.thunkOrInstance(
      filtered(applied(slot(2), slot(3), filtered(slot(0), slot(1))), slot(1)),
      Vector(Hole.Bound(0)),
      Vector(wordType, fixpoint, sum)
    )
    val expected = (Some(Set(-1, 0, 1, 2, 3).map(wordValue)), 3, false)
    assertEquals(
      outcomes(
        stop,
        compiled(block),
        Vector(Vector(wordValue(0), wordValue(2)))
      ),
      Vector(expected, expected)
    )
  }

  stoppableTest(
    "an argument that waits makes no call: S (S x + 5) on {2} is {4, 6, 8} in 4 calls"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    import naturalLibraryRead.{*, given}
    // x 0, N 1, fixpoint 2, S 3, five 4.
    val inner =
      filtered(applied(slot(2), slot(3), filtered(slot(0), slot(1))), slot(1))
    val block = encoding.thunkOrInstance(
      filtered(
        applied(
          slot(2),
          slot(3),
          filtered(Code.Choice(inner, slot(4)), slot(1))
        ),
        slot(1)
      ),
      Vector(Hole.Bound(0)),
      Vector(naturals, fixpoint, halvesSum, natural(5))
    )
    val expected = (Some(Set(4L, 6L, 8L).map(naturalValue)), 4, false)
    assertEquals(
      outcomes(stop, compiled(block), Vector(Vector(naturalValue(2)))),
      Vector(expected, expected)
    )
  }

  stoppableTest(
    "an argument the filter rejects stops the block: T on m {0, 2} and e = 0 ∥ P gives no value, no call"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    import naturalLibraryRead.{*, given}
    // T: self 0, m 1, e 2, N 3, P 4, plus 5, seven 6, the half at 7.
    val step = withHalf(
      applied(
        slot(5),
        filtered(slot(2), slot(3)),
        filtered(
          applied(
            slot(0),
            filtered(slot(7), slot(3)),
            filtered(slot(2), slot(4))
          ),
          slot(3)
        )
      ),
      7
    )
    val readsMOnly = encoding.thunkOrInstance(
      applied(filtered(slot(1), slot(3)), slot(6), step, step),
      Vector(Hole.Bound(0), Hole.Bound(1), Hole.Bound(2)),
      Vector(naturals, positives, plus, natural(7))
    )
    // x 0, N 1, P 2, fixpoint 3, T 4, zero 5.
    val block = encoding.thunkOrInstance(
      filtered(
        applied(
          slot(3),
          slot(4),
          filtered(slot(0), slot(1)),
          filtered(slot(5), slot(2))
        ),
        slot(1)
      ),
      Vector(Hole.Bound(0)),
      Vector(naturals, positives, fixpoint, readsMOnly, natural(0))
    )
    val expected = (None, 0, true)
    assertEquals(
      outcomes(
        stop,
        compiled(block),
        Vector(Vector(naturalValue(0), naturalValue(2)))
      ),
      Vector(expected, expected)
    )
  }

  stoppableTest(
    "calls keyed by groups that come back to a waiting one are a cycle: f on {0, 4} stops with no value"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    import naturalLibraryRead.{*, given}
    // f: self 0, n 1, N 2, zero 3, six 4, the half at 5.
    val step = withHalf(
      filtered(
        applied(
          slot(0),
          filtered(Code.Choice(filtered(slot(5), slot(2)), slot(4)), slot(2))
        ),
        slot(2)
      ),
      5
    )
    val cycling = encoding.thunkOrInstance(
      applied(filtered(slot(1), slot(2)), slot(3), step, step),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, natural(0), natural(6))
    )
    // x 0, N 1, fixpoint 2, f 3.
    val block = encoding.thunkOrInstance(
      filtered(applied(slot(2), slot(3), filtered(slot(0), slot(1))), slot(1)),
      Vector(Hole.Bound(0)),
      Vector(naturals, fixpoint, cycling)
    )
    val expected = (None, 0, false)
    assertEquals(
      outcomes(
        stop,
        compiled(block),
        Vector(Vector(naturalValue(0), naturalValue(4)))
      ),
      Vector(expected, expected)
    )
  }
