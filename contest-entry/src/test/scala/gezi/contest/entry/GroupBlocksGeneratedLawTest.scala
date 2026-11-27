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

/** The consistency law of group blocks on generated programs: a program
  * `(λx. E) (s₁ + … + sₖ)`, the sᵢ storages of distinct naturals and E drawn
  * from a small language of the group grammar's productions, gives through the
  * JIT, with the scalar group backend and with the JVM array group backend, the
  * normal forms of E's values on the group (each value's storage read alone),
  * the reading keeping the compiled block; unless the grammar reads closed code
  * in E (a choice of constants as a native's or a recursion's argument,
  * `plus (0 + 1) x`), which a block does not hold, so that the program compiles
  * no block on either backend. E's values are computed by the language's
  * definition below, on sets of naturals, by the β rule, as the productions'
  * guarantees state them (`GroupGrammar`): each occurrence of x its own member,
  * a native and a choice on every combination, a recursion's call on its
  * argument's group, each read of its parameter its own member (S reads it
  * twice, so `S (0 + 2)` has 1, the branch reading 2 and the sum reading 0).
  * The reading with group blocks off, deprecated, is no reference either: it
  * takes a native call's product outside any block and loses an answer of its
  * own (on `plus x (plus (x + 1) x)` at x = 0 it reads 0 and not 1,
  * https://github.com/Atry/private-overlay/issues/2221). E is one of
  *
  *   - `x ∥ F`, an occurrence of the parameter, each its own branch over x's
  *     group, so two of them make an outer product; F is the program's one
  *     filter of the parameter, the canonical naturals' N or the positive
  *     naturals' P, since the block's entry decodes the parameter in one
  *     representation, and under P the group is of positive naturals, since the
  *     entry decodes the whole group or none (a row-wise fallback is
  *     https://github.com/Atry/private-overlay/issues/2219);
  *   - a storage of a natural written in the block, a constant;
  *   - `merge_binary_plus E E`, a native called row by row;
  *   - `E + E`, a choice, whose members may give the same values, which a block
  *     deduplicates;
  *   - `fixpoint S (E ∥ N) ∥ N`, S k = k + S (k div 2) (S 0 = 0), a recursion
  *     over a binary branch whose cases bind the half, its calls shared across
  *     the rows.
  *
  * The library is `tests/library_fixtures/group_blocks.lambdalattice`, the
  * binary naturals with `merge_binary_plus` bound to the native
  * `wren_binary_plus`.
  *
  * Rows with no answer are the halving native's in `GroupRunLawTest`, on both
  * backends.
  *
  * Its purpose is to catch a production whose block gives other answers than
  * the term, on either backend: a product that loses or repeats a combination,
  * a choice deduplicated wrongly, a filter that keeps a row it should drop or
  * drops one it should keep, a recursion whose shared calls give another call's
  * result.
  */
class GroupBlocksGeneratedLawTest extends GeneratedProperties:

  private val buildRoot = Paths.get(sys.props("gezi.buildRoot"))

  private lazy val library =
    StandardLibrary.compiledAt(
      buildRoot,
      buildRoot.resolve("tests/library_fixtures/group_blocks.lambdalattice"),
      Vector(BackendChecks)
    )

  private lazy val facts = BackendFacts.of(library)

  private lazy val terms: Map[String, Configured[NoFacts.type]] =
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

  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => facts)

  /** Each input reads one program three times; a reading of these programs
    * takes up to about 0.3 s (measured 2026-11-24 on 6 cores at nice 10).
    */
  override val munitTimeout: scala.concurrent.duration.Duration =
    scala.concurrent.duration.Duration(30, "s")

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

  /** `binary_set flag`, its flag the library's `true` or its false. */
  private lazy val naturals: Configured[encoding.type] =
    encoding.application(term("binary_set"), term("true"))

  /** The positive naturals' criterion, `binary_set false`, the library's false,
    * which the backend's facts bind.
    */
  private lazy val positives: Configured[encoding.type] =
    encoding.application(term("binary_set"), term("false"))

  private def storage(value: Long): Configured[encoding.type] =
    closedTerm(
      operations.storageOf(
        BinaryNaturalNatives.canonical,
        BinaryNatural(BigInt(value))
      )
    )

  private def applied(function: Code, arguments: Code*): Code =
    arguments.foldLeft(function)(Code.Apply(_, _))

  private def filtered(value: Code, criterion: Code): Code =
    Code.Parallel(value, criterion)

  /** S's G, S k = k + S (k div 2): self at slot 0, k at 1, N at 2, plus at 3,
    * the constant 0 at 4; each case binds the half at slot 5 and reads the
    * enclosing slots 0 to 4 at the same slots.
    */
  private lazy val halvesSum: Configured[encoding.type] =
    val step = applied(
      Code.Slot(3),
      filtered(Code.Slot(1), Code.Slot(2)),
      filtered(
        applied(Code.Slot(0), filtered(Code.Slot(5), Code.Slot(2))),
        Code.Slot(2)
      )
    )
    val withHalf =
      Code.Thunk(step, Vector(Hole.Bound(5)), Vector.tabulate(5)(Code.Slot(_)))
    encoding.thunkOrInstance(
      applied(
        filtered(Code.Slot(1), Code.Slot(2)),
        Code.Slot(4),
        withHalf,
        withHalf
      ),
      Vector(Hole.Bound(0), Hole.Bound(1)),
      Vector(naturals, term("merge_binary_plus"), storage(0))
    )

  /** An expression of the language, written as code over the block's slots: x
    * at 0, N at 1, P at 2, plus at 3, fixpoint at 4, S at 5, the constants 0,
    * 1, 2 and 5 at 6 to 9, and the parameter's filter, N or P, at 10.
    */
  private enum Expression:
    case Parameter
    case Constant(index: Int)
    case Plus(left: Expression, right: Expression)
    case Either(left: Expression, right: Expression)
    case Recursion(argument: Expression)

    /** Whether the expression reads the parameter. */
    def readsParameter: Boolean = this match
      case Parameter           => true
      case Constant(_)         => false
      case Plus(left, right)   => left.readsParameter || right.readsParameter
      case Either(left, right) => left.readsParameter || right.readsParameter
      case Recursion(argument) => argument.readsParameter

    /** Whether the expression is a choice of constants only. */
    def onlyConstants: Boolean = this match
      case Constant(_)         => true
      case Either(left, right) => left.onlyConstants && right.onlyConstants
      case _                   => false

    /** Whether the grammar reads closed code in the expression, standing where
      * an operand stands (`operand` in `operandPosition`): code whose every
      * slot holds a closed term of no narrow kind, here a choice of constants
      * as a native's or a recursion's argument. A block holds no closed code
      * (it computes nothing at compile time), so the program is no block; a
      * choice standing as an expression reads its constants as constant
      * columns, and a native's call reads its native's slot, which has a kind.
      */
    def closedCode(operandPosition: Boolean): Boolean = this match
      case Parameter | Constant(_) => false
      case Either(left, right)     =>
        (operandPosition && onlyConstants) || left.closedCode(false) || right
          .closedCode(false)
      case Plus(left, right) => left.closedCode(true) || right.closedCode(true)
      case Recursion(argument) => argument.closedCode(true)

    /** The expression's values when x ranges over the group. */
    def values(group: Set[BigInt]): Set[BigInt] = this match
      case Parameter         => group
      case Constant(index)   => Set(BigInt(constants(index)))
      case Plus(left, right) =>
        for a <- left.values(group); b <- right.values(group) yield a + b
      case Either(left, right) => left.values(group) ++ right.values(group)
      case Recursion(argument) => halvesSumOf(argument.values(group))

    def code: Code = this match
      case Parameter           => filtered(Code.Slot(0), Code.Slot(10))
      case Constant(index)     => Code.Slot(6 + index)
      case Plus(left, right)   => applied(Code.Slot(3), left.code, right.code)
      case Either(left, right) => Code.Choice(left.code, right.code)
      case Recursion(argument) =>
        filtered(
          applied(
            applied(Code.Slot(4), Code.Slot(5)),
            filtered(argument.code, Code.Slot(1))
          ),
          Code.Slot(1)
        )

  private val constants: Vector[Long] = Vector(0, 1, 2, 5)

  /** S k = k + S (k div 2), S 0 = 0. */
  /** S's values on a group V, by the β rule (V substituted at both reads of k,
    * each its own member): 0 when V holds 0, and k′ + s for each member m of V
    * above 0, each k′ of V and each s of S on the group of m's half.
    */
  private def halvesSumOf(group: Set[BigInt]): Set[BigInt] =
    (if group.contains(BigInt(0)) then Set(BigInt(0)) else Set.empty[BigInt]) ++
      group
        .filter(_ > 0)
        .flatMap(member =>
          for k <- group; s <- halvesSumOf(Set(member / 2)) yield k + s
        )

  private def expression(depth: Int): Gen[Expression] =
    if depth == 0 then
      Gen.frequency1(
        3 -> Gen.constant(Expression.Parameter),
        1 -> Gen.int(Range.constant(0, 3)).map(Expression.Constant(_))
      )
    else
      val inner = expression(depth - 1)
      Gen.frequency1(
        2 -> expression(0),
        2 -> inner.flatMap(left => inner.map(Expression.Plus(left, _))),
        2 -> inner.flatMap(left => inner.map(Expression.Either(left, _))),
        1 -> inner.map(Expression.Recursion(_))
      )

  private def block(
      body: Expression,
      positiveParameter: Boolean
  ): Configured[encoding.type] =
    encoding.thunkOrInstance(
      body.code,
      Vector(Hole.Bound(0)),
      Vector(
        naturals,
        positives,
        term("merge_binary_plus"),
        Configured.fromPure(encoding)(GroupGrammar.fixpointByValue),
        halvesSum
      ) ++ constants.map(storage) :+
        (if positiveParameter then positives else naturals)
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

  /** The normal forms of the program, and whether the reading kept a compiled
    * block.
    */
  private def readOnce(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      stop: StopSignal
  ): (Option[ScottADTChoices.Read[encoding.type]], Boolean) =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    val read = Judgments.read(
      executor,
      ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
      program,
      1000000L,
      stop,
      jit.readingConfiguration
    )
    val kept = read.executor match
      case executor: gezi.weakhead.ReadingExecutor[?] =>
        executor.jitState match
          case state: gezi.jit.JitRunState[?] =>
            state.groupBlocks.values.exists(_.isDefined)
          case other =>
            throw IllegalStateException(
              s"a reading of the JIT leaves its run state, not $other"
            )
      case other =>
        throw IllegalStateException(
          s"the framework's executor is a reading executor, not $other"
        )
    (read.read, kept)

  private def fewInputs(
      config: hedgehog.core.PropertyConfig
  ): hedgehog.core.PropertyConfig =
    config.copy(testLimit = hedgehog.core.SuccessCount(20))

  stoppableProperty(
    "a generated block gives the term's normal forms on both backends",
    fewInputs
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for
      // A body that reads no parameter is no block (`(λx. c) G` reads no x);
      // one reads x at least once.
      body <- expression(3)
        .map(found =>
          if found.readsParameter then found
          else Expression.Plus(Expression.Parameter, found)
        )
        .forAll
      positiveParameter <- Gen.boolean.forAll
      group <- Gen
        .int(Range.linear(if positiveParameter then 1 else 0, 6))
        .list(Range.linear(1, 3))
        .map(_.distinct.toVector)
        .forAll
    yield
      val program = encoding.application(
        block(body, positiveParameter),
        group
          .map(value => storage(value.toLong))
          .reduceRight(encoding.choice(_, _))
      )
      val expected = body
        .values(group.map(BigInt(_)).toSet)
        .toVector
        .map(value =>
          readOnce(storage(value.toLong), GroupBlocksOption.None, stop)._1
        )
      val found = Vector(
        GroupBlocksOption.Enabled(),
        GroupBlocksOption.Enabled(backend = GroupBackendOption.JvmArray)
      ).map(readOnce(program, _, stop))
      val result =
        if body.closedCode(operandPosition = false) then
          Result.diff(found.map(_._2), Vector(false, false))(_ == _)
        else
          Result.assert(
            found.size == 2 && found.forall((read, kept) =>
              kept && ScottReadingComparison.sameAsUnion(read, expected)
            )
          )
      result.log(body.toString)
  }
