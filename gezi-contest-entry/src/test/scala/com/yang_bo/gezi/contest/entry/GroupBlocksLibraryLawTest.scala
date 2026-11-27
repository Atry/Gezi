package com.yang_bo.gezi.contest.entry

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import java.math.BigInteger
import java.nio.file.Paths
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.hotspot.ExecutionDependencies
import com.yang_bo.gezi.hotspot.ExpansionSource
import com.yang_bo.gezi.ir.Closed
import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Pure
import com.yang_bo.gezi.ir.StorageAccess
import com.yang_bo.gezi.ir.Value
import com.yang_bo.gezi.jit.BackendChecks
import com.yang_bo.gezi.jit.BackendFacts
import com.yang_bo.gezi.jit.BinaryNatural
import com.yang_bo.gezi.jit.BinaryNaturalNatives
import com.yang_bo.gezi.jit.ConstructedNaturals
import com.yang_bo.gezi.jit.CriterionParameters
import com.yang_bo.gezi.jit.FamilyIdentity
import com.yang_bo.gezi.jit.JitValue
import com.yang_bo.gezi.jit.Representation
import com.yang_bo.gezi.jit.StorageEncoding
import com.yang_bo.gezi.jit.StorageEncodingOperations
import com.yang_bo.gezi.narrowblocks.groups.GroupCompilation
import com.yang_bo.gezi.narrowblocks.groups.GroupResult
import com.yang_bo.gezi.narrowblocks.groups.GroupRun
import com.yang_bo.gezi.narrowblocks.groups.GroupValue
import com.yang_bo.gezi.narrowblocks.groups.ScalarGroupBackend
import com.yang_bo.gezi.saturation.StopSignal
import com.yang_bo.gezi.standardlibrary.StandardLibrary
import com.yang_bo.gezi.standardlibrary.TermTable
import com.yang_bo.gezi.weakhead.Expansions
import com.yang_bo.gezi.weakhead.ScottADTChoices

/** The laws of a group block whose values are a declared family's, over a
  * library compiled from `tests/library_fixtures/group_blocks.lambdalattice`:
  * the binary naturals and their natives, and the pair family
  * `plover_pair_type`, of one constructor `plover_pair` whose two fields are
  * the family's parameters (`data_fields`). The block is
  * `λx. plover_pair (x ∥ N) (x ∥ N) ∥ plover_pair_type N N`, N the canonical
  * naturals' criterion `binary_set true`, the library's `true`, which the
  * backend binds as the constructor of three codecs (the big integers' zero,
  * the booleans' true, the lists' nil), read by its place: as the booleans'
  * true, the argument of `binary_set`, whose parameter is a boolean. Derived
  * from the grammar's
  * declared family production and its guarantee: the constructor is the
  * family's, applied to its two fields, and filtered by the family's
  * criterion at two parameters each N, under which each field's
  * representation is the canonical naturals', so the block compiles, its
  * values the family's at that filter; each occurrence of x branches over
  * x's group on its own, so on a group G of distinct naturals it gives
  * |G|² pairs, every (a, b) of G × G once, 9 on 3 values; and the JIT,
  * which builds each pair by its construction, gives the normal forms it
  * gives with no group blocks, 9 distinct ones on 3 values. And
  * `λx. merge_binary_plus (x ∥ N) true`, `true` at a place of naturals,
  * which the place names as no boolean and where the block reads a closed
  * term only as a storage, compiles no block.
  *
  * And a group storage, `(s1 + … + sk) ∥ N` as the converting
  * construction spells it, is read at the entry as its k members.
  *
  * Their purpose is to catch a declared family's value the grammar does not
  * read, fields tied together or lost, a pair built by the mechanism that
  * differs from the application's, a criterion's boolean read by the
  * order of a name's bindings, and a name of several families read as a
  * natural at a place that does not name its family.
  */
class GroupBlocksLibraryLawTest extends GeneratedProperties:

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

  private lazy val canonicalCriterion: Configured[encoding.type] =
    encoding.application(term("binary_set"), term("true"))

  private lazy val pairFilter: Configured[encoding.type] = encoding.application(
    encoding.application(term("plover_pair_type"), canonicalCriterion),
    canonicalCriterion
  )

  /** The pair family's criterion at two parameters each the canonical
    * naturals', as the grammar writes it.
    */
  private lazy val pairRepresentation: Representation[Nothing] =
    Representation.Data(
      FamilyIdentity.Declared(
        Pure.required(
          terms.getOrElse(
            "plover_pair_type",
            throw IllegalArgumentException("no member plover_pair_type")
          )
        )
      ),
      Some(CriterionParameters(Vector.fill(2)(BinaryNaturalNatives.canonical)))
    )

  /** `λx. plover_pair (x ∥ N) (x ∥ N) ∥ plover_pair_type N N`: x at slot 0,
    * plover_pair at slot 1, N at slot 2, the pair's filter at slot 3.
    */
  private lazy val paired: Configured[encoding.type] =
    val filtered = Code.Parallel(Code.Slot(0), Code.Slot(2))
    encoding.thunkOrInstance(
      Code.Parallel(
        Code.Apply(Code.Apply(Code.Slot(1), filtered), filtered),
        Code.Slot(3)
      ),
      Vector(Hole.Bound(0)),
      Vector(term("plover_pair"), canonicalCriterion, pairFilter)
    )

  private lazy val compilation = GroupCompilation(facts)

  /** The library compiled before the first test, about 2.5 s, which a test's 3
    * s deadline does not cover.
    */
  override def sharedFixtures: Vector[scala.concurrent.Future[Unit] => Any] =
    Vector(_ => terms, _ => compilation)

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = false,
    instanceTableTrial = com.yang_bo.gezi.jit.TableCost.trial,
    instanceRetention = InstanceRetentionOption.Generations(
      com.yang_bo.gezi.jit.JitConfiguration.defaultInstanceTableGeneration
    ),
    budget = com.yang_bo.gezi.jit.JitConfiguration.defaultBudget,
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

  /** The normal forms of the program the JIT reads under the converting
    * construction and the group blocks given.
    */
  private def normalForms(
      program: Configured[encoding.type],
      groupBlocks: GroupBlocksOption,
      stop: StopSignal
  ): Option[ScottADTChoices.Read[encoding.type]] =
    val jit = Defaults.jit(encoding, jitOptions, groupBlocks, access)
    val executor = Defaults.executor(jit, readingOptions)
    Judgments
      .read(
        executor,
        ExecutionDependencies(Defaults.caches(), ExpansionSource.fresh()),
        program,
        1000000L,
        stop,
        jit.readingConfiguration
      )
      .read

  private def storage(value: BigInteger): Configured[encoding.type] =
    closedTerm(
      operations.storageOf(
        BinaryNaturalNatives.canonical,
        BinaryNatural(BigInt(value))
      )
    )

  private val values: Gen[Vector[BigInteger]] =
    Gen
      .int(Range.linear(0, 30))
      .list(Range.linear(1, 4))
      .map(_.distinct.toVector.map(value => BigInteger.valueOf(value.toLong)))

  test("the pair block compiles, its values the pair family's at its filter") {
    assertEquals(
      compilation.compiled(paired, operations).map(_.result),
      Some(
        GroupResult.Constructed(
          FamilyIdentity.Declared(
            Pure.required(
              terms.getOrElse(
                "plover_pair_type",
                throw IllegalArgumentException("no member plover_pair_type")
              )
            )
          ),
          pairRepresentation
        )
      )
    )
  }

  stoppableProperty(
    "each occurrence branches on its own: the block gives every pair of the group once"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    for group <- values.forAll
    yield
      val block = compilation
        .compiled(paired, operations)
        .getOrElse(throw IllegalStateException("the pair block compiles"))
      val pairs = (for
        first <- group
        second <- group
      yield GroupValue.Constructed(
        ConstructedNaturals(0, Vector(first, second))
      )).sorted(using com.yang_bo.gezi.narrowblocks.groups.GroupBackend.valueOrdering)
      Result.diff(
        GroupRun
          .run(
            block,
            Vector(group.map(GroupValue.Natural(_))),
            ScalarGroupBackend,
            1000000L,
            stop
          )
          .results,
        Some(pairs)
      )(_ == _)
  }

  test(
    "a group storage, the converting construction's spelling of a choice of storages filtered, is read as its members"
  ) {
    val members = Vector(1L, 2L, 3L).map(value => BigInteger.valueOf(value))
    val chosen: Configured[encoding.type] =
      members.map(storage).reduceRight(encoding.choice(_, _))
    val written = Value.Parallel(Value.of(chosen), Value.of(canonicalCriterion))
    assertEquals(
      com.yang_bo.gezi.narrowblocks.groups.GroupBlockMechanism
        .group(written)
        .map(
          _.sorted(using com.yang_bo.gezi.narrowblocks.groups.GroupBackend.valueOrdering)
        ),
      Some(members.sorted.map(GroupValue.Natural(_)))
    )
  }

  test("`true` at a place of naturals compiles no block") {
    val block = encoding.thunkOrInstance(
      Code.Apply(
        Code.Apply(Code.Slot(1), Code.Parallel(Code.Slot(0), Code.Slot(2))),
        Code.Slot(3)
      ),
      Vector(Hole.Bound(0)),
      Vector(term("merge_binary_plus"), canonicalCriterion, term("true"))
    )
    assert(compilation.compiled(block, operations).isEmpty)
  }

  stoppableTest(
    "on three values the JIT with the scalar group blocks gives the 9 pairs, as with no group blocks"
  ) { stopped =>
    val stop = StopSignal.completedWith(stopped)
    val program = encoding.application(
      paired,
      Vector(1L, 2L, 3L)
        .map(value => storage(BigInteger.valueOf(value)))
        .reduceRight(encoding.choice(_, _))
    )
    val withBlocks = normalForms(program, GroupBlocksOption.Enabled(), stop)
    assertEquals(
      (
        ScottReadingComparison.memberCount(withBlocks),
        ScottReadingComparison.sameReadings(
          withBlocks,
          normalForms(program, GroupBlocksOption.None, stop)
        )
      ),
      (Some(9), true)
    )
  }
