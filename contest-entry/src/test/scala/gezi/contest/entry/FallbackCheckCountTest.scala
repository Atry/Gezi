package gezi.contest.entry

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.Configured
import gezi.ir.NoFacts
import gezi.ir.Pure
import gezi.ir.Value
import gezi.jit.BackendFacts
import gezi.jit.DeclaredFamilies
import gezi.jit.JitRunState
import gezi.jit.NativesProvider
import gezi.jit.StorageEncoding
import gezi.standardlibrary.CombinatorProperty
import gezi.standardlibrary.NativeBound
import gezi.standardlibrary.Property
import gezi.standardlibrary.StandardLibraryIndex
import gezi.weakhead.Computed
import gezi.weakhead.Mode
import gezi.weakhead.ReadingState
import gezi.weakhead.WeakHead

private given fallbackCheckCountTestNoFacts: NoFacts.type = NoFacts

/** The cost of a fallback point's check read again: a define bound to
  * `wren_binary_plus`, nested d deep,
  * `plus (… (plus (x + (x ∥ N)) (x + (x ∥ N))) …) (x + (x ∥ N))`, every
  * argument a fallback point by the canonical naturals' criterion N, and
  * `x = λy. y`, which is no binary natural, so that no check holds. The JIT,
  * its instance table on, reads the program to its first heads only (its normal
  * forms do not end), and `JitCounts.fallbackChecks` counts the checks.
  *
  * Derived before the run (#2261's acceptance, "代价"): each level calls `plus`'s
  * native application once, whose two arguments are each checked once
  * (`fallbackOutcome`); a check that does not hold reads the define instead,
  * whose body reads its arguments again, and a second read of a checked operand
  * replays its heads from the table of checked heads (`CheckedHeads`) and runs
  * no check. The first argument's check reads the level below, so each level is
  * read once: 2d checks, 8 for d = 4 and 16 for d = 8. A differing count is a
  * defect or a fault in this derivation, investigated before anything else. Its
  * purpose is to catch a check run again at every read of its operand, the cost
  * the deleted `Evaluated` layer saved and its table keeps.
  */
class FallbackCheckCountTest extends gezi.generatedinputs.FailFastSuite:

  private def slot(index: Int): Code = Code.Slot(index)

  private def applied(function: Code, arguments: Code*): Code =
    arguments.foldLeft(function)(Code.Apply(_, _))

  private def thunk(code: Code, holes: Int): Configured[NoFacts.type] =
    NoFacts.thunkOrInstance(
      code,
      (0 until holes).map(Hole.Bound(_)).toVector,
      Vector.empty
    )

  /** λx. x x, bound to zero. */
  private val zero: Configured[NoFacts.type] =
    thunk(applied(slot(0), slot(0)), 1)

  /** λx y. y x, bound to even. */
  private val even: Configured[NoFacts.type] =
    thunk(applied(slot(1), slot(0)), 2)

  /** λx y z. z y x, bound to odd. */
  private val odd: Configured[NoFacts.type] =
    thunk(applied(slot(2), slot(1), slot(0)), 3)

  /** λx y. y y x, bound to `wren_binary_plus`. */
  private val plus: Configured[NoFacts.type] =
    thunk(applied(slot(1), slot(1), slot(0)), 2)

  /** λx y. x, the Scott true. */
  private val truth: Configured[NoFacts.type] = NoFacts.thunkOrInstance(
    slot(0),
    Vector(Hole.Bound(0), Hole.Ignored),
    Vector.empty
  )

  /** λx y. y, the Scott false. */
  private val falsity: Configured[NoFacts.type] = NoFacts.thunkOrInstance(
    slot(0),
    Vector(Hole.Ignored, Hole.Bound(0)),
    Vector.empty
  )

  /** λx. x x (x x), bound to boolean_type by its native_specialization and its
    * data_family, true and false: the parameter of `binary_set true` is read as
    * a truth value.
    */
  private val booleanType: Configured[NoFacts.type] =
    thunk(applied(applied(slot(0), slot(0)), applied(slot(0), slot(0))), 1)

  /** λx y. x (y y), bound to binary_set by its native_specialization. */
  private val binarySet: Configured[NoFacts.type] =
    thunk(applied(slot(0), applied(slot(1), slot(1))), 2)

  /** λy. y, no binary natural. */
  private val identity: Configured[NoFacts.type] = thunk(slot(0), 1)

  private val index = StandardLibraryIndex(
    NoFacts,
    Vector.empty,
    Vector.empty,
    Vector(NativeBound(Pure.required(plus), "wren_binary_plus")),
    Vector(
      CombinatorProperty(
        Pure.required(binarySet),
        Property.NativeSpecialization("binary_natural")
      ),
      CombinatorProperty(
        Pure.required(binarySet),
        Property.DataFamily(0, Vector(zero, even, odd).map(Pure.required))
      ),
      CombinatorProperty(
        Pure.required(booleanType),
        Property.NativeSpecialization(gezi.jit.BooleanFamily.identity.name)
      ),
      CombinatorProperty(
        Pure.required(booleanType),
        Property.DataFamily(0, Vector(truth, falsity).map(Pure.required))
      )
    )
  )

  private val facts = BackendFacts(
    index,
    DeclaredFamilies.extended(index, NativesProvider.loaded)
  )

  private val jitOptions = JitOptions(
    DispatchOption.Fallback,
    BackendOption.Closure,
    GranularityOption.PredicatePerCode,
    instanceTable = true,
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

  /** The backend's encoding, the configuration the program is read in. */
  private val encoding: StorageEncoding = facts.storageEncoding

  private given encodingConfiguration: encoding.type = encoding

  /** A term written with no facts, crossed into the encoding by its pure key.
    */
  private def crossed(
      term: Configured[NoFacts.type]
  ): Configured[encoding.type] =
    Configured.fromPure(encoding)(Pure.required(term))

  /** `a + (a ∥ N)`, N the canonical naturals' criterion `binary_set true`. */
  private def fallbackPoint(
      operand: Configured[encoding.type]
  ): Configured[encoding.type] =
    encoding.choice(
      operand,
      encoding.parallel(
        operand,
        encoding.application(crossed(binarySet), crossed(truth))
      )
    )

  /** The program nested `depth` deep. */
  private def nested(depth: Int): Configured[encoding.type] =
    val identityTerm = crossed(identity)
    val plusTerm = crossed(plus)
    (2 to depth).foldLeft(
      encoding.application(
        encoding.application(plusTerm, fallbackPoint(identityTerm)),
        fallbackPoint(identityTerm)
      )
    )((inner, _) =>
      encoding.application(
        encoding.application(plusTerm, fallbackPoint(inner)),
        fallbackPoint(identityTerm)
      )
    )

  /** The checks the JIT runs reading the program's heads. */
  private def checks(depth: Int): Long =
    val jit = Defaults.jit(
      encoding,
      jitOptions,
      GroupBlocksOption.None,
      gezi.ir.StorageAccess.granted()
    )
    WeakHead
      .heads(Mode.Jit, Value.of(nested(depth)))
      .collected
      .result(ReadingState.fresh(1000000, jit.readingConfiguration)) match
      case Computed.Done(_, after) =>
        JitRunState.held(after.jitState, jit.configuration) match
          case Some(run) => run.counts.fallbackChecks
          case None      =>
            fail(
              s"a reading of the JIT leaves its run state, not ${after.jitState}"
            )
      case Computed.Stopped(after) =>
        fail(
          s"the reading of the heads stopped after ${after.budget.spent} steps"
        )

  test("a nested native application checks each argument once") {
    assertEquals(Vector(4, 8).map(checks), Vector(8L, 16L))
  }
