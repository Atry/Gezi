package gezi.jit

import gezi.ir.Code
import gezi.ir.Hole
import gezi.ir.{Configured, NativeSpecializer}
import gezi.saturation.StopSignal

/** The native block mechanism of the JIT, a replaceable component of
  * `JitConfiguration`: when an instance enters a block, what the block runs,
  * and so what it does with a head it cannot run, and when a code is retired.
  * The machine (`JitRules`) calls it at one place: an application that fills a
  * code's last hole. It asks `entered`; on yes, it reads the fillings that may
  * be the self filling (`JitRules.selfFound`), calls `run`, records the outcome
  * in the reading's record (`BlockRecord`), and continues with the block's
  * value or, when the block fell back, runs the instance itself from the entry.
  *
  * A block's value must be equal to the instance under the β rule, the η rule
  * and the natives' equations: the machine continues from it as from the
  * instance.
  *
  * FIXME: this interface is inadmissible and must be redesigned
  * https://github.com/Atry/private-overlay/issues/1943 (`CONTRIBUTING.md`,
  * "Types live only in the term"): a search strategy may not hard-code syntax;
  * it is to find optimisation opportunities by attractors, with the cost model
  * written as properties in the e-graph. `entered` chooses an evaluation
  * strategy in the host from the entry's syntax, its run-time argument and the
  * costs recorded so far, and `run` receives the entry to choose further by its
  * shape. A block's strategy (native eager, lazy or tabling evaluation,
  * evaluation by an algebraic data type's compilation, or the interpreter) is
  * to be chosen only from a property proved on the e-graph and written in the
  * term, in a schedule round that alternates with the type check. The only
  * implementation left is `NoNativeBlocks`, which enters no block, so the
  * defect is not reached by any configuration in the tree; the baseline
  * `BaselineNativeBlocks`, which entered when the argument was represented, was
  * deleted for it.
  *
  * A mechanism that compiles a code keeps the compiled form in the run state
  * (`JitRunState.blockArtifacts`): `run` receives the artifact it left for the
  * entry's code earlier and returns the one to keep. The run state belongs to
  * one configuration (`JitRunState.of`), so the code is the whole key; an
  * artifact is an immutable value computed from the code's syntax and the
  * backend's facts, a table of the second kind of `CONTRIBUTING.md`, "Tables",
  * never a judgment about a value.
  */
trait NativeBlockMechanism:

  /** Whether the instance enters a block, by the entry's syntax and the costs
    * recorded so far: the policy of which argument shapes enter and of when a
    * code is retired.
    */
  def entered[C <: NativeSpecializer & Singleton](
      entry: BlockEntry[C],
      record: BlockRecord
  ): Boolean

  /** The block of the entry run, within `allowance` steps, `spent` being the
    * steps the reading spent before it (for the stop checks of
    * `gezi.weakhead.Budget.stopCheckSteps`) and `stop` the reading's stop
    * signal, given the artifact kept for the entry's code, if any: a value the
    * machine continues from, or a fall back, after which the machine runs the
    * instance from the entry, with the artifact to keep for the code. A block
    * that meets a head it cannot run either falls back or finishes with the
    * term it has reached, an instance the machine then reads on.
    */
  def run[C <: NativeSpecializer & Singleton](
      rules: JitRules[C],
      entry: BlockEntry[C],
      self: Option[SelfFilling[C]],
      artifact: Option[BlockArtifact],
      allowance: Long,
      spent: Long,
      stop: StopSignal
  ): BlockResult[C]

/** A mechanism's compiled form of a code, kept in the run state between its
  * blocks (`JitRunState.blockArtifacts`); each mechanism defines its own
  * immutable subtypes and reads back only those.
  *
  * An artifact is computed from the code's syntax and the backend's facts only,
  * never from the entry's fillings, its argument or the self filling: it is
  * kept under the code alone and handed to every later block of that code,
  * whatever values enter it. An artifact that depended on a value would be a
  * judgment about that value kept under a code, which the type rule forbids
  * (`CONTRIBUTING.md`, "Types live only in the term"). This is a table of the
  * second kind of `CONTRIBUTING.md`, "Tables", a memo of a pure function of
  * syntax.
  */
trait BlockArtifact

/** A block's outcome and the artifact to keep for its code: a new one, or none
  * to keep what was kept.
  */
final case class BlockResult[C <: NativeSpecializer & Singleton](
    outcome: BlockOutcome[C],
    artifact: Option[BlockArtifact]
)

/** An instance at a block's entry: the code, its last hole, its fillings before
  * the hole is filled, and the argument that fills it, as the term writes it (a
  * cell read through).
  */
final case class BlockEntry[C <: NativeSpecializer & Singleton](
    code: Code,
    hole: Hole,
    fillings: Vector[JitValue[C]],
    argument: JitValue[C]
)

/** How a block ended: with a value the machine continues from, or by falling
  * back; the costs it spent either way. The steps of a finished block are
  * charged to the reading; those of a fallen back block are not, since the
  * machine then reads the instance again from the entry.
  */
enum BlockOutcome[C <: NativeSpecializer & Singleton]:
  case Finished(value: JitValue[C], costs: BlockCosts)
  case FellBack(costs: BlockCosts)

/** The costs a native block spent: its steps and its native calls. */
final case class BlockCosts(steps: Long, callsByNative: Map[NativeName, Long]):

  def stepped: BlockCosts = copy(steps = steps + 1)

  def called(native: NativeName): BlockCosts =
    copy(
      steps = steps + 1,
      callsByNative =
        callsByNative.updated(native, callsByNative.getOrElse(native, 0L) + 1)
    )

/** The self filling of a native block and the one head the machine read it to:
  * a lambda of `code` with `holes` left, over `fillings`, among which the self
  * itself (`JitRules.selfFound`).
  */
final case class SelfFilling[C <: NativeSpecializer & Singleton](
    value: JitValue[C],
    code: Code,
    holes: Vector[Hole],
    fillings: Vector[JitValue[C]]
)

/** The costs of the blocks each code ran so far in a run state's life
  * (`JitRunState.blockRecord`): costs, never a type.
  */
final case class BlockRecord(byCode: Map[Code, BlockCodeRecord]):

  /** The record of the code, empty when it ran no block. */
  def of(code: Code): BlockCodeRecord =
    byCode.getOrElse(code, BlockCodeRecord.empty)

  /** The record with the outcome of a block of the code added. */
  def recorded[C <: NativeSpecializer & Singleton](
      code: Code,
      outcome: BlockOutcome[C]
  ): BlockRecord =
    BlockRecord(byCode.updated(code, of(code).recorded(outcome)))

object BlockRecord:

  /** No block run. */
  val empty: BlockRecord = BlockRecord(Map.empty)

/** The blocks of one code: how many finished and fell back, and the steps each
  * kind spent.
  */
final case class BlockCodeRecord(
    finished: Long,
    fellBack: Long,
    finishedSteps: Long,
    fellBackSteps: Long
):

  def recorded[C <: NativeSpecializer & Singleton](
      outcome: BlockOutcome[C]
  ): BlockCodeRecord = outcome match
    case BlockOutcome.Finished(_, costs) =>
      copy(finished = finished + 1, finishedSteps = finishedSteps + costs.steps)
    case BlockOutcome.FellBack(costs) =>
      copy(fellBack = fellBack + 1, fellBackSteps = fellBackSteps + costs.steps)

object BlockCodeRecord:

  val empty: BlockCodeRecord = BlockCodeRecord(0, 0, 0, 0)

/** No native block: every instance is read by the machine. The default. */
object NoNativeBlocks extends NativeBlockMechanism:

  def entered[C <: NativeSpecializer & Singleton](
      entry: BlockEntry[C],
      record: BlockRecord
  ): Boolean = false

  def run[C <: NativeSpecializer & Singleton](
      rules: JitRules[C],
      entry: BlockEntry[C],
      self: Option[SelfFilling[C]],
      artifact: Option[BlockArtifact],
      allowance: Long,
      spent: Long,
      stop: StopSignal
  ): BlockResult[C] =
    throw IllegalStateException(
      s"no native block is entered, yet one was run at code ${entry.code}"
    )

// TODO: a mechanism that chooses a block's strategy only from a property
// proved on the e-graph and written in the term stands beside
// `NoNativeBlocks` once the slot is redesigned (the FIXME on
// `NativeBlockMechanism`).
// The deleted `BaselineNativeBlocks`, which entered when the term wrote the
// argument represented and so chose by syntax and run-time value,
// reads back with
// `git show 169baa469:lambda_jit/jit/src/main/scala/lambdajit/jit/NativeBlockMechanism.scala`,
// and the block interpreter it ran, `NativeBlock` and `BlockValue`, with
// `git show 169baa469:lambda_jit/jit/src/main/scala/lambdajit/jit/NativeBlocks.scala`.
