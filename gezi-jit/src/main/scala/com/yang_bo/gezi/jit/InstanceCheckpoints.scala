package com.yang_bo.gezi.jit

/** What the instance table does with one instance. */
enum CheckpointDecision:

  /** Look the instance up; on a miss hand its heads on as they come and record
    * them when its reading ends, a checkpoint.
    */
  case Tabled

  /** Look the instance up and take a hit; on a miss run it untabled and record
    * nothing.
    */
  case LookupOnly

  /** Run the instance untabled, with no lookup. */
  case Untabled

/** The strategy that chooses which instances the table keeps: a table is a
  * checkpoint, which need not cache every instruction even where they are
  * reused, and how often to take one is the strategy's speculation. It reads
  * costs only, never a code, a filling, syntax or a type (a strategy remembers
  * costs only, `CONTRIBUTING.md`, "Types live only in the term"): the code's
  * use of the table so far, the steps the reading spent since the last
  * checkpoint, and the trial the configuration names. A decision changes steps
  * and memory, not answers: the law test `InstanceCheckpointsLawTest` compares
  * a policy's normal forms with the default's wherever both finish. The JIT
  * keeps one exception outside the strategy, the cell's code
  * (`JitRules.cellCode`), which is always tabled, so that the strategy never
  * sees a code.
  */
trait InstanceCheckpoints:

  /** The decision for an instance of a code whose table cost is `cost`, read
    * `stepsSinceCheckpoint` steps after the reading's last recorded entry
    * (`JitRunState.lastCheckpointSpent`), under the configuration's `trial`
    * (`JitConfiguration.instanceTableTrial`).
    */
  def decided(
      cost: TableCost,
      stepsSinceCheckpoint: Long,
      trial: Long
  ): CheckpointDecision

/** The default policy, the table as it was before checkpoint policies: an
  * instance is tabled unless its code's cost is judged unprofitable
  * (`TableCost.unprofitable`), then it runs untabled.
  */
object ProfitableCheckpoints extends InstanceCheckpoints:

  def decided(
      cost: TableCost,
      stepsSinceCheckpoint: Long,
      trial: Long
  ): CheckpointDecision =
    if cost.unprofitable(trial) then CheckpointDecision.Untabled
    else CheckpointDecision.Tabled

/** An example policy, not the default: a checkpoint is taken once at least
  * `interval` steps were spent since the last one; between checkpoints an
  * instance is only looked up.
  */
final case class EveryStepsCheckpoints(interval: Long)
    extends InstanceCheckpoints:
  require(interval >= 0, s"a checkpoint interval is not negative: $interval")

  def decided(
      cost: TableCost,
      stepsSinceCheckpoint: Long,
      trial: Long
  ): CheckpointDecision =
    if stepsSinceCheckpoint >= interval then CheckpointDecision.Tabled
    else CheckpointDecision.LookupOnly
