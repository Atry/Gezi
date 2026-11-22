package gezi.weakhead

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExpansionSource
import gezi.hotspot.LifecycleEvent
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.ir.Instruction
import gezi.standardlibrary.SplitMix

/** The clearing law of shared tables (`TableSharing`),
  * as a state machine:
  * a generated sequence of readings of a few generated closed terms, of
  * clearings of the cache service (`LifecycleEvent.RoundStarted`) and of
  * changes of the expansion source, folded over readings that share their
  * complete tables through one provider under each retention, and over the
  * model, each reading from no table at all. After each reading both read
  * the same set of heads where both finish. Its purpose is to catch a table
  * kept before its component completed, or kept when its reading stopped,
  * which a later reading would take for the least fixed point and read fewer
  * heads from; a table found after the clearing or the change of source
  * that should have hidden it; and a pinned table whose answers a reading reads at the wrong place. The
  * terms are drawn from a pool of three, so that readings repeat and later
  * ones find what earlier ones kept, and each shared reading has a step
  * limit of its own, drawn from 1 to 40, so that many stop (the terms take 3
  * to 20 steps), while the model reads under a limit none reaches.
  */
class TableSharingLawTest extends GeneratedProperties:

  private val modelLimit: Long = 3000

  private enum Operation:
    case Read(term: Int, limit: Long)
    case Cleared
    case SourceChanged

  private val pool: Gen[Vector[Instruction]] =
    Gen.list(
      for
        size <- Gen.int(Range.linear(2, 20))
        seed <- Gen.long(Range.linear(0L, Long.MaxValue))
      yield Defunctionalization.thunkInstruction(EvaluatorTesting.randomApplication(size, SplitMix(seed))._1),
      Range.singleton(3)
    ).map(_.toVector)

  private val operations: Gen[List[Operation]] =
    Gen.frequency1(
      8 -> (for
        term <- Gen.int(Range.constant(0, 2))
        limit <- Gen.long(Range.constant(1L, 40L))
      yield Operation.Read(term, limit)),
      1 -> Gen.constant(Operation.Cleared),
      1 -> Gen.constant(Operation.SourceChanged)
    ).list(Range.linear(1, 16))

  /** The heads of a reading, if it finished. */
  private def heads(term: Instruction, state: ReadingState): Option[Set[ParallelSet]] =
    WeakHead.heads(Mode.TablingWeakHead, term).collected.result(state) match
      case Computed.Done(sets, _) => Some(sets.toSet)
      case Computed.Stopped(_)    => None

  Vector(Retention.Strong, Retention.SoftValues, Retention.WeakKeys).foreach(retention =>
    property(s"readings sharing their complete tables under $retention read the heads of readings from no table") {
      for
        terms <- pool.forAll
        steps <- operations.forAll
          .cover(30, "a term read twice with no clearing between", repeatedRead)
          .cover(30, "a shared reading stopped by its limit", _.exists {
            case Operation.Read(_, limit) => limit < 20
            case _                        => false
          })
      yield
        val provider = BaselineCaches.provider()
        val (_, checks) = steps.foldLeft((ExpansionSource.fresh(), Vector.empty[Result])) {
          case ((source, checked), Operation.Read(index, limit)) =>
            val term = terms(index)
            val shared = ReadingState.knowingTop(limit).copy(sharing = TableSharing.Shared(provider, retention, source))
            val compared = (heads(term, shared), heads(term, ReadingState.knowingTop(modelLimit))) match
              case (Some(found), Some(expected)) => Result.diff(found, expected)(_ == _)
              case _                             => Result.success
            (source, checked :+ compared)
          case ((source, checked), Operation.Cleared) =>
            provider.lifecycle(LifecycleEvent.RoundStarted)
            (source, checked)
          case ((_, checked), Operation.SourceChanged) =>
            (ExpansionSource.fresh(), checked)
        }
        Result.all(checks.toList)
    }
  )

  /** Whether some term is read twice with no clearing and no change of
    * source between the two readings.
    */
  private def repeatedRead(steps: List[Operation]): Boolean =
    steps
      .foldLeft((Set.empty[Int], false)) {
        case ((read, repeated), Operation.Read(index, _)) => (read + index, repeated || read.contains(index))
        case ((_, repeated), Operation.Cleared | Operation.SourceChanged) => (Set.empty, repeated)
      }
      ._2
