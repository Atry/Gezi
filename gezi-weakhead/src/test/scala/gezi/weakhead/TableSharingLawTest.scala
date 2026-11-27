package gezi.weakhead

import gezi.ir.NoFacts
import gezi.ir.Configured
import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.frontend.Defunctionalization
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.ExpansionSource
import gezi.hotspot.LifecycleEvent
import gezi.hotspot.Retention
import gezi.hotspot.baselines.BaselineCaches
import gezi.standardlibrary.SplitMix

/** The clearing law of shared tables (`TableSharing`), as a state machine: a
  * generated sequence of readings of a few generated closed terms, of clearings
  * of the cache service (`LifecycleEvent.RoundStarted`) and of changes of the
  * expansion source, folded over readings that share their complete tables
  * through one provider under each retention, and over the model, each reading
  * from no table at all. After each reading both read the same set of heads
  * where both finish. Its purpose is to catch a table kept before its component
  * completed, or kept when its reading stopped, which a later reading would
  * take for the least fixed point and read fewer heads from; a table found
  * after the clearing or the change of source that should have hidden it; and a
  * pinned table whose answers a reading reads at the wrong place. The terms are
  * drawn from a pool of three, so that readings repeat and later ones find what
  * earlier ones kept, and each shared reading has a step limit of its own,
  * drawn from 1 to 40, so that many stop (the terms take 3 to 20 steps), while
  * the model reads under a limit none reaches.
  */
class TableSharingLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts

  private val modelLimit: Long = 3000

  private enum Operation:
    case Read(term: Int, limit: Long)
    case Cleared
    case SourceChanged

  private val pool: Gen[Vector[Configured[NoFacts.type]]] =
    Gen
      .list(
        for
          size <- Gen.int(Range.linear(2, 20))
          seed <- Gen.long(Range.linear(0L, Long.MaxValue))
        yield Defunctionalization.thunkInstruction[NoFacts.type](
          EvaluatorTesting.randomApplication(size, SplitMix(seed))._1
        ),
        Range.singleton(3)
      )
      .map(_.toVector)

  private val operations: Gen[List[Operation]] =
    Gen
      .frequency1(
        8 -> (for
          term <- Gen.int(Range.constant(0, 2))
          limit <- Gen.long(Range.constant(1L, 40L))
        yield Operation.Read(term, limit)),
        1 -> Gen.constant(Operation.Cleared),
        1 -> Gen.constant(Operation.SourceChanged)
      )
      .list(Range.linear(1, 16))

  /** The heads of a reading, if it finished. */
  private def heads(
      term: Configured[NoFacts.type],
      state: ReadingState[NoFacts.type]
  ): Option[Set[ParallelSet[NoFacts.type]]] =
    WeakHead
      .heads(Mode.TablingWeakHead, gezi.ir.Value.of(term))
      .collected
      .result(state) match
      case Computed.Done(sets, _) => Some(sets.toSet)
      case Computed.Stopped(_)    => None

  Vector(Retention.Strong, Retention.SoftValues, Retention.WeakKeys).foreach(
    retention =>
      property(
        s"readings sharing their complete tables under $retention read the heads of readings from no table"
      ) {
        for
          terms <- pool.forAll
          drawn <- operations.forAll
          repeated <- Gen.int(Range.constant(0, 2)).forAll
        yield
          // Both cases the law must reach, by construction every iteration: a
          // shared reading under a limit of 1, which stops it (the terms take 3
          // to 20 steps), and the same term then read twice with no clearing
          // and no change of source between.
          val steps = drawn ++ List(
            Operation.Read(repeated, 1L),
            Operation.Read(repeated, 40L),
            Operation.Read(repeated, 40L)
          )
          val provider = BaselineCaches.provider()
          val (_, checks) =
            steps.foldLeft((ExpansionSource.fresh(), Vector.empty[Result])) {
              case ((source, checked), Operation.Read(index, limit)) =>
                val term = terms(index)
                val shared = ReadingState
                  .knowingTop(
                    limit,
                    gezi.weakhead.ReadingConfiguration.withoutFacts
                  )
                  .copy(sharing =
                    TableSharing.Shared(provider, retention, source)
                  )
                val compared = (
                  heads(term, shared),
                  heads(
                    term,
                    ReadingState.knowingTop(
                      modelLimit,
                      gezi.weakhead.ReadingConfiguration.withoutFacts
                    )
                  )
                ) match
                  case (Some(found), Some(expected)) =>
                    Result.diff(found, expected)(_ == _)
                  case _ => Result.success
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
