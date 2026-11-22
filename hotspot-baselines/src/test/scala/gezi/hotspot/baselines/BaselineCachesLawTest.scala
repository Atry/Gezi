package gezi.hotspot.baselines

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.hotspot.Budget
import gezi.hotspot.CacheNamespace
import gezi.hotspot.ForkedTask
import gezi.hotspot.Forks
import gezi.hotspot.LifecycleEvent
import gezi.hotspot.Spent
import gezi.hotspot.TaskOutcome
import gezi.saturation.StopSignal

/** The namespaces of the test. */
private object Numbers extends CacheNamespace[Int, Int]("test.numbers")

private object Others extends CacheNamespace[Int, Int]("test.others")

/** The laws of the baseline's cache provider (`BaselineCaches.provider`).
  *
  * The first: a provider built to clear at a set of lifecycle events, after
  * any sequence of `getOrElseUpdate` calls and lifecycle events on one
  * thread, returns from each call, and reads by `tryGet`, the value first
  * written to its key since the last event of the set, and the first ever
  * written when the set is empty. Its purpose is to catch a provider that
  * clears at an event outside its set (a family's or a point's, whose reuse
  * a family rewards) or misses one in it, that overwrites a held value, or
  * that mixes up two namespaces' keys. The inputs are generated sets of the
  * six events, the judge's `RoundStarted` among them, and sequences of
  * writes of small keys to two namespaces and of the six events.
  *
  * The second, below, is on threads.
  */
class BaselineCachesLawTest extends GeneratedProperties:

  private val namespaces: Vector[CacheNamespace[Int, Int]] = Vector(Numbers, Others)

  /** A write of a value to a key of a namespace, or an event. */
  private enum Operation:
    case Write(namespace: CacheNamespace[Int, Int], key: Int, value: Int)
    case Event(event: LifecycleEvent)

  private val operation: Gen[Operation] = Gen.choice1(
    for
      namespace <- Gen.element1(Numbers, Others)
      key <- Gen.int(Range.constant(0, 3))
      value <- Gen.int(Range.constant(0, 100))
    yield Operation.Write(namespace, key, value),
    Gen.element1(LifecycleEvent.values.head, LifecycleEvent.values.tail*).map(Operation.Event(_))
  )

  /** The value the law expects of the key after the operations: the first
    * write to it after the last event at which the provider clears.
    */
  private def expected(
      operations: Vector[Operation],
      clearedAt: Set[LifecycleEvent],
      namespace: CacheNamespace[Int, Int],
      key: Int
  ): Option[Int] =
    val sinceCleared = operations.reverse.takeWhile {
      case Operation.Event(event) => !clearedAt.contains(event)
      case Operation.Write(_, _, _) => true
    }.reverse
    sinceCleared.collectFirst {
      case Operation.Write(written, writtenKey, value) if written == namespace && writtenKey == key => value
    }

  private val clearings: Gen[Set[LifecycleEvent]] =
    Gen.frequency1(
      1 -> Gen.constant(Set(LifecycleEvent.RoundStarted)),
      1 -> Gen.constant(Set.empty[LifecycleEvent]),
      2 -> Gen.boolean.list(Range.singleton(LifecycleEvent.values.length)).map(chosen =>
        LifecycleEvent.values.toVector.zip(chosen).collect { case (event, true) => event }.toSet
      )
    )

  property("a key holds the first value written to it since the provider was last cleared") {
    for
      clearedAt <- clearings.forAll
      operations <- operation.list(Range.linear(0, 30)).forAll
    yield
      val provider = if clearedAt == Set(LifecycleEvent.RoundStarted) then BaselineCaches.provider() else BaselineCaches.provider(clearedAt)
      val returned = operations.toVector.zipWithIndex.collect {
        case (Operation.Write(namespace, key, value), position) =>
          val got = provider.locked(namespace)(_.getOrElseUpdate(key, value))
          Result.diff(Some(got), expected(operations.toVector.take(position + 1), clearedAt, namespace, key))(_ == _)
        case (Operation.Event(event), _) =>
          provider.lifecycle(event)
          Result.success
      }
      val held =
        for
          namespace <- namespaces
          key <- 0 to 3
        yield Result.diff(provider.locked(namespace)(_.tryGet(key)), expected(operations.toVector, clearedAt, namespace, key))(_ == _)
      Result.all((returned ++ held).toList)
  }

  /** The second law: tasks forked on virtual threads (`Forks.joinedAll`)
    * call `getOrElseUpdate` on overlapping keys of one namespace at once,
    * each offering a value of its own; afterwards each key touched holds one
    * value, every call on that key returned it, and it is one of the values
    * offered for the key. Its purpose is to catch a provider that loses a
    * write, lets a later write replace an earlier one, or answers two threads
    * differently. The inputs are generated lists of keys, one for each task.
    * The values differ between tasks only to make a disagreement visible; a
    * real entry is a pure function of its key.
    */
  stoppableProperty("threads writing one key at once all read the value written first") { stopped =>
    for keysOfTasks <- Gen.int(Range.constant(0, 5)).list(Range.linear(1, 20)).list(Range.linear(1, 8)).forAll
    yield
      val provider = BaselineCaches.provider()
      val tasks = keysOfTasks.toVector.zipWithIndex.map((keys, taskIndex) =>
        ForkedTask[Vector[(Int, Int)]](
          Budget(0, countedUnits = false, StopSignal.completedWith(stopped)),
          (_, _) =>
            TaskOutcome(
              keys.toVector.map(key => (key, provider.locked(Numbers)(_.getOrElseUpdate(key, taskIndex * 100 + key)))),
              Spent.none
            )
        )
      )
      val returned = Forks.joinedAll(tasks).outcomes.flatMap(_.result)
      val touched = keysOfTasks.flatten.distinct
      Result.all(touched.map { key =>
        val held = provider.locked(Numbers)(_.tryGet(key))
        val offered = keysOfTasks.zipWithIndex.collect { case (keys, taskIndex) if keys.contains(key) => taskIndex * 100 + key }
        Result.all(
          List(
            Result.assert(held.exists(offered.contains)).log(s"key $key holds $held, offered $offered"),
            Result.assert(returned.filter(_._1 == key).forall(pair => held.contains(pair._2))).log(s"key $key: calls returned other values")
          )
        )
      })
  }
