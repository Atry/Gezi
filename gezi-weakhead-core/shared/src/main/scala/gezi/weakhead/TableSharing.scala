package gezi.weakhead

import scala.annotation.tailrec
import gezi.hotspot.Cache
import gezi.hotspot.CacheGuard
import gezi.hotspot.CacheNamespace
import gezi.hotspot.ExpansionSource
import gezi.hotspot.Retention

/** Whether a reading's complete tables of `tabling(weak_head)` are kept in
  * the cache service beside its state, so that other readings read them
  * instead of computing them again: tabling built on the cache service, so
  * that its caching policy is configurable.
  * A complete table is the least fixed point of its key, so whether it is
  * shared, and for how long the service keeps it, changes the time a
  * reading takes and never an answer (the clearing check, `CONTRIBUTING.md`, "Tables"). The tables in progress are never shared: they stay in the
  * reading's state.
  */
enum TableSharing:

  /** The complete tables are kept in the reading's state alone, for as long as
    * its owner carries the state.
    */
  case Local

  /** The complete tables are also kept in the cache service, under a
    * namespace whose retention is `retention`, for the readings of the same
    * extremes, application reading and expansion source.
    *
    * @param cache
    *   the cache service the reading's owner was handed
    * @param retention
    *   how eagerly the service may drop a table (`Retention`)
    * @param source
    *   the version of what the URI nodes the reading meets expand to
    *   (`ExpansionSource`)
    */
  case Shared(cache: Cache, retention: Retention, source: ExpansionSource)

  /** Where a reading in the state keeps its complete tables beside the
    * state: nowhere under `Local`; under `Shared`, the service's namespace
    * of the state's extremes, application reading, continuation reading and
    * parallel reading, read off the state at each call so that a state copied with other
    * extremes never reads the tables of the first, each table kept with the
    * mark of its head (`SharedReadingTables`).
    */
  def completedTables(state: ReadingState): CompletedTables[ReadingState, Value, ParallelSet] = this match
    case TableSharing.Local => CompletedTables.unshared
    case TableSharing.Shared(cache, retention, source) =>
      SharedReadingTables(
        cache,
        CompletedTableNamespace(state.extremes, state.applications, state.continuations, state.parallels, source, retention),
        state.unverified
      )

/** A complete table of `tabling(weak_head)` as the cache service keeps it:
  * its answers, and whether the head of its key, a function applied to an
  * argument, is marked unverified (`ReadingState.unverified`). A walk of
  * `ContinuationReading.Packed` marks a head when it drops a branch of the
  * head applied to the pack, and a consumer that finds the mark reads the
  * β rule as well; the mark is a function of the head alone, so it is kept
  * in the one entry with the answers, which the service keeps or drops
  * together under every retention.
  */
final case class KeptTable(answers: AnswerSet[ParallelSet], unverified: Boolean)

/** The namespace of the complete tables of `tabling(weak_head)` read under
  * one set of inputs: a key is an interned value, and the namespace holds
  * every other input the table's answers depend on, the known extremes, the
  * application reading, the continuation reading (whose `Packed` may lose
  * answers `Substituted` finds), the parallel reading (whose `HeadsMet` may
  * lose answers `BothSides` finds) and the expansion source, so that two readings share
  * a table only where they would compute the same one. Two namespaces are
  * one when their fields are equal.
  */
final case class CompletedTableNamespace(
    extremes: KnownExtremes,
    applications: ApplicationReading,
    continuations: ContinuationReading,
    parallels: ParallelReading,
    source: ExpansionSource,
    override val retention: Retention
) extends CacheNamespace[Value, KeptTable]("weakhead.completed_tables")

/** The complete tables of `tabling(weak_head)` kept in a namespace of the
  * cache service, each with the mark of its key's head (`KeptTable`): a
  * component's tables are written with the marks of the reading that
  * completed them, `unverified`, and a table found is pinned with its mark,
  * so that no reading holds a table of a marked head without the mark (the
  * review of https://github.com/Atry/private-overlay/pull/1798).
  * Each call takes the namespace's lock on its own and releases it before it
  * returns, so no guard escapes it.
  */
final case class SharedReadingTables(cache: Cache, namespace: CompletedTableNamespace, unverified: Set[Value])
    extends CompletedTables[ReadingState, Value, ParallelSet]:

  def found(key: Value): Option[(AnswerSet[ParallelSet], ReadingState => ReadingState)] =
    cache.locked(namespace)(_.tryGet(key)).map(kept =>
      (kept.answers, SharedReadingTables.markedHead(key).filter(_ => kept.unverified).fold(identity[ReadingState]) { head => state =>
        state.copy(unverified = state.unverified + head)
      })
    )

  def kept(leader: Value, members: Vector[Value], complete: Map[Value, AnswerSet[ParallelSet]]): Unit =
    val tables = (leader +: members).map(key =>
      key -> KeptTable(complete(key), SharedReadingTables.markedHead(key).exists(unverified.contains))
    )
    cache.locked(namespace)(guard => SharedCompletedTables.written(guard, tables.toList))

/** The head a mark of a kept table names. */
object SharedReadingTables:

  /** The function of a key that is an application, whose mark the table of
    * the key keeps: the head a walk of the key marks when the key is the head
    * applied to the pack. A mark kept with another application of the same
    * head states the same fact of the head.
    */
  def markedHead(key: Value): Option[Value] = key match
    case Value.Apply(head, _) => Some(head)
    case _                    => None

/** The complete tables kept in a namespace of the cache service, with
  * nothing besides their answers. Each call takes the namespace's lock on
  * its own and releases it before it returns, so no guard escapes it.
  */
final case class SharedCompletedTables[State, Key, Answer](cache: Cache, namespace: CacheNamespace[Key, AnswerSet[Answer]])
    extends CompletedTables[State, Key, Answer]:

  def found(key: Key): Option[(AnswerSet[Answer], State => State)] =
    cache.locked(namespace)(_.tryGet(key)).map(answers => (answers, identity[State]))

  def kept(leader: Key, members: Vector[Key], complete: Map[Key, AnswerSet[Answer]]): Unit =
    cache.locked(namespace)(guard => SharedCompletedTables.written(guard, (leader +: members).toList.map(key => key -> complete(key))))

/** The writing of a component's tables. */
object SharedCompletedTables:

  /** Each value written under its key, unless the key holds one already: a
    * table kept first by another reading is the same least fixed point.
    */
  @tailrec
  private[weakhead] def written[Key, Kept](guard: CacheGuard[Key, Kept], component: List[(Key, Kept)]): Unit =
    component match
      case Nil => ()
      case (key, value) :: rest =>
        val _ = guard.getOrElseUpdate(key, value)
        written(guard, rest)
