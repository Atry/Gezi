package gezi.hotspot.baselines

import gezi.hotspot.CacheGuard
import gezi.hotspot.CacheNamespace
import gezi.hotspot.CacheProvider
import gezi.hotspot.LifecycleEvent
import gezi.hotspot.Retention

/** The key of an entry: the namespace, an object compared by identity, and
  * the key within it, so that two namespaces' keys never meet.
  */
private final case class NamespacedKey(namespace: CacheNamespace[?, ?], key: Any)

/** The cache provider of the baseline: a thread
  * safe provider in the process, one map from a namespace and a key to a
  * value, the key itself as the map's key, so that the equality of instructions
  * is the equality of terms.
  *
  * Taking a namespace's lock does nothing: the map locks per key, so a
  * thread computing one key never holds up a thread reading or writing
  * another. Duplicate computation is allowed for every namespace (one of
  * the policies `CacheProvider` lists): `getOrElseUpdate` computes a
  * missing value with no lock held and writes it only if the key is still
  * absent, so two threads may both compute it, and both get the value
  * written first, which, an entry being a pure function of its key, is
  * the value either computed. No call blocks.
  *
  * A namespace's entries are kept as its retention says
  * (`CacheNamespace.retention`): a strong namespace's in the map; a namespace whose values are soft, or
  * whose keys are weak, in a Caffeine cache of its own, which may drop them
  * before any event. Everything is cleared at the lifecycle events of
  * `clearedAt`, which the adapter that builds the provider chooses, and kept
  * at every other event: the judge's provider clears when a round starts, so
  * that no round reads another's entries, and the points of a
  * family, and the families of a round, reuse what the ones before wrote; a
  * provider whose set is empty never clears, keeping everything in memory,
  * which is one of the options.
  *
  * @param clearedAt
  *   the lifecycle events at which every entry is cleared
  */
@SuppressWarnings(Array("gezi.warts.NoJavaUtilConcurrent")) // "这里可变Map作为底层接口局部封装例外可以引入" (the user, 2026-11-01)
final class ConcurrentMapCacheProvider(clearedAt: Set[LifecycleEvent]) extends CacheProvider:

  // The cache service's framework (the synchronized convention of `gezi.hotspot`); its
  // monitor is the map's own per-key locking, each operation one block; no
  // IO, no foreign call and no other monitor inside an operation (the value
  // is computed before `putIfAbsent`, outside it). A local mutable exception,
  // the user's (2026-11-01): "这里可变Map作为底层接口局部封装例外可以引入"
  private val entries = java.util.concurrent.ConcurrentHashMap[NamespacedKey, Any]() // "这里可变Map作为底层接口局部封装例外可以引入"

  // The entries of the namespaces whose retention lets them be dropped
  // before a lifecycle event (`Retention.SoftValues`, `Retention.WeakKeys`):
  // one Caffeine cache for each such namespace, made when the namespace is
  // first locked, since Caffeine takes softness and weakness per cache. The same local
  // mutable exception and the same monitor discipline: each operation one
  // block of the map's or the cache's own locking. "这里可变Map作为底层接口局部封装例外可以引入"
  private val dropping =
    java.util.concurrent.ConcurrentHashMap[CacheNamespace[?, ?], com.github.benmanes.caffeine.cache.Cache[AnyRef, AnyRef]]() // "这里可变Map作为底层接口局部封装例外可以引入"

  def locked[Key, Value, Result](namespace: CacheNamespace[Key, Value])(body: CacheGuard[Key, Value] => Result): Result =
    namespace.retention match
      case Retention.Strong => body(ConcurrentMapGuard(namespace))
      case Retention.SoftValues | Retention.WeakKeys =>
        body(DroppingGuard[Key, Value](dropping.computeIfAbsent(namespace, ConcurrentMapCacheProvider.droppingCache)))

  def lifecycle(event: LifecycleEvent): Unit =
    if clearedAt.contains(event) then
      entries.clear()
      dropping.clear()

  /** The guard of a namespace: a handle on the map with nothing of its own.
    * An entry under the namespace was written by `getOrElseUpdate` with a
    * value of the namespace's value type, so the casts hold.
    */
  private final class ConcurrentMapGuard[Key, Value](namespace: CacheNamespace[Key, Value]) extends CacheGuard[Key, Value]:

    def tryGet(key: Key): Option[Value] =
      Option(entries.get(NamespacedKey(namespace, key))).map(_.asInstanceOf[Value])

    def getOrElseUpdate(key: Key, value: => Value): Value =
      val namespacedKey = NamespacedKey(namespace, key)
      Option(entries.get(namespacedKey)) match
        case Some(found) => found.asInstanceOf[Value]
        case None =>
          val computed = value
          Option(entries.putIfAbsent(namespacedKey, computed)) match
            case Some(writtenFirst) => writtenFirst.asInstanceOf[Value]
            case None               => computed

  /** The guard of a namespace whose entries may be dropped: a handle on the
    * namespace's Caffeine cache, with duplicate computation allowed as for the
    * map's (`getOrElseUpdate` computes with no lock held and writes only if
    * the key is still absent). A key under weak keys is compared by identity,
    * which for an interned term is its equality; a key that is not interned
    * only misses where an equal one was written, which costs time and never
    * an answer. An entry under the namespace was written with a value of the
    * namespace's value type, so the casts hold.
    */
  private final class DroppingGuard[Key, Value](cache: com.github.benmanes.caffeine.cache.Cache[AnyRef, AnyRef])
      extends CacheGuard[Key, Value]:

    def tryGet(key: Key): Option[Value] =
      Option(cache.getIfPresent(key.asInstanceOf[AnyRef])).map(_.asInstanceOf[Value])

    def getOrElseUpdate(key: Key, value: => Value): Value =
      val boxedKey = key.asInstanceOf[AnyRef]
      Option(cache.getIfPresent(boxedKey)) match
        case Some(found) => found.asInstanceOf[Value]
        case None =>
          val computed = value
          Option(cache.asMap().putIfAbsent(boxedKey, computed.asInstanceOf[AnyRef])) match
            case Some(writtenFirst) => writtenFirst.asInstanceOf[Value]
            case None               => computed

/** The Caffeine caches of the namespaces whose entries may be dropped. */
object ConcurrentMapCacheProvider:

  /** A new Caffeine cache that keeps the namespace's entries as its retention
    * says: values held softly, or keys held weakly. Caffeine's builder is a
    * mutable object used only inside this call, which returns the cache it
    * builds, the local exception the user allowed for an underlying store
    * (2026-11-01): "这里可变Map作为底层接口局部封装例外可以引入".
    */
  @SuppressWarnings(Array("gezi.warts.NoNewBuilder")) // "这里可变Map作为底层接口局部封装例外可以引入" (the user, 2026-11-01)
  private val droppingCache: java.util.function.Function[CacheNamespace[?, ?], com.github.benmanes.caffeine.cache.Cache[AnyRef, AnyRef]] =
    namespace =>
      namespace.retention match
        case Retention.SoftValues => com.github.benmanes.caffeine.cache.Caffeine.newBuilder().softValues().build[AnyRef, AnyRef]()
        case Retention.WeakKeys   => com.github.benmanes.caffeine.cache.Caffeine.newBuilder().weakKeys().build[AnyRef, AnyRef]()
        case Retention.Strong     => com.github.benmanes.caffeine.cache.Caffeine.newBuilder().build[AnyRef, AnyRef]()
