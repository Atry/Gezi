package gezi.hotspot.baselines

import gezi.hotspot.CacheProvider
import gezi.hotspot.LifecycleEvent

/** The cache providers of the baseline: the thread safe map in the process,
  * cleared at the lifecycle events its builder chooses.
  */
object BaselineCaches:

  /** A new provider with nothing written, cleared when a round starts: the one
    * the judge builds by default, so that no round reads what another round
    * wrote.
    */
  def provider(): CacheProvider = provider(Set(LifecycleEvent.RoundStarted))

  /** A new provider with nothing written, cleared at the events given, and
    * never cleared when there are none.
    */
  def provider(clearedAt: Set[LifecycleEvent]): CacheProvider =
    ConcurrentMapCacheProvider(clearedAt)
