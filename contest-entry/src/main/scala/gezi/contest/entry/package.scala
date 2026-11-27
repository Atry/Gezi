package gezi.contest

/** The interface of a contest entry: an [[EntryProvider]], registered with
  * `java.util.ServiceLoader`, gives the first [[Entry]], and each entry runs a
  * cell ([[Cells]]) to an [[Interaction]] that finishes with the display of the
  * cell's Output, the [[Phase]]s of the run and the entry that runs the next
  * cell. These are the only types an entry implements; the runner in the
  * entry's JVM (`gezi.contest.runner`) loads them, handing the first entry the
  * round's cache service (`gezi.hotspot.Cache`) and the [[ArticleDestination]],
  * and announcing the lifecycle events to the service's provider, which no
  * entry holds. [[Defaults]] chooses the framework's default implementation of
  * each replaceable interface, the implementations the generic entry takes
  * where an entry's data chooses none. The module depends on `jit`, `frontend`,
  * `hotspot`, `hotspot-baselines` and `lemma-encoding-baseline`.
  */
package object entry
