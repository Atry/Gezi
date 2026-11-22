package gezi.jupyter

/** The Jupyter kernel of lambdalattice cells: [[CellInterpreter]], an adapter of almond's interpreter
  * that hands each cell to `gezi.contest.entry.Entry.run` and shows the
  * output it returns, and the main that serves it. The module depends on
  * `contest-runner` (the entry's provider, loaded by `ServiceLoader`) and on
  * `contest-entry-generic`, the framework's entry for an entry written as
  * data, which its classpath registers and which reads the
  * `entry.lambdalattice` of the directory named at the install; no module
  * depends on it. The whole module, an adapter of almond, is a local exception
  * to the immutability rule: almond keeps one interpreter across cells and
  * hands replies to handlers from any thread, so the adapter's state stands in
  * mutable cells, each site carrying its `@SuppressWarnings`.
  */
package object kernel
