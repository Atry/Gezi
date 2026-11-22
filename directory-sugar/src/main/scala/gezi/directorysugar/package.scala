package gezi

/** The sugar of a directory tree: [[DirectoryTree]] reads a tree
  * as one term, each directory and each file a mixin with a self, its
  * entries URI nodes of the IR whose expansions it gives, a directory listed
  * or a file parsed when the evaluator first expands it. It resolves no name
  * and no member: a reader applies the root to the keys it wants and
  * evaluates with the general weak-head evaluator. The module depends on
  * `frontend` only; `weakhead-core` calls its expansions.
  */
package object directorysugar
