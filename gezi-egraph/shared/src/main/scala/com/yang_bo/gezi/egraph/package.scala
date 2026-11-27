package com.yang_bo.gezi

/** The persistent e-graph of a saturation. [[EGraph]] holds the nodes, the data
  * of each class, the signature table, the union-find by size, the instruction
  * table, the closure states, the agenda and the counts; every operation
  * returns the graph after it and leaves the graph it was called on unchanged.
  * [[GraphView]] is what a compiled program reads of a graph and
  * [[GraphBuilding]] what it does to one when it builds nodes; the records of a
  * class and of the agenda, such as [[ClosureState]] and [[ClassData]], are in
  * this package as well.
  *
  * The module depends on `ir`; `ematching` and `extraction` depend on it.
  *
  * The module is compiled for Scala.js as well (`egraph-js`), so that the trace
  * player replays a backward higher-order conversion with saturation's
  * `HigherOrderMatching` on a graph of the replaced term. Its sources use no
  * JVM-only API; a change that needs one moves that code out of the module or
  * into a source `egraph-js` leaves out.
  */
package object egraph
