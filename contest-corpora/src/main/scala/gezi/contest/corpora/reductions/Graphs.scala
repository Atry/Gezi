package gezi.contest.corpora.reductions

import gezi.contest.corpora.merges

/** A directed graph of the graph families (`merges.MergeGraphShape`, the graphs
  * of `contest_merge_graph:graph/6`).
  */
type Graph = merges.MergeGraphShape

/** The graph builders of `problems/merge_graph` the reduction group uses, the
  * merge group's port (`merges.MergeGraph`'s companion): the two shapes, the
  * numeral case and lets, the reach body and the breadth-first reference
  * `reachable`.
  */
val Graphs = merges.MergeGraph

/** The shape of a graph of the graph families, a constructor of
  * problems/schema/graph_shape (`merges.MergeGraph.GraphShape`).
  */
type GraphShape = merges.MergeGraph.GraphShape

/** The shapes of `GraphShape`, for the readers and the tests of the reduction
  * group.
  */
val GraphShape = merges.MergeGraph.GraphShape
