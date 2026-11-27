package gezi

/** The source locations of an e-graph's nodes, computed from the graph's union
  * log (`gezi.egraph.EGraph.unions`), the source maps of the inputs added to it
  * and the sides of the lemmas whose instances it holds, by a pure function and
  * not by the graph, for the migration tools and for every other reader of
  * locations.
  *
  * The module is outside the framework: the graph keeps no location and no
  * analysis value, and the one datum the framework records for it is the thunk
  * node of a β union (`Justification.Beta`), part of the union log. REVIEW: a
  * location is for a message, a migration or a debugger; no strategy, cost
  * model, lemma, saturation or extraction reads one (`gezi.locations`).
  */
package object provenance
