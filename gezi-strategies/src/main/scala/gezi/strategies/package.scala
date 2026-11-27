package gezi

/** The baseline's search strategies. [[Schedule]] runs rounds, each a
  * [[SearchStrategy]], the outputs of one round the inputs of the next, and
  * writes a round's OpenTheory article with `proofs`; [[FixpointEgraph]]
  * saturates with the framework's e-graph and extracts by the ordering
  * modules of a normality degree ([[NormalityModule]], [[TermOrder]],
  * [[BaselineModules]]); [[NativeRouteCompilation]] holds the schedules of
  * the native route, and [[DispatchStrategies]] the dispatch strategies.
  * Strategies remember costs only and name no lemma and no combinator. A
  * saturation encodes its lemmas into patterns by the `LemmaEncoding` its
  * caller puts in its `SaturationOptions`.
  *
  * The module depends on `standardlibrary`, `proofs`, `lemma-encoding` (the
  * interface, no implementation), `orientation`,
  * `ematching-indexing`, the three backends `ematching-interpretation`,
  * `ematching-closures` and `ematching-bytecode`, `saturation` and
  * `extraction`; `jit` depends on it.
  */
package object strategies
