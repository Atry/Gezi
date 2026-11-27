package gezi

/** Source locations, for people and tools, never for a choice: a [[Span]] of a
  * text, a [[Location]] (a span of a file, a node of a β body applied at a
  * call, or a node a lemma's instance built), and a [[SourceMap]], the
  * locations of each place of one occurrence of an IR term, a function the
  * migration tools need and not they alone.
  *
  * REVIEW: no strategy, cost model, lemma, saturation, extraction or evaluator
  * reads a location: a location is for a message, a migration or a debugger,
  * and removing every location changes no answer, no node number and no union.
  * The dependency check of `conventions` holds the modules that may depend on
  * this one.
  *
  * A location is not part of a term's identity: instructions and codes are
  * hash-consed by content, so one object stands for every occurrence of a term,
  * and the locations of an occurrence travel beside it, as a value the reader
  * returns, never in a table keyed by the term.
  */
package object locations
