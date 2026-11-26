package gezi.contest.corpora

/** Reference implementations the old corpora's tests keep:
  * [[BetaEtaNormalisation]], the beta eta normaliser of de Bruijn terms that
  * computed the attractors' normal forms, and [[AttractorReferences]], the
  * native reference computation of each attractor that has one. The
  * pipeline (the library, the strategies, the compilation) does not use
  * them.
  *
  * No other package of the module uses this one outside its tests.
  */
package object oldcorpora
:

  /** A program of the corpora in the higher-order abstract syntax: a term whose constants are closed terms of no
    * facts, the library's terms and the problems' data, read under no facts.
    */
  type ProblemTerm = gezi.frontend.TermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]

  /** A closed de Bruijn term of the corpora whose constants are closed terms of no facts. */
  type ProblemDeBruijnTerm = gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]
