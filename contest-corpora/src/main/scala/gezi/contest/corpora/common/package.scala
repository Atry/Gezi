package gezi.contest.corpora

/** What the groups of the problem corpora share: [[HardCorpus]] gathers the
  * tables of the hard corpus over every group's files, the claims group's
  * tables with the clauses the merge and reduction groups add to them, and
  * [[DeBruijnTerms]] turns closed de Bruijn terms written as data back into
  * the higher-order abstract syntax for the generators that build programs
  * around them.
  *
  * The package uses `claims`, `merges` and `reductions`, and `claims` and
  * `reductions` use it.
  */
package object common
:

  /** A program of the corpora in the higher-order abstract syntax: a term whose constants are closed terms of no
    * facts, the library's terms and the problems' data, read under no facts.
    */
  type ProblemTerm = gezi.frontend.TermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]

  /** A closed de Bruijn term of the corpora whose constants are closed terms of no facts. */
  type ProblemDeBruijnTerm = gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]
