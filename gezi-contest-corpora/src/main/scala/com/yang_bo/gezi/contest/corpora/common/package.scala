package com.yang_bo.gezi.contest.corpora

/** What the groups of the problem corpora share: [[HardCorpus]] gathers the
  * tables of the hard corpus over every group's files, the claims group's
  * tables with the clauses the merge and reduction groups add to them, and
  * [[DeBruijnTerms]] turns closed de Bruijn terms written as data back into the
  * higher-order abstract syntax for the generators that build programs around
  * them.
  *
  * The package uses `claims`, `merges` and `reductions`, and `claims` and
  * `reductions` use it.
  */
package object common:

  /** A program of the corpora in the higher-order abstract syntax: a term whose
    * constants are closed terms of no facts, the library's terms and the
    * problems' data, read under no facts.
    */
  type ProblemTerm =
    com.yang_bo.gezi.frontend.TermOf[com.yang_bo.gezi.ir.Configured[com.yang_bo.gezi.ir.NoFacts.type]]

  /** A closed de Bruijn term of the corpora whose constants are closed terms of
    * no facts.
    */
  type ProblemDeBruijnTerm =
    com.yang_bo.gezi.frontend.DeBruijnTermOf[com.yang_bo.gezi.ir.Configured[com.yang_bo.gezi.ir.NoFacts.type]]
