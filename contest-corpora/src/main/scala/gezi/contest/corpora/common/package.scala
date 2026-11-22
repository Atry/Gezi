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
