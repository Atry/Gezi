package gezi.contest.corpora

/** The claims group of the problem corpora: [[Claims]] makes the group's
  * generators over the files of `gezi/corpora` and the tables of the
  * hard corpus's answers ([[HardAnswers]]) and claims ([[HardClaims]]) over
  * its families, each a [[HardFamily]]: the points of the hard and
  * qualifying corpora ([[Hard]], [[HardClauses]], [[Qualifying]]) and the
  * other families of the group, each reading its tables with a
  * `ProblemFamily`.
  *
  * The package uses `common`, `merges` and `reductions`, which use it in
  * turn.
  */
package object claims
:

  /** A program of the corpora in the higher-order abstract syntax: a term whose constants are closed terms of no
    * facts, the library's terms and the problems' data, read under no facts.
    */
  type ProblemTerm = gezi.frontend.TermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]

  /** A closed de Bruijn term of the corpora whose constants are closed terms of no facts. */
  type ProblemDeBruijnTerm = gezi.frontend.DeBruijnTermOf[gezi.ir.Configured[gezi.ir.NoFacts.type]]
