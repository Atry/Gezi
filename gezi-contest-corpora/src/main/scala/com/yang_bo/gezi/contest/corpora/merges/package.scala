package com.yang_bo.gezi.contest.corpora

/** The merge group of the problem corpora: the generators of the merge and
  * mixin families and the contest's prelude, such as [[Prelude]], [[Contest]],
  * [[ContestJit]], [[MergeGraph]] and [[MixinLibrary]], each taking its tables
  * from a `ProblemFamily`; [[ClaimFact]] and [[ClaimFactFamily]] are the facts
  * a family poses about its points, as the clauses they add to the hard
  * corpus's tables.
  *
  * The package uses `claims`, `common` and `reductions`, and they use it.
  */
package object merges:

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
