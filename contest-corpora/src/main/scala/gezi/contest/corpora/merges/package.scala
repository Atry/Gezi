package gezi.contest.corpora

/** The merge group of the problem corpora: the generators of the merge and
  * mixin families and the contest's prelude, such as [[Prelude]],
  * [[Contest]], [[ContestJit]], [[MergeGraph]] and [[MixinLibrary]], each
  * taking its tables from a `ProblemFamily`; [[ClaimFact]] and
  * [[ClaimFactFamily]] are the facts a family poses about its points,
  * as the clauses they add to the hard corpus's tables.
  *
  * The package uses `claims`, `common` and `reductions`, and they use it.
  */
package object merges
