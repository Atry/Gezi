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
