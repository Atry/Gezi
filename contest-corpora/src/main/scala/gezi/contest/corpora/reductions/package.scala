package gezi.contest.corpora

/** The reduction group of the problem corpora: the generators of the
  * reduction series and of the set-free, mixin, graph and dynamic
  * programming families, built from the Scott encodings of [[Encodings]]
  * and the problem data [[ReductionGroup]] reads once; a [[ReductionProblem]] is
  * one problem with its limits, and [[Reduction]] its judge, which reads
  * the program's normal forms on the evaluator.
  *
  * The families follow four principles:
  *   - Structure, not names: a point is a closed term that carries the
  *     library's bodies and never its names, and a family is written in two
  *     spellings, direct and respelled, that score alike, so that a compiler
  *     recognises library code by its structure only.
  *   - Repetition: a point has an unmarked repeated part, the function
  *     written once and let bound, and a non-repeated part, the sites' data,
  *     distinct at every site, so that across sites only code can be reused,
  *     never an answer.
  *   - Traps: a point offers the answers of common wrong solutions as
  *     candidates, so that a wrong answer is caught.
  *   - The ladder: a family written by its definition has low rungs that
  *     the reference reading answers within its budget and a top rung that
  *     only the best known algorithm on native representations answers; its
  *     reference time is that of a hand-written native solver.
  *
  * The package uses `claims`, `common`, `merges` and
  * `gezi.weakhead.oldcorpora`; `common` and `merges` use it.
  */
package object reductions
