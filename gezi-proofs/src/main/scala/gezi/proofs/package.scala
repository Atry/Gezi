package gezi

/** The proof outputs. A search strategy gives its proof as data, a
  * [[StrategyProof]]: the terms it names, its unions and one equation for
  * each input. [[OpentheoryArticle]] writes it as an OpenTheory article,
  * reading the IR and the library through an [[ArticleStore]] and the
  * unions as a [[ProofForest]]; [[LeanStatements]] writes the Lean module
  * of the library's lemma statements. Both state a lemma by the strategy's
  * encoding of its two closed terms into patterns, an `EncodedLemma` the
  * caller passes as data (in the proof, or to `LeanStatements`).
  *
  * The module depends on `standardlibrary`, `frontend` and `lemma-encoding`,
  * the interface only; `strategies`, whose
  * schedule writes a round's article, depends on it.
  */
package object proofs
