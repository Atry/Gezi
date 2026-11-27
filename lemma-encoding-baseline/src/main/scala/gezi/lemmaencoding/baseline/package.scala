package gezi.lemmaencoding

/** The baseline's encoding of lemmas into patterns, [[BaselineLemmaEncoding]],
  * an implementation of `LemmaEncoding`: as many metavariables as both sides'
  * instructions open binders with, and the defines of the library as
  * references.
  *
  * The module depends on `lemma-encoding`; the top-level composers
  * (`programfamilies`, the contest entries, and the tests of `proofs`,
  * `strategies` and `jit`) choose it.
  */
package object baseline
