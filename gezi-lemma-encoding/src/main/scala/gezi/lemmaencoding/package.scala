package gezi

/** The interface by which an entry encodes a lemma's two closed terms as
  * patterns: [[LemmaEncoding]] and its result, [[EncodedLemma]]. The
  * strategies and the proofs depend on this interface and are given an
  * implementation by their caller; the baseline's implementation is in the
  * module `lemma-encoding-baseline`.
  *
  * The module depends on `standardlibrary`; `lemma-encoding-baseline`,
  * `proofs` and `strategies` depend on it.
  */
package object lemmaencoding
