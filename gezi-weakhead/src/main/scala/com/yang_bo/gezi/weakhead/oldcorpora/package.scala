package com.yang_bo.gezi.weakhead

/** Scott case analysis for the problem corpora: [[ScottDecoding]] reads a term
  * as a tree of a [[ScottDataType]] by applying it, on the weak-head evaluator,
  * to one neutral value per constructor. It encodes the corpora's numerals and
  * reads their answers; the library, the strategies and the compilation do not
  * use it, and its data types are tables of the corpora, never a type of a
  * term.
  *
  * The package is in the module `weakhead`; the package
  * `com.yang_bo.gezi.contest.corpora.reductions` uses it.
  */
package object oldcorpora
