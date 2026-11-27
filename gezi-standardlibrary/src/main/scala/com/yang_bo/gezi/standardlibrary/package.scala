package com.yang_bo.gezi

/** The loader of the standard library: library files reached by paths in source
  * trees, and knowledge files ([[KnowledgeFileReading]]), whose only
  * declarations are `lemma`, `native` and the combinator properties, each
  * binding the term a path gives, compiled by [[StandardLibrary]] into the
  * [[StandardLibraryIndex]] of five facts, which holds no type.
  * [[CombinatorPropertyVocabulary]] lists the combinator properties a library
  * term may carry, and a [[LibraryBackend]] checks a compiled library's natives
  * and specializations.
  *
  * The index gives a lemma its two closed terms only; how they become patterns
  * is an entry's encoding, the module `lemma-encoding`.
  *
  * The module depends on `frontend` and `knowledge-reading`; `lemma-encoding`,
  * `programfamilies`, `proofs`, `strategies`, `weakhead`, `contest-corpora` and
  * `jit` depend on it. It ports modules of the deleted Prolog implementation.
  */
package object standardlibrary
