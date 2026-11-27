package com.yang_bo.gezi

/** The custom warts of the immutability rule of this build (CONTRIBUTING.md,
  * "The code is 100% immutable"), for WartRemover. Each wart forbids a family
  * of symbols, found by the symbol a tree refers to and by the types a type
  * tree mentions, never by text: a renamed import, an alias or an inferred type
  * does not escape it. [[ForbiddenSymbols]] is their common base; the built-in
  * warts `Var`, `MutableDataStructures` and `While` cover the rest of the rule.
  * A wart is suppressed on a declaration with
  * `@SuppressWarnings(Array("com.yang_bo.gezi.warts.<Name>"))` and the user's words that
  * make the exception, never on a file or a project. An import is not checked,
  * since it cannot carry the annotation; the uses it makes possible are.
  */
package object warts
