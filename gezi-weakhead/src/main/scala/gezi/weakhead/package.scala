package gezi

/** The weak-head evaluator on the thunk IR and what reads its heads.
  * [[WeakHead]] gives the heads of a closed term in a [[Mode]]: weak head, weak
  * head under the immutable [[Tables]] of tabling, or the JIT's, which `jit`
  * supplies as a [[JitEvaluator]]. [[Reading]] reads a term within a budget of
  * evaluator steps, [[NormalForms]] reads normal forms, and the codecs
  * ([[BigIntegerCodec]], [[BooleanCodec]], [[ListCodec]]) decode and encode the
  * Prolog backend's representations. [[ReadingExecutor]] is a reader of normal
  * forms as an executor of `hotspot`, the weak-head reference of hotspot
  * compilation's baseline.
  *
  * The package spans two modules: `weakhead-core` holds the evaluator, the
  * readings and the executor and depends on `frontend` and `hotspot` only, so
  * that the reader of knowledge files can evaluate them; `weakhead` holds the
  * codecs, which read the library's index, and depends on `weakhead-core` and
  * `standardlibrary`. `jit` and `contest-corpora` depend on `weakhead`.
  */
package object weakhead
