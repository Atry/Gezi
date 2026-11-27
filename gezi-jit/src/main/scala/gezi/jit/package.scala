package gezi

/** Whole-block compilation of the thunk IR and the JIT evaluator on it.
  * [[Jit]] is the evaluator the mode `Mode.Jit` of `weakhead` runs, under
  * a [[JitConfiguration]]; a [[GenerationStrategy]] writes a code's
  * [[Emission]] and a [[CompilationBackend]] such as [[ClosureBackend]]
  * compiles it. A [[NativeBackend]] holds the native implementations and
  * the data families the JIT runs, a value an entry may extend or replace
  * (`NativeBackend.standard` is the default); [[BackendFacts]] are the
  * backend's facts of a compiled library under such a value and
  * [[BackendChecks]] the library compiler's checks of it; [[StrategyDispatch]] runs a test under
  * a [[CompilationStrategy]], a schedule of `strategies` and a dispatch
  * strategy, and refines its output. [[JitExecutor]] and [[JitCompiler]]
  * are the JIT and its compilation as the executor and the compiler of
  * hotspot compilation's baseline.
  *
  * The module depends on `weakhead`, `standardlibrary`, `strategies`,
  * `hotspot` and `hotspot-baselines`;
  * the tests of `contest-corpora` depend on it.
  */
package object jit
