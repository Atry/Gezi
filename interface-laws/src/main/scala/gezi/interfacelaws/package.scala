package gezi

/** The laws of the replaceable interfaces, written against each interface and
  * run on any implementation, so that a module replacing an interface's
  * implementation is checked by the same laws as the default:
  * [[JitEvaluatorLaws]] for the reader `JitEvaluator` and [[ExtractorLaws]] for
  * the extraction `Extractor`. A suite that extends one with an implementation
  * checks that implementation; this module's tests check the framework's
  * defaults, and a contributed module or entry, whose tests depend on this
  * module, checks its replacement the same way. It is test support: it depends
  * on munit and Hedgehog at compile scope, as `generatedinputs` does, and on
  * the test helpers of `jit` and `strategies`.
  */
package object interfacelaws
