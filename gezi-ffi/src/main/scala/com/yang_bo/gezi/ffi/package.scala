package com.yang_bo.gezi

/** The FFI: a program calls external services, and models them in Gezi rather
  * than adapting a runtime to Gezi's standard library. Of the two native
  * interfaces, a `native` adapts the runtime underneath to Gezi's standard
  * library, and this continuation passing FFI models the foreign language in
  * Gezi.
  *
  * A program is a closed term, the state of a Moore machine,
  * `λk. k output transition` (`corpora/library/java_ffi/moore`), so the FFI
  * needs no neutral value, and Definition 14 is the semantics as it stands.
  * Definition 14 promises nothing about side effects: which calls repeat, and
  * what the FFI caches, is its behaviour and not what the program means, and
  * the FFI and the program's author ensure that a call is idempotent.
  *
  * How a program runs is the configured entry's: an executor reads
  * `x ∥ moore_state_type`, decodes it with no normal form, and calls the
  * service an adapter injects (`com.yang_bo.gezi.hotspot.ForeignService`). This package
  * holds what the JVM's service calls (`ContinuationAwareCall`) and what a
  * method replies through (`ReplyHandler`).
  */
package object ffi
