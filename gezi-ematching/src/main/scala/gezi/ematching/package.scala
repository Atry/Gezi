package gezi

/** The backend interface: a [[Program]] is first-order data, the seeds of
  * the orientations filed by [[SeedKind]] and [[SeedKey]], each a sequence
  * of [[Step]]s over registers, and the [[Building]]s of added sides,
  * shared subterms and code bodies. A [[Backend]] compiles a program once
  * into a [[CompiledProgram]], which finds the [[Matching]] of a delta in a
  * graph and builds nodes.
  *
  * The module depends on `ir` and `egraph`. `ematching-indexing` compiles
  * orientations into programs, `ematching-interpretation`,
  * `ematching-closures` and `ematching-bytecode` are the backends, and
  * `saturation` runs a compiled program; a further backend is one more
  * module that depends on this one alone.
  */
package object ematching
