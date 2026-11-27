package com.yang_bo.gezi.ematching

/** The backend that compiles a program into closures: [[ClosureCompilation]]
  * compiles a program once into a tree of Scala closures, each seed's steps
  * into nested closures, one a step, and each building into a closure from a
  * graph to the graph after it and the node built, so that what a step does is
  * chosen when the program is compiled.
  *
  * The module depends on `ematching` alone; `backendcomparison` selects it.
  */
package object closures
