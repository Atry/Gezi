package gezi

/** The terms of the defunctionalized IR as the e-graph reads them. A term is an
  * [[Instruction]], one hash-consed term, the canonical object of its
  * [[Layer]]: an application, a parallel, a choice or a thunk (a code with the
  * [[Hole]] of each binder and the fillings of the code's other slots); the
  * e-graph reads a noinline instruction as a leaf and never unfolds it. A
  * [[Code]] is the body of a thunk, one layer over slots, held by a [[Code]],
  * and the [[Store]] holds the noinline instructions. A [[Pattern]] is a side
  * of a lemma over metavariables, instructions and layers.
  *
  * The module `ir` depends on no other module of this build; every other module
  * of the framework but `generatedinputs` depends on it, directly or through
  * another.
  */
package object ir
