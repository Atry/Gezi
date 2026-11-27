package com.yang_bo.gezi.ir

/** The positive evidence that a child type of a layer cannot be a term (a class
  * number of the e-graph, a code, a pattern), so that the public constructors
  * of `Apply`, `Choice`, `Thunk` and `Parallel` build layers over it, while a
  * layer over terms is built only by a configuration's native specializer or
  * the value layer of this module, whose construction is typed by the
  * configuration. A negative guard (no evidence that a child is an instruction)
  * let `Configured[C]` and `Value[C]` through, opaque types with no upper
  * bound.
  */
sealed trait NotTerm[Child]

object NotTerm:
  private object Evidence extends NotTerm[Any]

  private def evidence[Child]: NotTerm[Child] =
    Evidence.asInstanceOf[NotTerm[Child]]

  /** The evidence for a child type of another module that is no term (the front
    * end's de Bruijn terms): granted only where the conventions project lists
    * it.
    */
  private[gezi] def granted[Child]: NotTerm[Child] = evidence

  /** A class number of the e-graph. */
  given NotTerm[Int] = evidence

  /** An optional child that is no term (the e-graph's class of a respelled
    * filling, when it has one).
    */
  given [Child](using NotTerm[Child]): NotTerm[Option[Child]] = evidence

  /** A code's child, a code. */
  given NotTerm[Code] = evidence

  /** A pattern's child is no term of the IR, so the IR's public constructors
    * build its layers; here, in the implicit scope of every `NotTerm`, since
    * `Pattern` is an alias whose own scope is the pool's.
    */
  given [C <: NativeSpecializer & Singleton]: NotTerm[Pattern[C]] = evidence
