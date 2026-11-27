package com.yang_bo.gezi.warts

/** Forbids every reference to `java.util.concurrent`: its mutable collections,
  * atomics, executors and locks.
  */
object NoJavaUtilConcurrent extends ForbiddenSymbols:

  override protected val message: String = "java.util.concurrent is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    fullName == "java.util.concurrent" || fullName.startsWith(
      "java.util.concurrent."
    )
