package com.yang_bo.gezi.warts

/** Forbids `java.lang.ThreadLocal`. */
object NoThreadLocal extends ForbiddenSymbols:

  override protected val message: String = "ThreadLocal is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    fullName == "java.lang.ThreadLocal"
