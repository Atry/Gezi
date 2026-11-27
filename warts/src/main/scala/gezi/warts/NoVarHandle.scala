package gezi.warts

/** Forbids `java.lang.invoke.VarHandle`. */
object NoVarHandle extends ForbiddenSymbols:

  override protected val message: String = "VarHandle is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    fullName == "java.lang.invoke.VarHandle"
