package gezi.warts

/** Forbids `scala.util.DynamicVariable`. */
object NoDynamicVariable extends ForbiddenSymbols:

  override protected val message: String = "DynamicVariable is disabled"

  override protected def isForbidden(fullName: String, simpleName: String): Boolean =
    fullName == "scala.util.DynamicVariable"
