package gezi.warts

/** Forbids a call of `newBuilder`, which makes a mutable collection builder. */
object NoNewBuilder extends ForbiddenSymbols:

  override protected val message: String = "newBuilder is disabled"

  override protected def isForbidden(fullName: String, simpleName: String): Boolean =
    simpleName == "newBuilder"
