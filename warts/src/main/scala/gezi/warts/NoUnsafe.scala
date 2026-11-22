package gezi.warts

/** Forbids the JDK's `Unsafe` classes (`sun.misc.Unsafe`, `jdk.internal.misc.Unsafe`). */
object NoUnsafe extends ForbiddenSymbols:

  override protected val message: String = "Unsafe is disabled"

  override protected def isForbidden(fullName: String, simpleName: String): Boolean =
    simpleName == "Unsafe" && (fullName.startsWith("sun.") || fullName.startsWith("jdk.") || fullName.startsWith("java."))
