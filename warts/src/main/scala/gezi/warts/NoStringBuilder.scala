package gezi.warts

/** Forbids the mutable string builders, `java.lang.StringBuilder` and Scala's
  * `StringBuilder` and its alias in the `scala` package.
  */
object NoStringBuilder extends ForbiddenSymbols:

  override protected val message: String = "StringBuilder is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    simpleName == "StringBuilder" && (fullName.startsWith(
      "java.lang."
    ) || fullName.startsWith("scala."))
