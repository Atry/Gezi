package gezi.warts

/** Forbids iterators: the types `scala.collection.Iterator` and
  * `java.util.Iterator` (and their aliases) and the call of an `iterator`
  * method.
  */
object NoIterator extends ForbiddenSymbols:

  override protected val message: String = "Iterator is disabled"

  override protected def isForbidden(
      fullName: String,
      simpleName: String
  ): Boolean =
    (simpleName == "Iterator" && (fullName.startsWith("scala.") || fullName
      .startsWith("java."))) || simpleName == "iterator"
