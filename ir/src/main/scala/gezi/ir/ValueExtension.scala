package gezi.ir

/** A layer of a reader's value that is no layer of the IR: the readers' neutral
  * value and suspension, and the JIT's sharing cell. Its implementers are
  * listed by the conventions project. The IR fixes, finally, that an extension
  * holds a suspension in the sense of `ConstructorIdentity.suspensionFree`, so
  * that no value with an extension in it is ever taken for a term of the IR; a
  * neutral value says, besides, that it is not closed.
  */
trait ValueExtension[+Child]:

  /** Whether the extension holds no neutral value. */
  def closed: Boolean

  /** False: no value with an extension in it is a term of the IR. */
  final def suspensionFree: Boolean = false
