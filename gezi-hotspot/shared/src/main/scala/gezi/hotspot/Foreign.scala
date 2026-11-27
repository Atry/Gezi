package gezi.hotspot

import gezi.ir.{Closed, NativeSpecializer, Pure}
import gezi.saturation.StopSignal

/** A value that crosses the FFI's boundary as a JVM value, with no Scott
  * encoding on the way, as an input symbol is a closed term of Gezi or a JVM
  * value that encodes as one: a JVM boolean, the bits of a value type of the width, high bit at
  * `width - 1` (`java_ffi/bits`; a `float`'s and a `double`'s are their raw
  * IEEE 754 bits), or a closed term with no parallel (`Pure`), the same under every configuration: a service
  * knows no configuration, and the executor that receives the term brings it into its own by
  * `Configured.fromPure`.
  */
enum ForeignValue:
  case Truth(value: Boolean)
  case Bits(width: Int, value: Long)
  case Term(term: Pure)

/** A call an executor asks of the service: a method by its owner's internal
  * name, its name and its descriptor, and its arguments, which the
  * descriptor's parameters type.
  */
final case class ForeignCall(owner: String, name: String, descriptor: String, arguments: Vector[ForeignValue])

/** The external service an executor calls for a program's Moore machine, which
  * the adapter injects through the executor's dependencies as it injects the
  * cache service.
  * Which calls an executor makes, how often and in what order is the
  * executor's behaviour and not what the program means: whether two
  * executors cause the same side effects is outside the language.
  */
trait ForeignService:

  /** The replies of each call, in the calls' order, each call with its
    * replies in the order it gave them; none when the stop is requested
    * before every call is done.
    */
  def replies(calls: Vector[ForeignCall], stop: StopSignal): Option[Vector[Vector[ForeignValue]]]

object ForeignService:

  /** No service, the dependency of an execution that calls none, such as the
    * judge's. Asked for a reply, it throws: an executor calls a service only
    * in `Executor.interacted`, which such an execution does not run.
    */
  object Absent extends ForeignService:
    def replies(calls: Vector[ForeignCall], stop: StopSignal): Option[Vector[Vector[ForeignValue]]] =
      throw IllegalStateException(s"no foreign service was given for the calls $calls")

/** What one interaction with a program's Moore machine gives: the answers its
  * branches ended with (the output fields they left unread, each a closed value of the configuration the program
  * was read under), whether it ran to its end, and what it cost.
  */
final case class ForeignProgress[C <: NativeSpecializer & Singleton](answers: Vector[Closed[C]], finished: Boolean, spent: Spent)
