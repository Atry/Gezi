package com.yang_bo.gezi.jupyter.kernel

import com.yang_bo.gezi.ffi.ContinuationAwareCall
import com.yang_bo.gezi.ffi.ReplyHandler
import com.yang_bo.gezi.hotspot.ForeignCall
import com.yang_bo.gezi.hotspot.ForeignService
import com.yang_bo.gezi.hotspot.ForeignValue
import com.yang_bo.gezi.saturation.StopSignal

/** The JVM service the kernel injects into its entry's executor
  * (`com.yang_bo.gezi.hotspot.ForeignService`): each call is a continuation-aware method,
  * and a call whose arguments are not values of its parameters has no reply.
  */
object JvmService extends ForeignService:

  def replies(
      calls: Vector[ForeignCall],
      stop: StopSignal
  ): Option[Vector[Vector[ForeignValue]]] =
    RoundReplies.collected(
      calls.map(call =>
        ContinuationAwareCall.of(call) match
          case Some(found) => found.requested(_)
          case None        => (handler: ReplyHandler) => handler.completed()
      ),
      stop
    )

/** The replies of the calls the kernel's service is asked for at once: each
  * call is given a handler of its own, and they are answered when every call
  * has said it is done, each call with its replies in the order it gave them.
  *
  * The handlers collect the replies a method gives from any thread, after it
  * returns as well, since a continuation-aware method receives an asynchronous
  * handler, so they are mutable cells: the almond adapter's local exception
  * ([[com.yang_bo.gezi.jupyter.kernel]]).
  */
@SuppressWarnings(
  Array("com.yang_bo.gezi.warts.NoJavaUtilConcurrent")
) // 可以用almond。可以把整个基于almond的适配层都当成”局部“ (the user, 2026-11-02)
object RoundReplies:

  /** The replies of each call, in the calls' order; none when the stop is
    * requested before every call is done.
    */
  def collected(
      calls: Vector[ReplyHandler => Unit],
      stop: StopSignal
  ): Option[Vector[Vector[ForeignValue]]] =
    val handlers = calls.map(call =>
      val handler = Collecting()
      call(handler)
      handler
    )
    Option.when(allCompleted(handlers, stop))(handlers.map(_.replies))

  /** The milliseconds between two reads of the stop while a call is not done.
    */
  private val pollMilliseconds: Long = 10

  @annotation.tailrec
  private def allCompleted(
      handlers: Vector[Collecting],
      stop: StopSignal
  ): Boolean =
    handlers.find(!_.isCompleted) match
      case None                          => true
      case Some(_) if stop.stopRequested => false
      case Some(waiting)                 =>
        val _ = waiting.awaited(pollMilliseconds)
        allCompleted(handlers, stop)

  /** The handler of one call. A reply after `completed`, or a second
    * `completed`, is the method breaking its contract and throws
    * `IllegalStateException` in the method's thread.
    */
  private final class Collecting extends ReplyHandler:
    private val gathered =
      java.util.concurrent.atomic.AtomicReference(Vector.empty[ForeignValue])
    private val done = java.util.concurrent.CountDownLatch(1)

    def resumed(reply: ForeignValue): Unit =
      if isCompleted then
        throw IllegalStateException(
          "a method gave a reply after it said it was done"
        )
      val _ = gathered.updateAndGet(_ :+ reply)

    def completed(): Unit =
      if isCompleted then
        throw IllegalStateException("a method said twice that it was done")
      done.countDown()

    def isCompleted: Boolean = done.getCount == 0

    def awaited(milliseconds: Long): Boolean =
      done.await(milliseconds, java.util.concurrent.TimeUnit.MILLISECONDS)

    def replies: Vector[ForeignValue] = gathered.get
