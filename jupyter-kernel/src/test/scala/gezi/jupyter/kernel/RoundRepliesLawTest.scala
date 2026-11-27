package gezi.jupyter.kernel

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.ffi.ReplyHandler
import gezi.frontend.Defunctionalization
import gezi.frontend.Lambdalattice
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.hotspot.ForeignValue
import gezi.saturation.StopSignal
import scala.concurrent.ExecutionContext
import scala.concurrent.Future

/** The laws of collecting a step's replies (`RoundReplies`), on generated steps
  * whose methods reply from the thread of the call or later from another. Its
  * purpose is to catch a reply lost, given to another call, reordered, or a
  * step answered before every method is done; and a step that waits on a method
  * that is never done past the stop.
  */
class RoundRepliesLawTest extends GeneratedProperties:

  /** A call that gives the replies and says it is done, in the thread of the
    * call or, when `later`, in another one after the call has returned.
    */
  private def replying(
      replies: Vector[ForeignValue],
      later: Boolean
  ): ReplyHandler => Unit = handler =>
    def answered(): Unit =
      replies.foreach(handler.resumed)
      handler.completed()
    if later then
      val _ = Future {
        Thread.sleep(5)
        answered()
      }(using ExecutionContext.global)
    else answered()

  private val reply: Gen[ForeignValue] =
    HoasGenerators.normalForm.map(term =>
      ForeignValue.Term(
        Defunctionalization.thunkInstruction(
          Lambdalattice.term(LambdalatticeText.text(term))
        )(using gezi.ir.NoFacts)
      )
    )

  stoppableProperty(
    "each call gets the replies its method gave, in order, once every method is done"
  ) { stopped =>
    for
      rounds <- Gen
        .list(
          Gen.list(reply, Range.linear(0, 3)).map(_.toVector),
          Range.linear(1, 4)
        )
        .forAll
      later <- Gen.list(Gen.boolean, Range.singleton(rounds.size)).forAll
    yield
      val calls = rounds.toVector.zip(later).map(replying(_, _))
      Result.diff(
        RoundReplies.collected(calls, StopSignal.completedWith(stopped)),
        Some(rounds.toVector)
      )(_ == _)
  }

  /** A call that never says it is done. */
  private val silent: ReplyHandler => Unit = _ => ()

  private object Stopped extends StopSignal:
    def stopRequested: Boolean = true

  property(
    "a step whose method is never done is not answered once the stop is requested"
  ) {
    for replies <- Gen.list(reply, Range.linear(0, 3)).forAll
    yield
      val calls = Vector(replying(replies.toVector, later = false), silent)
      Result.diff(RoundReplies.collected(calls, Stopped), None)(_ == _)
  }
