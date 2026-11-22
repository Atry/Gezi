package gezi.traceplayer

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of `PlayState` on generated states, times and rounds: the hash
  * reads back to the state it spells, in a trace of the rounds, and a hash
  * without a round counts its step from the start; pausing, playing and changing the speed at a time
  * leave the position at that time where it was; and a playing state's
  * position never goes back as time goes on. Its purpose is to catch a hash
  * that loses or rounds a field (a reload would move the player, change
  * its view or forget an inlined shared instruction), a round spelled from the wrong round's input, a control
  * that re-anchors wrongly (the picture would jump when the reader pauses or
  * changes the speed), and a clock read backwards.
  */
class PlayStateLawTest extends GeneratedProperties:

  private val time: Gen[Double] = Gen.double(Range.linearFrac(1.7e12, 1.8e12))

  private val speed: Gen[Double] = Gen.double(Range.linearFrac(0.01, 16.0))

  /** The key of a name the printer gives a shared instruction, a head's
    * name or none, a hash and an ordinal.
    */
  private val sharedKey: Gen[String] =
    for
      head <- Gen.element1(None, Some("cons"), Some(gezi.frontend.NameSpelling.escaped("été")))
      hash <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue))
      ordinal <- Gen.int(Range.linear(1, 3))
      key <- SharedKey.of(gezi.frontend.NameSpelling.shared(gezi.frontend.NameSpelling.Shared(head, hash, ordinal))) match
        case Some(key) => Gen.constant(key)
        case None      => throw new AssertionError(s"a name the printer gives a shared instruction has a key: $head $hash $ordinal")
    yield key

  private val state: Gen[PlayState] =
    for
      anchor <- Gen.choice1(Gen.double(Range.linearFrac(-5.0, 500.0)), Gen.int(Range.linear(0, 500)).map(_.toDouble))
      speed <- speed
      since <- Gen.choice1(Gen.constant(None), time.map(Some(_)))
      view <- Gen.element1(PlayView.Boxes, PlayView.Text)
      inlined <- sharedKey.list(Range.linear(0, 4))
    yield PlayState(anchor, speed, since, view, inlined.toSet)

  /** The rounds of a trace: none, or a few, some of them with no step. */
  private val rounds: Gen[TraceRounds] =
    Gen.int(Range.linear(0, 6)).flatMap(count => Gen.int(Range.linear(0, 40)).list(Range.singleton(count))).map(sizes => TraceRounds(sizes.toVector))

  /** Equal up to the rounding of a sum of a few doubles. */
  private def near(left: Double, right: Double): Boolean =
    (left - right).abs <= 1e-9 * (1 + left.abs.max(right.abs))

  property("the hash reads back to the state") {
    for
      spelled <- state.forAll
      trace <- rounds.forAll
    yield
      val hash = spelled.hash(trace)
      Result.diff(PlayState.parsed(hash, trace), Right(spelled))((read, _) =>
        read.exists(state => near(state.anchor, spelled.anchor) && state.copy(anchor = spelled.anchor) == spelled)
      ).log(hash)
  }

  property("a hash without a round counts its step from the start") {
    for
      spelled <- state.forAll
      trace <- rounds.forAll
    yield
      val hash = spelled.hash(TraceRounds(Vector.empty))
      Result.diff(PlayState.parsed(hash, trace), Right(spelled))(_ == _).log(hash)
  }

  property("pausing, playing and changing the speed keep the position at the time") {
    for
      before <- state.forAll
      now <- time.forAll
      newSpeed <- speed.forAll
    yield
      val position = before.position(now)
      Result.all(
        List(
          Result.diff(before.paused(now).position(now), position)(near).log("paused"),
          Result.diff(before.played(now).position(now), position)(near).log("played"),
          Result.diff(before.withSpeed(now, newSpeed).position(now), position)(near).log("speed changed")
        )
      )
  }

  property("a playing state's position does not go back as time goes on") {
    for
      playing <- state.map(spelled => spelled.copy(playingSince = spelled.playingSince.orElse(Some(1.75e12)))).forAll
      earlier <- time.forAll
      later <- Gen.double(Range.linearFrac(0.0, 1e7)).map(earlier + _).forAll
    yield Result.assert(playing.position(earlier) <= playing.position(later))
  }
