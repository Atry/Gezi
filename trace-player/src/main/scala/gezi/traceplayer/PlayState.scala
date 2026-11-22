package gezi.traceplayer

/** How the player draws a step's term: each layer of the IR as a box nested
  * in its parent's (`TermView`), or the term's text as the printer writes it,
  * with names and sharing, in the structure of the alternating view
  * (`TextView`).
  */
enum PlayView:
  case Boxes, Text

  /** The value of the hash's `view` key that spells the view. */
  def spelling: String = this match
    case Boxes => "boxes"
    case Text  => "text"

/** The rounds of a trace as the hash counts them:
  * the number of steps of each round, in order, the steps of all rounds one
  * sequence after the start. A position in that sequence is spelled as a
  * round and a step counted from that round's input, the term the round
  * before it gave (the start for the first). A term belongs to the round of
  * the command that made it, as its label says (`TraceSourceMaps.label`): the
  * position at the end of round r is round r's last step, not step 0 of the
  * round after it.
  */
final case class TraceRounds(sizes: Vector[Int]):
  require(sizes.forall(_ >= 0), s"a round has no negative number of steps: $sizes")

  private val offsets: Vector[Int] = sizes.scanLeft(0)(_ + _)

  /** The position of step `step` of round `round`, the first round 1. */
  def position(round: Int, step: Double): Double = offsets(round - 1) + step

  /** The round and the step within it that spell the position: the last
    * round with steps that starts before the position, the first round for a
    * position at or before the start; none for a trace of no round.
    */
  def located(position: Double): Option[(Int, Double)] =
    Option.when(sizes.nonEmpty) {
      val index = sizes.indices.filter(index => sizes(index) > 0 && offsets(index) < position).lastOption.getOrElse(0)
      (index + 1, position - offsets(index))
    }

/** The state of the player, as the page's URL hash spells it
  * (`#round=1&step=42.5&speed=2`): the anchor, a position in steps over all the rounds (`TraceRounds`), the speed in steps per second, while the
  * player plays the time in milliseconds since the Unix epoch at which it was
  * at the anchor, the view the term is drawn in, and the keys of the shared
  * instructions the reader has β-reduced into their occurrences (a click on
  * one shared instruction inlines it, and another binds it again as a
  * synthetic immediately applied abstraction),
  * each the content hash in the name the printer gives the instruction (`SharedKey`), so that one stays
  * inlined from step to step and a key no step's term shares does nothing. While it plays, the
  * position at a time is the anchor's plus the time since then times the
  * speed: the anchor is in the hash, and a change of speed sets a new
  * anchor.
  *
  * The hash is the player's only state: every control writes a new state
  * into it, and the page reads it back, so that a reload, a link or the
  * browser's own navigation restores the position and the view.
  */
final case class PlayState(anchor: Double, speed: Double, playingSince: Option[Double], view: PlayView, inlined: Set[String]):
  require(!anchor.isNaN && !anchor.isInfinite, s"the anchor is a finite number of steps: $anchor")
  require(speed > 0 && !speed.isInfinite, s"the speed is a positive finite number of steps per second: $speed")
  require(playingSince.forall(since => !since.isNaN && !since.isInfinite), s"the time of the anchor is finite: $playingSince")
  require(inlined.forall(SharedKey.isKey), s"each inlined key is a shared instruction's key: $inlined")

  /** The state with the shared instruction of the key β-reduced into its
    * occurrences.
    */
  def withInlined(key: String): PlayState = copy(inlined = inlined + key)

  /** The state with the shared instruction of the key bound again, the
    * printer's binding of it written back.
    */
  def withExtracted(key: String): PlayState = copy(inlined = inlined - key)

  /** The position at the time, in milliseconds since the Unix epoch: the
    * anchor while paused, and the anchor moved on by the time since the
    * anchor's time while playing.
    */
  def position(now: Double): Double = playingSince match
    case None        => anchor
    case Some(since) => anchor + (now - since) / PlayState.millisecondsPerSecond * speed

  /** Paused at the position the state has at the time. */
  def paused(now: Double): PlayState = copy(anchor = position(now), playingSince = None)

  /** Playing from the position the state has at the time, anchored there. */
  def played(now: Double): PlayState = copy(anchor = position(now), playingSince = Some(now))

  /** The state at the new speed, anchored at the position the state has at
    * the time, so that changing the speed does not move the position.
    */
  def withSpeed(now: Double, newSpeed: Double): PlayState =
    copy(anchor = position(now), speed = newSpeed, playingSince = playingSince.map(_ => now))

  /** Paused at the position given, a step or a jump. */
  def at(position: Double): PlayState = copy(anchor = position, playingSince = None)

  /** The hash that spells the state in a trace of the rounds,
    * `#round=…&step=…&speed=…`, the anchor spelled as a round and a step in
    * it (`TraceRounds.located`; `#step=…&speed=…` for a trace of no round),
    * with `&since=…` while playing, `&view=boxes` in the boxes view and
    * `&inline=…` with the keys of the inlined shared instructions
    * (`SharedKey`), in order, separated by commas;
    * `PlayState.parsed` reads it back.
    */
  def hash(rounds: TraceRounds): String =
    val playing = playingSince.fold("")(since => s"&${PlayState.sinceKey}=${PlayState.number(since)}")
    val viewed = if view == PlayState.initial.view then "" else s"&${PlayState.viewKey}=${view.spelling}"
    val inlinedNames = if inlined.isEmpty then "" else s"&${PlayState.inlineKey}=${inlined.toVector.sorted.mkString(",")}"
    val located = rounds.located(anchor).fold(s"${PlayState.stepKey}=${PlayState.number(anchor)}")((round, step) =>
      s"${PlayState.roundKey}=$round&${PlayState.stepKey}=${PlayState.number(step)}"
    )
    s"#$located&${PlayState.speedKey}=${PlayState.number(speed)}$playing$viewed$inlinedNames"

object PlayState:

  private val millisecondsPerSecond: Double = 1000

  private val roundKey = "round"

  private val stepKey = "step"

  private val speedKey = "speed"

  private val sinceKey = "since"

  private val viewKey = "view"

  private val inlineKey = "inline"

  /** The state of a page whose hash names nothing: paused at the first term,
    * one step per second, the term drawn as its text. Both views draw a
    * shared subterm once:
    * on `contest-entries-wren`'s calls_1000_hot direct point,
    * whose step 30's
    * term is a graph of 811 nodes and a tree of 5,407,983, headless chromium
    * opened step 30 in 24.8 s in the boxes and 25.6 s in the text, the
    * trace's replay included (2026-11-20, two runs side by side on two core
    * pairs). The text is the default as the more compact reading of a term.
    */
  val initial: PlayState = PlayState(0, 1, None, PlayView.Text, Set.empty)

  /** The number as the hash writes it: an integral number without a
    * fraction, any other with the digits `Double.toString` gives, which read
    * back to the same number.
    */
  private def number(value: Double): String =
    if value.isWhole && value.abs < 1e15 then value.toLong.toString else value.toString

  /** The state the hash spells in a trace of the rounds, with or without
    * its leading `#`: the keys `round`, `step`, `speed`, `since`, `view` and `inline`,
    * each at most once, separated by `&`; a key left out takes the value of
    * `initial`, and `since` left out means paused. With `round`, `step` counts
    * from that round's input (`TraceRounds.position`); without it, from the
    * start. An empty hash is `initial`. Anything else, a key unknown
    * or repeated, a part without `=`, a value of `step`, `speed` or `since`
    * that is no number or that `PlayState` rejects, a `round` that is not one
    * of the trace's rounds, a `view` that names
    * no view, or an `inline` that is not keys (`SharedKey.isKey`) separated by commas, is `Left` with the reason: the hash is the reader's input,
    * typed or pasted, and the page shows the reason rather than a picture.
    */
  def parsed(hash: String, rounds: TraceRounds): Either[String, PlayState] =
    val text = hash.stripPrefix("#")
    val parts = if text.isEmpty then Vector.empty else text.split('&').toVector
    val pairs = parts.map(part =>
      part.split("=", -1).toVector match
        case Vector(key, value) => Right((key, value))
        case _                  => Left(s"the part '$part' of the hash is not key=value")
    )
    pairs.collectFirst { case Left(reason) => reason } match
      case Some(reason) => Left(reason)
      case None =>
        val found = pairs.collect { case Right(pair) => pair }
        val keys = found.map(_._1)
        val unknown = keys.filterNot(Set(roundKey, stepKey, speedKey, sinceKey, viewKey, inlineKey))
        val repeated = keys.diff(keys.distinct)
        if unknown.nonEmpty then Left(s"the hash names the unknown keys ${unknown.mkString(", ")}")
        else if repeated.nonEmpty then Left(s"the hash repeats the keys ${repeated.distinct.mkString(", ")}")
        else
          val values = found.toMap
          def numberOf(key: String): Either[String, Option[Double]] = values.get(key) match
            case None => Right(None)
            case Some(value) =>
              value.toDoubleOption match
                case Some(read) if !read.isNaN && !read.isInfinite => Right(Some(read))
                case _                                             => Left(s"the value '$value' of $key is no finite number")
          val viewRead: Either[String, PlayView] = values.get(viewKey) match
            case None => Right(initial.view)
            case Some(value) =>
              PlayView.values.find(_.spelling == value).toRight(s"the view '$value' is none of ${PlayView.values.map(_.spelling).mkString(", ")}")
          val inlinedRead: Either[String, Set[String]] = values.get(inlineKey) match
            case None => Right(Set.empty)
            case Some(value) =>
              val keys = value.split(",", -1).toVector
              if keys.forall(SharedKey.isKey) then Right(keys.toSet)
              else Left(s"the value '$value' of $inlineKey is not a list of shared instructions' keys separated by commas")
          val roundRead: Either[String, Option[Int]] = values.get(roundKey) match
            case None => Right(None)
            case Some(value) =>
              value.toIntOption match
                case Some(round) if round >= 1 && round <= rounds.sizes.size => Right(Some(round))
                case _ => Left(s"the round '$value' is none of the trace's ${rounds.sizes.size} rounds, counted from 1")
          for
            round <- roundRead
            step <- numberOf(stepKey)
            speed <- numberOf(speedKey)
            since <- numberOf(sinceKey)
            view <- viewRead
            inlined <- inlinedRead
            state <-
              val speedRead = speed.getOrElse(initial.speed)
              val stepRead = step.getOrElse(initial.anchor)
              val anchor = round.fold(stepRead)(rounds.position(_, stepRead))
              if speedRead > 0 then Right(PlayState(anchor, speedRead, since, view, inlined))
              else Left(s"the speed $speedRead is not positive")
          yield state
