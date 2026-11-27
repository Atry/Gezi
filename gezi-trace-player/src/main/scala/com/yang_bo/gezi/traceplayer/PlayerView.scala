package com.yang_bo.gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.Binding.Constant
import com.yang_bo.html.*
import com.yang_bo.gezi.frontend.ReadableText
import org.scalajs.dom

/** The player: the control bar and the term of the current step.
  *
  * No `Var`: the state is the URL hash, read through LatestEvent
  * (`PageLocation.states`), and the clock is LatestEvent's latest animation
  * frame (`PageClock.frames`). The controls are Bootstrap's styles of native
  * controls (a `btn-check` checkbox to play and pause, a `form-range` slider
  * for the speed, buttons to step, a number field to jump, and buttons to draw
  * the term in boxes, `TermView`, or as its text, `TextView`, and a shared
  * instruction's name or the button of an inlined one, which β-reduce it into
  * its occurrences or bind it again, `SharingClicks`); each shows the state the
  * hash spells, and its event writes the state that follows into the hash
  * (`PageLocation.write`), re-anchored at the time of the event. The hash, not
  * the controls, holds the state because re-anchoring needs the position at the
  * moment of the change, which the anchor gives and a binding of the slider
  * alone does not.
  */
object PlayerView:

  /** The slowest and the fastest speed of the slider, in steps per second, and
    * its increment.
    */
  private val slowest: Double = 0.25

  private val fastest: Double = 8

  private val speedIncrement: Double = 0.25

  /** The identifier of the stage of the term and its transition. */
  private val TransitionStage: String = "trace-player-stage"

  /** The page's content for the terms: the player while the hash spells a
    * state, and the reason in its place while it does not.
    */
  def player(played: Played): Binding[dom.Node] =
    val states = PageLocation.states(played.rounds)
    states.map(_.left.toOption).flatMap {
      case Some(reason) =>
        problem(s"The URL hash spells no state of the player: $reason")
      case None =>
        playing(
          played,
          states.map(
            _.getOrElse(
              throw IllegalStateException(
                "the player is drawn only while the hash spells a state"
              )
            )
          ),
          PageClock.frames()
        )
    }

  /** The message of a page that cannot play, in place of the player. */
  def problem(message: String): Binding[dom.Node] =
    html"""<div class="alert alert-danger m-3" role="alert"><pre class="mb-0">$message</pre></div>"""

  /** The control bar and the term of the step the position shows. */
  private def playing(
      played: Played,
      state: Binding[PlayState],
      clock: Binding[Option[Double]]
  ): Binding[dom.Node] =
    val position: Binding[Double] = state.flatMap(current =>
      current.playingSince match
        case None        => Constant(current.anchor)
        case Some(since) =>
          clock.map(time => current.position(time.getOrElse(since)))
    )
    val frame = position.map(at =>
      val shown = Frame.indexed(played.size, at)
      Frame(shown.step, shown.progress, played.term(shown.step))
    )
    val last = played.size - 1
    val playingNow = state.map(_.playingSince.isDefined)
    val stepText = frame.map(shown =>
      played.rounds
        .located(shown.step)
        .fold(s"Step ${shown.step} of $last")((round, step) =>
          s"Step ${shown.step} of $last (round $round of ${played.rounds.sizes.size}, step ${step.toInt} of ${played.rounds.sizes(round - 1)})"
        )
    )
    val stepLabel =
      frame.map(shown => played.labels(shown.step).getOrElse("The start"))
    def nextStep(step: Int): Int = (step + 1).min(last)
    // The overlay drawn for the frame (`TransitionOverlay`), an empty text in
    // the page's markup: the moves of the step that makes the next term, each
    // subtree found as the view draws it.
    def transition(
        inCurrent: TransitionOverlay.Located,
        inNext: TransitionOverlay.Located
    ): Binding[String] = frame.map(shown =>
      TransitionOverlay.drawn(
        TransitionStage,
        played.moves(nextStep(shown.step)),
        if shown.step < last then shown.progress else 0,
        inCurrent,
        inNext
      )
      ""
    )
    // The resting term dimmed while the step's subtrees are in flight, so that
    // the ghosts stand out from the nodes they leave.
    val currentClass = frame.map(shown =>
      if shown.step < last && shown.progress > 0 && played
          .moves(nextStep(shown.step))
          .nonEmpty
      then "trace-current trace-fading"
      else "trace-current"
    )
    val speedText = state.map(current => s"${current.speed} steps/s")
    val speedValue = state.map(_.speed.toString)
    val jumpValue = frame.map(_.step.toString)
    val playIcon =
      playingNow.map(if _ then "bi bi-pause-fill" else "bi bi-play-fill")
    val progressWidth = position.map(at =>
      s"width: ${100 * (at.max(0).min(last)) / last.max(1)}%"
    )
    def stepTo(step: Int): Unit =
      PageLocation.write(
        currentState(played.rounds).at(step.max(0).min(last)),
        played.rounds
      )
    def currentStep(): Int = Frame
      .indexed(
        played.size,
        currentState(played.rounds).position(PageClock.now())
      )
      .step
    val toggled = (event: dom.Event) =>
      val now = PageClock.now()
      val current = currentState(played.rounds)
      if current.playingSince.isDefined then
        PageLocation.write(current.paused(now), played.rounds)
      else if current.position(now) >= last then
        PageLocation.write(current.at(0).played(now), played.rounds)
      else PageLocation.write(current.played(now), played.rounds)
    val speedChanged = (event: dom.Event) =>
      val slider = event.target.asInstanceOf[dom.HTMLInputElement]
      PageLocation.write(
        currentState(played.rounds)
          .withSpeed(PageClock.now(), slider.valueAsNumber),
        played.rounds
      )
    val jumped = (event: dom.Event) =>
      val field = event.target.asInstanceOf[dom.HTMLInputElement]
      if !field.valueAsNumber.isNaN then stepTo(field.valueAsNumber.toInt)
    val firstClicked = (_: dom.MouseEvent) => stepTo(0)
    val previousClicked = (_: dom.MouseEvent) => stepTo(currentStep() - 1)
    val nextClicked = (_: dom.MouseEvent) => stepTo(currentStep() + 1)
    val lastClicked = (_: dom.MouseEvent) => stepTo(last)
    def viewClicked(view: PlayView) = (_: dom.MouseEvent) =>
      PageLocation.write(
        currentState(played.rounds).copy(view = view),
        played.rounds
      )
    def viewClass(view: PlayView): Binding[String] =
      state.map(current =>
        if current.view == view then "btn btn-outline-secondary active"
        else "btn btn-outline-secondary"
      )
    // A click on a shared instruction writes the state that inlines or
    // binds it again.
    val clicks = SharingClicks(
      key =>
        PageLocation
          .write(currentState(played.rounds).withInlined(key), played.rounds),
      key =>
        PageLocation.write(
          currentState(played.rounds).withExtracted(key),
          played.rounds
        )
    )
    // The step's term and the next, each printed and folded once for each
    // step shown and each set of inlined keys (a binding's `map` passes on
    // only a value unequal to the one before, so the frames within a step
    // print nothing again), the same printing for both views; the library
    // terms the trace names are written by those names and their bodies not
    // shown.
    val folded: Binding[
      (
          Int,
          (ReadableText.Printed[com.yang_bo.gezi.ir.NoFacts.type], BoxFolding),
          (ReadableText.Printed[com.yang_bo.gezi.ir.NoFacts.type], BoxFolding)
      )
    ] =
      frame
        .map(_.step)
        .flatMap(step =>
          state
            .map(_.inlined)
            .map(keys =>
              (
                step,
                BoxFolding.step(
                  played.term(step),
                  played.map(step),
                  played.names,
                  keys
                ),
                BoxFolding.step(
                  played.term(nextStep(step)),
                  played.map(nextStep(step)),
                  played.names,
                  keys
                )
              )
            )
        )
    // The term of the step in boxes, with the step's transition, made again
    // each time the view turns to them, the next laid out unseen for the
    // ghosts' destinations.
    def boxes(): Binding[dom.Node] =
      val current = folded.map(_._2._2)
      val next = folded.map(_._3._2)
      val rewrittenKey = folded.map((step, printing, _) =>
        played.rewritten(step).map(printing._2.place(_).key)
      )
      val drawnTransition = folded.flatMap((_, printing, printingNext) =>
        transition(
          TransitionOverlay.byBox(printing._2),
          TransitionOverlay.byBox(printingNext._2)
        )
      )
      html"""<div class="trace-term trace-stage" id=${TransitionStage}>
        <div class=$currentClass>${TermView.drawn(
          current,
          rewrittenKey,
          played.source,
          clicks
        )}</div>
        <div class="trace-next" aria-hidden="true">${TermView.drawn(
          next,
          Constant(None),
          played.source,
          clicks
        )}</div>
        <div class="trace-overlay" aria-hidden="true"></div>
        ${drawnTransition.bind}
      </div>"""
    // The term of the step as its text, with the step's transition, the next
    // laid out unseen for the ghosts' destinations, as in the boxes.
    def text(): Binding[dom.Node] =
      folded.flatMap((step, printing, printingNext) =>
        val (printed, folding) = printing
        val (printedNext, foldingNext) = printingNext
        // No white space between the stage's elements: the text keeps its
        // white space (`white-space: pre-wrap`), which would put a line
        // above the shown term and none above the next.
        val current =
          TextView.drawn(
            printed,
            played.rewritten(step).flatMap(TextView.highlighted(printed, _)),
            folding.extractions,
            clicks
          )
        val next =
          TextView.drawn(printedNext, None, foldingNext.extractions, clicks)
        val drawnTransition = transition(
          TransitionOverlay.byPlace(printed),
          TransitionOverlay.byPlace(printedNext)
        )
        html"""<div class="trace-text trace-stage" id=${TransitionStage}><div class=$currentClass>$current</div><div class="trace-next" aria-hidden="true">$next</div><div class="trace-overlay" aria-hidden="true"></div>${drawnTransition.bind}</div>"""
      )
    val drawnTerm: Binding[dom.Node] = state.map(_.view).flatMap {
      case PlayView.Boxes => boxes()
      case PlayView.Text  => text()
    }
    html"""<div class="container-fluid py-3">
      <div class="d-flex flex-wrap align-items-center gap-3 mb-2">
        <div class="btn-group" role="group" aria-label="Steps">
          <button type="button" class="btn btn-outline-secondary" title="First step" onclick=$firstClicked><i class="bi bi-skip-start-fill"></i></button>
          <button type="button" class="btn btn-outline-secondary" title="Previous step" onclick=$previousClicked><i class="bi bi-skip-backward-fill"></i></button>
          <input type="checkbox" class="btn-check" id="trace-player-play" autocomplete="off" checked=$playingNow onchange=$toggled>
          <label class="btn btn-outline-primary" for="trace-player-play" title="Play or pause"><i class=$playIcon></i></label>
          <button type="button" class="btn btn-outline-secondary" title="Next step" onclick=$nextClicked><i class="bi bi-skip-forward-fill"></i></button>
          <button type="button" class="btn btn-outline-secondary" title="Last step" onclick=$lastClicked><i class="bi bi-skip-end-fill"></i></button>
        </div>
        <div class="input-group" style="width: 10rem">
          <span class="input-group-text">Step</span>
          <input type="number" class="form-control" min="0" max=${last.toString} step="1" value=$jumpValue onchange=$jumped>
        </div>
        <div class="d-flex align-items-center gap-2">
          <label class="form-label mb-0" for="trace-player-speed"><i class="bi bi-speedometer2"></i></label>
          <input type="range" class="form-range" style="width: 12rem" id="trace-player-speed" min=${slowest.toString} max=${fastest.toString} step=${speedIncrement.toString} value=$speedValue oninput=$speedChanged>
          <span class="text-body-secondary">${speedText.bind}</span>
        </div>
        <span class="text-body-secondary">${stepText.bind}</span>
        <div class="btn-group" role="group" aria-label="View">
          <button type="button" class=${viewClass(
        PlayView.Boxes
      )} title="The term's layers as nested boxes" onclick=${viewClicked(
        PlayView.Boxes
      )}><i class="bi bi-bounding-box"></i></button>
          <button type="button" class=${viewClass(
        PlayView.Text
      )} title="The term's text, with names and sharing" onclick=${viewClicked(
        PlayView.Text
      )}><i class="bi bi-text-left"></i></button>
        </div>
      </div>
      <div class="progress mb-3" role="progressbar" aria-label="Position" style="height: 0.25rem">
        <div class="progress-bar" style=$progressWidth></div>
      </div>
      <div class="trace-step text-body-secondary mb-2">${stepLabel.bind}</div>
      ${drawnTerm}
    </div>"""

  /** The state the hash spells at an event. A control is drawn only while the
    * hash spells a state, so its event finds one; throws
    * `IllegalStateException` otherwise.
    */
  private def currentState(rounds: TraceRounds): PlayState =
    PageLocation
      .current(rounds)
      .fold(
        reason =>
          throw IllegalStateException(
            s"a control acted on a hash that spells no state: $reason"
          ),
        identity
      )
