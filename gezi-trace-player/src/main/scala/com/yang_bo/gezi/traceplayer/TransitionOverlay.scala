package com.yang_bo.gezi.traceplayer

import com.yang_bo.gezi.frontend.ReadableText
import org.scalajs.dom

/** The transition within a step: each subtree the step moves (`Played.moves`)
  * drawn as a ghost, a copy of its node, flying from where it stands in the
  * term the step starts from to where it stands in the term the step makes, at
  * the step's progress.
  *
  * The resting terms are declarative (`TermView`); this is the one place the
  * player changes the DOM by hand, an exception to the immutability of the
  * Scala code: cloning, inserting and removing DOM nodes and creating animation
  * objects happen in the overlay and nowhere else. The overlay is emptied and
  * drawn again at each frame from the position alone, so dragging the progress
  * shows the same picture as playing to it.
  *
  * The stage holds three layers, the same width and the same origin: the term
  * the step starts from (`trace-current`), the term it makes laid out but not
  * shown (`trace-next`), from which a ghost's destination is read, and the
  * overlay (`trace-overlay`). A view says where a layer draws the subtree at a
  * path (`Located`): the boxes by their places (`byBox`, `data-place` of
  * `TermView`), the text by the printer's marks of places (`byPlace`,
  * `TextView`), a suffix of a spine being the elements after its mark, which
  * fly together.
  */
object TransitionOverlay:

  /** The elements, in order, that a layer draws the subtree at a path as; none
    * where the layer does not draw it apart from what holds it.
    */
  type Located = (dom.Element, Vector[Int]) => Vector[dom.Element]

  /** A box of `TermView` of the folding: the box at the path's place
    * (`BoxFolding.place`), the binding's for a path that leads to a shared
    * instruction.
    */
  def byBox(folding: BoxFolding): Located =
    (layer, path) =>
      Option(
        layer.querySelector(s"""[data-place="${folding.place(path).key}"]""")
      ).toVector

  /** The text of `TextView` of the printed term: the element after the mark of
    * the path's place, or, for a suffix's mark, every element after it in its
    * spine; none where the text marks no place for the path, which writes the
    * subterm inside another's piece (`TextView.highlighted` finds the nearest
    * place above it instead, which would fly too much).
    */
  def byPlace(printed: ReadableText.Printed[com.yang_bo.gezi.ir.NoFacts.type]): Located =
    val suffixes = printed.pieces.collect {
      case ReadableText.Piece.At(place, suffix) => place.key -> suffix
    }.toMap
    (layer, path) =>
      val key = printed.place(path).key
      suffixes
        .get(key)
        .fold(Vector.empty[dom.Element])(suffix =>
          Option(layer.querySelector(s"""[data-place="$key"]""")).toVector
            .flatMap(mark =>
              val following = Vector.unfold(mark.nextElementSibling)(element =>
                Option(element).map(found => (found, found.nextElementSibling))
              )
              if suffix then following else following.take(1)
            )
        )

  /** Draws the moves at the progress into the stage's overlay, in the next
    * animation frame, after the declarative layers have taken the frame's
    * terms, each subtree found in the term the step starts from and in the term
    * it makes as the view locates it; an empty overlay for no move or no
    * progress.
    */
  def drawn(
      stageIdentifier: String,
      moves: Vector[(Vector[Int], Vector[Int])],
      progress: Double,
      inCurrent: Located,
      inNext: Located
  ): Unit =
    val _ = dom.window.requestAnimationFrame(_ =>
      Option(dom.document.getElementById(stageIdentifier)).foreach(stage =>
        (
          Option(stage.querySelector(".trace-overlay")),
          Option(stage.querySelector(".trace-current")),
          Option(stage.querySelector(".trace-next"))
        ) match
          case (Some(overlay), Some(current), Some(next)) =>
            overlay.innerHTML = ""
            if progress > 0 then
              val origin = overlay.getBoundingClientRect()
              moves.foreach((from, to) =>
                (inCurrent(current, from), inNext(next, to)) match
                  case (sources @ (source +: _), target +: _) =>
                    val sourceRectangle = source.getBoundingClientRect()
                    val targetRectangle = target.getBoundingClientRect()
                    val ghost = sources match
                      case Vector(one) =>
                        val copy =
                          one.cloneNode(true).asInstanceOf[dom.HTMLElement]
                        copy.removeAttribute("data-place")
                        copy
                      case several =>
                        val holder = dom.document
                          .createElement("span")
                          .asInstanceOf[dom.HTMLElement]
                        several.foreach(element =>
                          val _ = holder.appendChild(element.cloneNode(true))
                        )
                        holder
                    ghost.classList.add("trace-ghost")
                    val left =
                      sourceRectangle.left + (targetRectangle.left - sourceRectangle.left) * progress
                    val top =
                      sourceRectangle.top + (targetRectangle.top - sourceRectangle.top) * progress
                    ghost.style.left = s"${left - origin.left}px"
                    ghost.style.top = s"${top - origin.top}px"
                    val _ = overlay.appendChild(ghost)
                  case _ => ()
              )
          case _ => ()
      )
    )
