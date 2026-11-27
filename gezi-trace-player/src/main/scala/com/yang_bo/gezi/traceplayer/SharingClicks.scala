package com.yang_bo.gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.Binding.Constants
import com.yang_bo.html.*
import com.yang_bo.gezi.frontend.NameSpelling
import org.scalajs.dom

/** What a click on a shared instruction does: `inlined` β-reduces the shared
  * instruction of the key into its occurrences, `extracted` binds it again,
  * each by writing the state that follows into the hash
  * (`PlayState.withInlined`, `PlayState.withExtracted`).
  */
final case class SharingClicks(
    inlined: String => Unit,
    extracted: String => Unit
):

  /** A name as shown, with the classes: a shared instruction's name (when
    * `shared` says it names one) by its parts (`NameSpelling.sharedParts`), the
    * head's name decoded, then the hash in a span of its own, then the ordinal
    * from 2 on in another, the rest of the spelling not shown (the user,
    * 2026-11-20: "The TermView UI does not need to render `$merkle$`. It could
    * choose to render `89abcdef` part to a special CSS format"), which a click
    * inlines when the printer synthesized it (`SharedKey`); a name the printer
    * escaped decoded; anything else, a literal included, as written. Its title
    * is the text as written.
    */
  def name(text: String, classes: String, shared: Boolean): Binding[dom.Node] =
    Option.when(shared)(text).flatMap(NameSpelling.sharedParts) match
      case Some(parts) =>
        val head = parts.head.fold("")(NameSpelling.unescaped)
        val hash = f"${parts.hash}%08x"
        val ordinals = Constants(
          Vector(parts.ordinal)
            .filter(_ >= 2)
            .map(ordinal =>
              html"""<span class="text-shared-ordinal">${ordinal.toString}</span>""": Binding[
                dom.Node
              ]
            )*
        ).mapBinding(identity)
        SharedKey.of(text) match
          case Some(key) =>
            val title = s"$text: click to β-reduce it into its occurrences"
            val clicked = (_: dom.MouseEvent) => inlined(key)
            html"""<span class=${s"$classes shared-name shared-inlinable"} title=$title onclick=$clicked>$head<span class="text-shared-hash">$hash</span>$ordinals</span>"""
          case None =>
            html"""<span class=${s"$classes shared-name"} title=$text>$head<span class="text-shared-hash">$hash</span>$ordinals</span>"""
      case None =>
        val shown = if NameSpelling.isName(text) && text.contains('$') then
          NameSpelling.unescaped(text)
        else text
        html"""<span class=$classes title=$text>$shown</span>"""

  /** The button that binds the inlined shared instruction of the key again. */
  def extraction(key: String): Binding[dom.Node] =
    val clicked = (event: dom.MouseEvent) =>
      event.stopPropagation()
      extracted(key)
    html"""<button type="button" class="shared-extract" title="Bind this shared term again, as an IIFE" onclick=$clicked><i class="bi bi-box-arrow-up-left"></i></button>"""
