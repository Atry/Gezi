package com.yang_bo.gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.Binding.Constants
import com.yang_bo.html.*
import com.yang_bo.html.adaptors.AccessibleAdaptors.given
import com.yang_bo.gezi.frontend.ReadableText
import org.scalajs.dom

/** An IR term drawn as a DOM tree, declaratively with Binding.scala: a node is
  * keyed by its path from the root and binds only its own layer's constructor,
  * so a step's rewrite redraws only that place and what is under it, its
  * ancestors' DOM untouched; folded as the printer shares it: first each shared
  * instruction the printed text binds, once, under its name, then the body,
  * each occurrence of a shared instruction a reference to its binding and each
  * library term the trace names its name (`BoxFolding`). A click on a binding's
  * name or a reference β-reduces the shared instruction into its occurrences,
  * and a button on the box of an inlined one binds it again (`SharingClicks`).
  *
  * The box at a place (`ReadableText.Place`: a binding's name, none for the
  * body, and the path from there by the indices of `Layer.children`, written in
  * its element's `data-place`) is drawn from the binding of what `BoxFolding`
  * draws there (`BoxFolding.Shown`): its element is made from that alone, and
  * the boxes under it from the bindings of what is drawn at the paths one
  * longer. A binding maps to what is drawn by Binding.scala's `map`, which
  * tells its listeners only of a value unequal to the one before (equality of
  * instructions is by content). So when the term shown changes, a box whose
  * term and folding are unchanged is told nothing and keeps its DOM; one whose
  * term changes and whose shape does not keeps its element and passes the
  * change to the boxes under it; one whose shape changes gets a new element,
  * and new boxes under it. The bindings are drawn again when their names
  * change.
  *
  * A box is drawn from its term with the source map of its occurrence
  * (`com.yang_bo.gezi.locations.SourceMap`; a binding's, the map of its occurrences
  * merged), whose children are the maps of the terms under it: a thunk's
  * binders get the names its source spells (`CodeDisplay`), and a box's title
  * gives its place in the source (`StartSource.place`), when the map locates
  * it.
  *
  * Order of the updates: what a box draws is mapped from its binding before the
  * boxes under it subscribe to that binding, so on a change of the term the
  * shape is told first; when the shape changes, the old boxes under it
  * unsubscribe and are not told (Binding.scala's listener buffer skips a
  * listener removed while it notifies), so `BoxFolding.under` is asked only for
  * positions the new term has, and `BoxFolding.binding` only for the names of
  * the bindings drawn.
  */
object TermView:

  /** The boxes of a step's term as its folding draws them, the box at the key
    * of `rewritten` marked `ir-rewritten`: the box the step shown put there.
    */
  def drawn(
      folding: Binding[BoxFolding],
      rewritten: Binding[Option[String]],
      source: StartSource,
      clicks: SharingClicks
  ): Binding[dom.Node] =
    val names = folding.map(_.bindings.map(_.name))
    val bindings = names.flatMap(all =>
      html"""<div class="ir-bindings">${Constants(
          all.map(name => binding(name, folding, rewritten, source, clicks))*
        ).mapBinding(identity)}</div>"""
    )
    html"""<div class="ir-folded">${bindings}${node(
        ReadableText.Place(None, Vector.empty),
        folding.map(_.body),
        folding,
        rewritten,
        source,
        clicks
      )}</div>"""

  /** The binding of the name: its name, which a click inlines, in the style of
    * a binder, and its value's boxes indented under it, with no operator
    * between them, the text having no `=` (CONTRIBUTING.md, "What Gezi is",
    * Text: "no `=`, not even in pseudo-code"), so that the binding does not
    * read as a `let` the language lacks.
    */
  private def binding(
      name: String,
      folding: Binding[BoxFolding],
      rewritten: Binding[Option[String]],
      source: StartSource,
      clicks: SharingClicks
  ): Binding[dom.Node] =
    html"""<div class="ir-binding">${clicks.name(
        name,
        "ir-binding-name ir-binders",
        true
      )}<div class="ir-binding-value">${node(
        ReadableText.Place(Some(name), Vector.empty),
        folding.map(_.binding(name)),
        folding,
        rewritten,
        source,
        clicks
      )}</div></div>"""

  /** The box at the place, from the binding of what is drawn there. */
  private def node(
      place: ReadableText.Place,
      shown: Binding[BoxFolding.Shown],
      folding: Binding[BoxFolding],
      rewritten: Binding[Option[String]],
      source: StartSource,
      clicks: SharingClicks
  ): Binding[dom.Node] =
    shown
      .map(drawing(_, source))
      .flatMap(drawn =>
        element(place, drawn, shown, folding, rewritten, source, clicks)
      )

  /** What a box draws of its own place: a layer's shape, the names of a thunk's
    * binders and the display of its code, its title, and the key of the inlined
    * shared instruction it is; or a reference to a binding.
    */
  private enum Drawing:
    case Layer(
        shape: NodeShape,
        binders: Vector[String],
        code: Option[CodeDisplay],
        title: String,
        extracted: Option[String]
    )
    case Reference(name: String)

  private def drawing(shown: BoxFolding.Shown, source: StartSource): Drawing =
    shown match
      case BoxFolding.Shown.Reference(name, _) => Drawing.Reference(name)
      case BoxFolding.Shown.Layer(instruction, map, extracted) =>
        val shape = NodeShape.of(instruction)
        def titled(kind: String): String =
          source.place(map).fold(kind)(place => s"$kind, source $place")
        shape match
          case NodeShape.Thunk(code, holes, _) =>
            val names = CodeDisplay.slotNames(code, map.code, Some(source))
            val written =
              CodeDisplay.writtenBinders(Some(map), holes.size, Some(source))
            Drawing.Layer(
              shape,
              CodeDisplay.binders(holes, 0, names, written),
              Some(
                CodeDisplay.of(code, holes, written, map.code, Some(source))
              ),
              titled("thunk"),
              extracted
            )
          case NodeShape.Apply =>
            Drawing.Layer(
              shape,
              Vector.empty,
              None,
              titled("application"),
              extracted
            )
          case NodeShape.Parallel =>
            Drawing.Layer(
              shape,
              Vector.empty,
              None,
              titled("parallel"),
              extracted
            )
          case NodeShape.Choice =>
            Drawing.Layer(
              shape,
              Vector.empty,
              None,
              titled("choice"),
              extracted
            )
          case NodeShape.Opaque(_) =>
            Drawing.Layer(
              shape,
              Vector.empty,
              None,
              titled("opaque instruction"),
              extracted
            )

  /** The element of a box, the boxes under it drawn from the binding of what is
    * drawn at its place.
    */
  private def element(
      place: ReadableText.Place,
      drawn: Drawing,
      shown: Binding[BoxFolding.Shown],
      folding: Binding[BoxFolding],
      rewritten: Binding[Option[String]],
      source: StartSource,
      clicks: SharingClicks
  ): Binding[dom.Node] =
    val key = place.key
    val marked = rewritten.map(_.contains(key))
    def classes(kind: String): Binding[String] =
      marked.map(if _ then s"ir $kind ir-rewritten" else s"ir $kind")
    def under(index: Int): Binding[dom.Node] =
      node(
        place.copy(path = place.path :+ index),
        shown.flatMap(at => folding.map(_.under(at, index))),
        folding,
        rewritten,
        source,
        clicks
      )
    drawn match
      case Drawing.Reference(name) =>
        html"""<span class="ir ir-reference">${clicks.name(
            name,
            "ir-reference-name",
            true
          )}</span>"""
      case Drawing.Layer(shape, binders, code, title, extracted) =>
        val extraction = Constants(extracted.toVector.map(clicks.extraction)*)
          .mapBinding(identity)
        shape match
          case NodeShape.Apply =>
            html"""<span class=${classes(
                "ir-apply"
              )} data-place=$key title=$title>$extraction${under(0)}${under(
                1
              )}</span>"""
          case NodeShape.Parallel =>
            html"""<span class=${classes(
                "ir-parallel"
              )} data-place=$key title=$title>$extraction${under(
                0
              )}<span class="ir-operator">∥</span>${under(1)}</span>"""
          case NodeShape.Choice =>
            html"""<span class=${classes(
                "ir-choice"
              )} data-place=$key title=$title>$extraction${under(
                1
              )}<span class="ir-operator">+</span>${under(0)}</span>"""
          case NodeShape.Opaque(description) =>
            html"""<span class=${classes(
                "ir-name"
              )} data-place=$key title=$title>$extraction$description</span>"""
          case NodeShape.Thunk(_, _, fillings) =>
            val shownBinders = binders.mkString(" ")
            val shownCode = code.getOrElse(
              throw IllegalStateException(
                s"a thunk's drawing has no code: $drawn"
              )
            )
            val drawnFillings = Vector.tabulate(fillings)(filling =>
              html"""<span class="ir-filling"><span class="ir-filling-name">${s"#$filling"}</span>${under(
                  filling
                )}</span>""": Binding[dom.Node]
            )
            html"""<span class=${classes(
                "ir-thunk"
              )} data-place=$key title=$title><span class="ir-thunk-code">$extraction<span class="ir-binders">λ $shownBinders.</span>${codeNode(
                shownCode
              )}</span><span class="ir-fillings">${Constants(drawnFillings*)
                .mapBinding(identity)}</span></span>"""

  /** The static drawing of a thunk's code, which belongs to the thunk's own
    * layer: nothing in it changes unless the thunk's shape does.
    */
  private def codeNode(display: CodeDisplay): Binding[dom.Node] = display match
    case CodeDisplay.Variable(name) =>
      html"""<span class="code code-variable">$name</span>"""
    case CodeDisplay.Filling(index) =>
      html"""<span class="code code-filling">${s"#$index"}</span>"""
    case CodeDisplay.Apply(function, argument) =>
      html"""<span class="code code-apply">${codeNode(function)}${codeNode(
          argument
        )}</span>"""
    case CodeDisplay.Parallel(left, right) =>
      html"""<span class="code code-parallel">${codeNode(
          left
        )}<span class="ir-operator">∥</span>${codeNode(right)}</span>"""
    case CodeDisplay.Choice(left, right) =>
      html"""<span class="code code-choice">${codeNode(
          right
        )}<span class="ir-operator">+</span>${codeNode(left)}</span>"""
    case CodeDisplay.Lambda(binders, body) =>
      html"""<span class="code code-lambda"><span class="ir-binders">λ ${binders
          .mkString(" ")}.</span>${codeNode(body)}</span>"""
