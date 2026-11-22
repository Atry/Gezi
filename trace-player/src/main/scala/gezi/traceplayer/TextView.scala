package gezi.traceplayer

import com.thoughtworks.binding.Binding
import com.thoughtworks.binding.Binding.Constants
import com.yang_bo.html.*
import com.yang_bo.html.adaptors.AccessibleAdaptors.given
import gezi.frontend.ReadableText
import org.scalajs.dom

/** A step's term drawn as its text, the structure of the DOM the
  * alternating view's, a shared subterm shown once:
  * the printer's pieces (`ReadableText.printed`) as nested elements, one for
  * each node of the printed structure (a right spine of
  * expressions and parameter lists, an expression's head and arguments, a
  * chain's operands, a parenthesized term), so that a shared subterm is
  * written once, in its binding, however often the term refers to it.
  *
  * Names are shown for a person, not to be read back, so a name in the DOM
  * need not be a valid variable name:
  * a shared instruction's name (`NameSpelling.shared`) as its head's
  * name followed by its content hash in a style of its own, `$merkle$`
  * left out: `cons` and `89abcdef` for `cons$merkle$89abcdef`, `89abcdef`
  * alone for `$merkle$89abcdef`, and the ordinal after the hash for
  * `cons$merkle$89abcdef$2`; and a name the printer
  * escaped with `$` decoded (`NameSpelling.unescaped`), its text as written
  * in its title (`SharingClicks.name`). A click on a shared instruction's
  * name β-reduces it into its occurrences, and a button at each occurrence
  * of an inlined one binds it again.
  *
  * The node a step rewrote is highlighted through the printer's marks
  * (`ReadableText.Piece.At`): each mark is an empty element before the
  * node it names, or before the rest of the spine it names, and the style
  * sheet highlights the element after a highlighted node's mark or every
  * element after a highlighted suffix's mark.
  *
  * A step's moves fly in the text as in the boxes (`TransitionOverlay`),
  * each subtree found by its place's mark (`TransitionOverlay.byPlace`).
  */
object TextView:

  /** The printed term's structure: a token of its text, a mark of a
    * subterm's place, or a node with what it holds.
    */
  enum Tree:
    case Token(text: String)
    case Mark(place: ReadableText.Place, suffix: Boolean)
    case Branch(node: ReadableText.Node, children: Vector[Tree])

  /** The structure of the pieces, the trees at its top in order. Throws
    * `IllegalArgumentException` for pieces whose openings and closings do
    * not pair.
    */
  def trees(pieces: Vector[ReadableText.Piece]): Vector[Tree] =
    val stack = pieces.foldLeft(List(Vector.empty[Tree] -> Option.empty[ReadableText.Node])) { (stack, piece) =>
      (piece, stack) match
        case (ReadableText.Piece.Token(text), (children, node) :: rest)       => (children :+ Tree.Token(text), node) :: rest
        case (ReadableText.Piece.At(place, suffix), (children, node) :: rest) => (children :+ Tree.Mark(place, suffix), node) :: rest
        case (ReadableText.Piece.Source(_), _)                                 => stack
        case (ReadableText.Piece.Open(opened), _)                              => (Vector.empty, Some(opened)) :: stack
        case (ReadableText.Piece.Close, (children, Some(closed)) :: (siblings, parent) :: rest) =>
          (siblings :+ Tree.Branch(closed, children), parent) :: rest
        case _ => throw IllegalArgumentException(s"the pieces close a node they did not open: $pieces")
    }
    stack match
      case List((top, None)) => top
      case _                 => throw IllegalArgumentException(s"the pieces leave a node open: $pieces")

  /** The key of the mark that shows the subterm of the printed term at the
    * path (by `Layer.children`): its place's mark, or, where the text writes
    * the subterm inside another's piece, the mark of the nearest place above
    * it; none when the text marks no place on the way, which a printed term
    * never does, its root being marked.
    */
  def highlighted(printed: ReadableText.Printed, path: Vector[Int]): Option[String] =
    val marked = printed.pieces.collect { case ReadableText.Piece.At(place, _) => place.key }.toSet
    path.inits.map(printed.place(_).key).find(marked.contains)

  /** The printed term's text as elements, laid out as the printer's text is
    * (`ReadableText.Printed.laidOutPieces` at `ReadableText.lineWidth`, the
    * width of the start's text, with no line-breaking rule of its own), the mark of the key, if any,
    * highlighted. A shared instruction's name inlines it when clicked, and the
    * mark of each place in `extractions` (`BoxFolding.extractions`) holds the
    * button that binds the inlined shared instruction there again,
    * inside the mark,
    * so that the element after a mark is still the subterm's.
    */
  def drawn(
      printed: ReadableText.Printed,
      highlightedKey: Option[String],
      extractions: Map[String, String],
      clicks: SharingClicks
  ): Binding[dom.Node] =
    val shared = printed.sharedNames.values.toSet
    def drawnAll(children: Vector[Tree]): Binding[dom.Node] =
      html"""<span class="text-run">${Constants(children.map(drawnTree)*).mapBinding(identity)}</span>"""
    def drawnTree(tree: Tree): Binding[dom.Node] = tree match
      case Tree.Token(text) => html"""<span class="text-token">$text</span>"""
      case Tree.Mark(place, suffix) =>
        val kind = if suffix then "text-at text-at-suffix" else "text-at text-at-node"
        val classes = if highlightedKey.contains(place.key) then s"$kind ir-rewritten" else kind
        extractions.get(place.key) match
          case Some(key) =>
            html"""<span class=${s"$classes text-at-extractable"} data-place=${place.key}>${clicks.extraction(key)}</span>"""
          case None => html"""<span class=$classes data-place=${place.key}></span>"""
      case Tree.Branch(ReadableText.Node.Atom, Vector(Tree.Token(text))) =>
        if shared.contains(text) then clicks.name(text, "text-node text-atom text-shared", true)
        else clicks.name(text, "text-node text-atom", false)
      case Tree.Branch(node, children) =>
        html"""<span class=${s"text-node ${nodeClass(node)}"}>${Constants(children.map(drawnTree)*).mapBinding(identity)}</span>"""
    drawnAll(trees(printed.laidOutPieces(ReadableText.lineWidth)))

  /** The class of a node of the printed structure. */
  private def nodeClass(node: ReadableText.Node): String = node match
    case ReadableText.Node.Spine         => "text-spine"
    case ReadableText.Node.Expression    => "text-expression"
    case ReadableText.Node.Parameters    => "text-parameters"
    case ReadableText.Node.Chain         => "text-chain"
    case ReadableText.Node.Step          => "text-step"
    case ReadableText.Node.Parenthesized => "text-parenthesized"
    case ReadableText.Node.Atom          => "text-atom"
