package gezi.frontend

import gezi.locations.Span

/** The spans of the nodes of a term read from lambdalattice text
  * (`Lambdalattice.located`), of the term's shape: a node's children are its
  * `DeBruijnTerm` children in order (a lambda's body; an application's function
  * then argument; a choice's or a parallel's left then right). Spans are in
  * code points, as `gezi.locations.Span` says, and end at the end of the node's
  * last token, the layout after it left out.
  *
  *   - `Written`: a node the text spells, the spans of the parentheses written
  *     around it, innermost first, each from its `(` to its `)` included, the
  *     spans of its children, and for an abstraction its binder.
  *   - `Generated`: a subterm the reader builds for one construct (the elements
  *     and the consumer of a literal, the abstractions of the enclosing names
  *     of `Lambdalattice.termInScope`): every node of it has the construct's
  *     span but the subterms written inside the construct, each given at its
  *     path, the child positions from the construct's root down to it; and the
  *     binders of the construct's abstractions, each at its path.
  *
  * The spans are what a migration of the text and a source map need; they are
  * never part of the term, whose equality ignores them.
  */
enum SyntaxSpans:
  case Written(
      span: Span,
      parentheses: Vector[Span],
      children: Vector[SyntaxSpans],
      binder: Option[SpelledBinder]
  )
  case Generated(
      span: Span,
      parentheses: Vector[Span],
      written: Vector[(Vector[Int], SyntaxSpans)],
      binders: Vector[(Vector[Int], SpelledBinder)]
  )

  def span: Span

  def parentheses: Vector[Span]

  /** The binder of the node when it is an abstraction the reader gave one. */
  def nodeBinder: Option[SpelledBinder] = this match
    case Written(_, _, _, binder)    => binder
    case Generated(_, _, _, binders) =>
      binders.collectFirst { case (Vector(), binder) => binder }

  /** The spans with one more pair of parentheses around the node, outside those
    * it has.
    */
  def parenthesized(outer: Span): SyntaxSpans = this match
    case written: Written =>
      written.copy(parentheses = written.parentheses :+ outer)
    case generated: Generated =>
      generated.copy(parentheses = generated.parentheses :+ outer)

  /** The spans of the child at the position: the written child, or for a
    * generated node the subterm written at that path, or the part of the
    * construct below it. Throws `IllegalArgumentException` for a position a
    * written node has no child at.
    */
  def child(position: Int): SyntaxSpans = this match
    case Written(_, _, children, _) =>
      require(
        children.indices.contains(position),
        s"a written node has no child at $position"
      )
      children(position)
    case Generated(span, _, written, binders) =>
      written.collectFirst {
        case (Vector(at), spans) if at == position => spans
      } match
        case Some(spans) => spans
        case None        =>
          Generated(
            span,
            Vector.empty,
            written.collect {
              case (at +: below, spans) if at == position && below.nonEmpty =>
                (below, spans)
            },
            binders.collect {
              case (at +: below, binder) if at == position => (below, binder)
            }
          )

/** A binder as the text gives it, from which the located conversion makes a
  * `gezi.locations.BinderOrigin`:
  *
  *   - `Named`: a name and its span, the name the text writes after a λ, or one
  *     a construct of the reader gives a binder it builds (the `t` and `f` of a
  *     literal argument's bit, and the binders of the miss top at each bit of a
  *     variable arguments partial function, spanning the literal);
  *   - `LiteralBit`: the binder of the bit of a literal's variable arguments
  *     partial function, the bit counted from 0, spanning the literal;
  *   - `Enclosing`: a name a file is read under (`Lambdalattice.termInScope`).
  */
enum SpelledBinder:
  case Named(name: String, span: Span)
  case LiteralBit(literal: Literal, bit: Int, span: Span)
  case Enclosing(name: String)

object SyntaxSpans:

  /** A leaf the text spells: a name. */
  def leaf(span: Span): SyntaxSpans =
    Written(span, Vector.empty, Vector.empty, None)
