package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import com.yang_bo.gezi.locations.Span
import scala.jdk.StreamConverters.*

/** The laws of the spans the located reading gives (`Lambdalattice.located`,
  * `SyntaxSpans`), on the text of a generated closed term, alone or as the body
  * of one λ of mixed binders (names and literals, which the reader spreads into
  * generated terms):
  *
  *   - the located reading reads the term `term` reads (the clearing law:
  *     locations change no term);
  *   - every span lies in the text and within the span of the node above it,
  *     neither starts nor ends with layout, and every pair of parentheses
  *     recorded on a node starts at a `(`, ends just after a `)` and holds the
  *     node's span;
  *   - the text of the span of every written closed node that starts a term (a
  *     node other than an abstraction of a later binder of one λ, and other
  *     than an application to a literal's element) reads, alone, to that node's
  *     term.
  *
  * Its purpose is to catch a span that misses its node's tokens, takes in the
  * layout after it or a neighbour's tokens, a generated node given a written
  * child's span or the reverse, and a located reading that reads another term.
  */
class LambdalatticeSpansLawTest extends GeneratedProperties:

  /** A literal binder's spelling, bare or alone in parentheses. */
  private val literalBinder: Gen[String] =
    Gen.element(
      "\"k\"",
      List("\"\"", "\"ab\"", "0", "12", "[1, 2]", "30([1])", "(3.0)", "\"😀\"")
    )

  /** The text of a generated closed term, alone or under one λ of mixed binders
    * applied to the names it binds, with layout around it.
    */
  private val texts: Gen[String] =
    for
      function <- HoasGenerators.closedTerm
      binders <- Gen.boolean.list(Range.linear(0, 3))
      literals <- literalBinder.list(Range.singleton(binders.size))
      layout <- Gen.element(" ", List("", "\n", " # a comment\n"))
    yield
      val written = binders.zip(literals).zipWithIndex.map {
        case ((isLiteral, literal), index) =>
          if isLiteral then literal else s"x$index"
      }
      val body = (s"(${LambdalatticeText.text(function)})" :: written.filter(
        _.startsWith("x")
      )).mkString(" ")
      val term = if written.isEmpty then LambdalatticeText.text(function)
      else s"λ${written.mkString(" ")}. $body"
      s"$layout$term$layout"

  property(
    "the located reading reads the term, and its spans nest and read back"
  ) {
    texts
      .forAllWithLog(identity)
      .map(text =>
        val located = Lambdalattice.located(text, FreeNames.Rejected)
        val codePoints = text.codePoints.toScala(Vector).map(_.toInt)
        val problems =
          (if located.term == Lambdalattice.term(text) then Vector.empty
           else Vector("another term")) ++
            spanProblems(
              located.term,
              located.spans,
              Span(0, codePoints.size),
              codePoints
            )
        Result.assert(problems.isEmpty).log(problems.mkString("\n"))
      )
  }

  /** The violations of the laws at the node and below it. */
  private def spanProblems(
      term: DeBruijnTerm,
      spans: SyntaxSpans,
      above: Span,
      codePoints: Vector[Int]
  ): Vector[String] =
    val own = spans.span
    val text = own.of(codePoints)
    val nesting = if above.contains(own) then Vector.empty
    else Vector(s"$own outside $above")
    val layout =
      if text.nonEmpty && (Character.isWhitespace(text.head) || Character
          .isWhitespace(text.last))
      then Vector(s"the span $own, `$text`, holds layout at an end")
      else Vector.empty
    val parentheses = spans.parentheses.flatMap(pair =>
      val written = pair.of(codePoints)
      if written.startsWith("(") && written.endsWith(")") && pair.contains(own)
      then Vector.empty
      else Vector(s"parentheses $pair ($written) around $own")
    )
    val readBack = spans match
      // The applications to a literal's elements all span the literal, so
      // only the last reads back alone; none is checked.
      case SyntaxSpans.Written(
            _,
            _,
            Vector(_, SyntaxSpans.Generated(_, _, _, _)),
            _
          ) =>
        Vector.empty
      case SyntaxSpans.Written(_, _, _, _)
          if startsTerm(term, own, codePoints) && looseness(term) == 0 =>
        val read = scala.util.Try(Lambdalattice.term(text)).toOption
        if read.contains(term) then Vector.empty
        else Vector(s"the span $own, `$text`, reads $read")
      case _ => Vector.empty
    val children = term match
      case DeBruijnTerm.Lambda(body) => Vector((body, spans.child(0)))
      case DeBruijnTerm.Apply(function, argument) =>
        Vector((function, spans.child(0)), (argument, spans.child(1)))
      case DeBruijnTerm.Choice(left, right) =>
        Vector((left, spans.child(0)), (right, spans.child(1)))
      case DeBruijnTerm.Parallel(left, right) =>
        Vector((left, spans.child(0)), (right, spans.child(1)))
      case _ => Vector.empty
    nesting ++ layout ++ parentheses ++ readBack ++ children.flatMap(
      (child, childSpans) => spanProblems(child, childSpans, own, codePoints)
    )

  /** Whether the node's span starts a term: it does unless the node is the
    * abstraction of a λ's later binder, whose span starts at that binder, not
    * at a λ.
    */
  private def startsTerm(
      term: DeBruijnTerm,
      own: Span,
      codePoints: Vector[Int]
  ): Boolean =
    term match
      case DeBruijnTerm.Lambda(_) =>
        val first = codePoints.lift(own.start)
        first.contains('λ'.toInt) || first.contains('\\'.toInt)
      case _ => true

  /** The least number of binders around the term under which it is closed.
    */
  private def looseness(term: DeBruijnTerm): Int = term match
    case DeBruijnTerm.Variable(index) => index + 1
    case DeBruijnTerm.Lambda(body)    => math.max(0, looseness(body) - 1)
    case DeBruijnTerm.Apply(function, argument) =>
      math.max(looseness(function), looseness(argument))
    case DeBruijnTerm.Choice(left, right) =>
      math.max(looseness(left), looseness(right))
    case DeBruijnTerm.Parallel(left, right) =>
      math.max(looseness(left), looseness(right))
    case DeBruijnTerm.Constant(_) | DeBruijnTerm.Free(_) => 0
