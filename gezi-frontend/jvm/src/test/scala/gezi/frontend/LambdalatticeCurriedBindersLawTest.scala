package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText

/** The law that one λ with several binders, names and literals mixed, reads as
  * one λ for each binder: `λb₁ b₂ … bₙ. M` reads as `λb₁. λb₂. … λbₙ. M`, the
  * body applying a generated closed term to every name bound. Its purpose is to
  * catch a binder after the first read as anything but one more abstraction
  * around the rest, a name whose index forgets the abstractions a literal
  * binder before or after it spreads into, or a body read outside the scope of
  * the later binders.
  */
class LambdalatticeCurriedBindersLawTest extends GeneratedProperties:

  /** A literal binder's spelling: strings, the empty one included, integers,
    * which stop before the dot after the last binder, an array, a tag, and
    * literals alone in parentheses, a number with a fraction among them, since
    * a bare binder holds no `.` outside its quotes and brackets.
    */
  private val literalBinder: Gen[String] =
    Gen.element(
      "\"k\"",
      List(
        "\"\"",
        "\"ab\"",
        "0",
        "12",
        "[1, 2]",
        "30([1])",
        "(3.0)",
        "(30([1.5]))"
      )
    )

  property("one λ with several binders reads as one λ for each binder") {
    for
      literalChoices <- Gen.boolean.list(Range.linear(1, 5)).forAll
      literals <- literalBinder
        .list(Range.singleton(literalChoices.size))
        .forAll
      function <- HoasGenerators.closedTerm.forAllWithLog(
        LambdalatticeText.text
      )
    yield
      val binders = literalChoices.zip(literals).zipWithIndex.map {
        case ((isLiteral, literal), index) =>
          if isLiteral then literal else s"x$index"
      }
      val names = binders.filter(_.startsWith("x"))
      val body =
        (s"(${LambdalatticeText.text(function)})" :: names).mkString(" ")
      val curried = s"λ${binders.mkString(" ")}. $body"
      val separate = binders.map(binder => s"λ$binder. ").mkString + body
      Result.diff(Lambdalattice.term(curried), Lambdalattice.term(separate))(
        _ == _
      )
  }
