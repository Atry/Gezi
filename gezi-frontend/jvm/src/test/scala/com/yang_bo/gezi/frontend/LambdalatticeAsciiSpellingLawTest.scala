package com.yang_bo.gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.generatedinputs.LambdalatticeText
import scala.jdk.StreamConverters.*

/** The law that the text of a generated term, applied to a generated string
  * literal, parses to the same term when each λ outside the string is spelled
  * `\` and each ∥ is spelled `||`, the spelling chosen per occurrence so that
  * one text mixes both: its purpose is to catch an ASCII spelling the lexer
  * misses or reads as another token, a `||` read as two tokens, or a `\`, `|`,
  * λ or ∥ inside a string read as anything but the string's text.
  */
class LambdalatticeAsciiSpellingLawTest extends GeneratedProperties:

  private val lambda: Int = 'λ'

  private val parallel: Int = 0x2225

  private def respellable(codePoint: Int): Boolean =
    codePoint == lambda || codePoint == parallel

  /** The text with its n-th λ or ∥ spelled `\` or `||` when the n-th choice is
    * true and left as it is otherwise; the text must hold no string literal and
    * exactly as many λ and ∥ as there are choices.
    */
  private def respelled(text: String, asciiChoices: List[Boolean]): String =
    val (unusedChoices, fragments) =
      text.codePoints
        .toScala(Vector)
        .foldLeft((asciiChoices, List.empty[String])) {
          case ((ascii :: rest, written), codePoint)
              if respellable(codePoint) =>
            val spelling =
              if !ascii then Character.toString(codePoint)
              else if codePoint == lambda then "\\"
              else "||"
            (rest, spelling :: written)
          case ((Nil, _), codePoint) if respellable(codePoint) =>
            throw AssertionError("more λ and ∥ than choices")
          case ((choices, written), codePoint) =>
            (choices, Character.toString(codePoint) :: written)
        }
    assert(unusedChoices.isEmpty, s"${unusedChoices.size} choices left over")
    fragments.reverse.mkString

  /** A string literal's text, drawn from the characters the ASCII spellings and
    * the escapes use and a letter.
    */
  private val literalText: Gen[String] =
    Gen.string(
      Gen.element('λ', List('∥', '\\', '|', '"', 'a')),
      Range.linear(0, 8)
    )

  property(
    "the ASCII spellings of λ and ∥ parse to the term the Unicode spellings give"
  ) {
    for
      term <- HoasGenerators.closedTerm.forAllWithLog(LambdalatticeText.text(_))
      termText = LambdalatticeText.text(term)
      asciiChoices <- Gen.boolean
        .list(
          Range.singleton(
            termText.codePoints.toScala(Vector).count(respellable)
          )
        )
        .forAll
      literal <- literalText.forAll
    yield
      val escaped = literal.flatMap {
        case '"'   => "\\\""
        case '\\'  => "\\\\"
        case other => other.toString
      }
      val unicodeText = s"($termText) \"$escaped\""
      val mixedText = s"(${respelled(termText, asciiChoices)}) \"$escaped\""
      val unicodeTerm = Lambdalattice.term(unicodeText)
      Result.all(
        List(
          Result.diff(Lambdalattice.term(mixedText), unicodeTerm)(_ == _),
          Result.diff(
            unicodeTerm,
            Literals
              .arguments(Literal.text(literal))
              .foldLeft(term.locallyNamelessTerm)(DeBruijnTerm.Apply(_, _))
          )(_ == _)
        )
      )
  }
