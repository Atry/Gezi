package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The laws of `NameSpelling`'s escape on generated texts: the escape of a text
  * is a name the reader reads as one bound variable, and unescaping it gives
  * the text back. Purpose: catch an escape that is not one to one (a `$`
  * written as itself, so that `$plus` in a text reads back as `+`), one whose
  * result the lexer splits or rejects (λ, a digit first, a character Java
  * admits in an identifier and the rule does not, `_` alone, which no text can
  * refer to), and a lexer that reads a name's `$` or letter as another token.
  */
class NameSpellingLawTest extends GeneratedProperties:

  /** Texts mixing the characters the escape treats apart: letters of both
    * cases, digits, `_`, `$`, the letters of an escape (`u`, `p`, `l`, `s`), λ,
    * operator characters, characters no name holds, and any UTF-16 unit, an
    * unpaired surrogate included.
    */
  private val text: Gen[String] =
    Gen.string(
      Gen.frequency1(
        3 -> Gen.element(
          'a',
          List('Z', '0', '9', '_', '$', 'u', 'p', 'l', 's', 'λ', 'é', '+', '.',
            '\'', '`', ' ', '∥', '\u0000')
        ),
        1 -> Gen.unicode
      ),
      Range.linear(1, 12)
    )

  property("the escape of a text is a name that unescapes to the text") {
    text.forAllWithLog(identity).map { written =>
      val name = NameSpelling.escaped(written)
      Result
        .assert(NameSpelling.isName(name))
        .log(s"not a name: $name")
        .and(Result.diff(NameSpelling.unescaped(name), written)(_ == _))
        .log(s"escaped: $name")
    }
  }

  /** The outer binder of the reading below: `$` alone, a name no escape gives,
    * since an escape writes `$` only before an operator's name or `u` and four
    * digits, so that the escape of a text never shadows it.
    */
  private val outer: String = "$"

  /** Texts of the characters a shared name and the escape's `$` meet on: the
    * letters of `merkle`, lower case hexadecimal digits, `$`, the characters
    * `NameTransformer` writes as an operator's name that starts with one of
    * them (`-` as `$minus`, `&` as `$amp`, `@` as `$at`, `!` as `$bang`, `|` as
    * `$bar`, `:` as `$colon`, `/` as `$div`, `=` as `$eq`), `\`, which it
    * writes as `$u005C`, and `u`.
    */
  private val hexadecimalText: Gen[String] =
    Gen.string(
      Gen.element(
        'a',
        List('b', 'c', 'd', 'e', 'f', 'm', 'r', 'k', 'l', '0', '1', '2', '9',
          '$', '-', '&', '@', '!', '|', '\\', ':', '/', '=', 'u', '_')
      ),
      Range.linear(1, 24)
    )

  property("no escape of a text is a shared instruction's name") {
    Gen.choice1(text, hexadecimalText).forAllWithLog(identity).map { written =>
      val name = NameSpelling.escaped(written)
      Result
        .diff(NameSpelling.sharedParts(name), None)(_ == _)
        .log(s"escaped: $name")
    }
  }

  property("a shared instruction's name is a name whose parts read back") {
    for
      head <- Gen.choice1(text, hexadecimalText).option.forAll
      hash <- Gen.int(Range.linearFrom(0, Int.MinValue, Int.MaxValue)).forAll
      ordinal <- Gen.int(Range.linear(1, 12)).forAll
    yield
      val parts =
        NameSpelling.Shared(head.map(NameSpelling.escaped), hash, ordinal)
      val name = NameSpelling.shared(parts)
      Result
        .assert(NameSpelling.isName(name))
        .log(s"not a name: $name")
        .and(Result.diff(NameSpelling.sharedParts(name), Some(parts))(_ == _))
        .log(s"shared: $name")
  }

  property("the reader reads the escape of a text as one bound variable") {
    text.forAllWithLog(identity).map { written =>
      val name = NameSpelling.escaped(written)
      Result
        .diff(
          Lambdalattice.term(s"λ$outer $name. $name $outer"),
          Lambdalattice.term("λa b. b a")
        )(_ == _)
        .log(s"escaped: $name")
    }
  }
