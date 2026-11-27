package gezi.frontend

import scala.reflect.NameTransformer

/** The spelling of a name of lambdalattice text, the rule Name of
  * `Lambdalattice`'s grammar, and the escape that spells any text as one.
  *
  * The rule is Scala's for an alphanumeric identifier, with Scala's `$` escape
  * and without its backquoted names, since a backquote touching a name starts a
  * prefixed string of the diagnostic notation): a name starts with a letter,
  * `_` or `$` and goes on with those and the digits 0 to 9. A letter is a code
  * point `Character.isLetter` holds of, other than λ, which is the
  * abstraction's token. Scala's operator suffix after `_` (`name_+`) is not
  * read.
  *
  * The escape is `scala.reflect.NameTransformer`'s, which writes an operator
  * character as its name (`+` as `$plus`) and any other character that is no
  * part of a Java identifier as `$u` and four upper case hexadecimal digits,
  * extended so that the escape is one to one and its result is always a name:
  * `$` itself is written `$u0024`, and a character the rule does not admit
  * where it stands (λ, a digit first, a character Java admits and the rule does
  * not) is written as `$u` and its code, and so is `_` when it is the whole
  * text, since `_` alone binds a variable no text can refer to
  * (`UnboundName("_")`). So `unescaped(escaped(text)) == text` for every text,
  * and `escaped(text)` is a name, which `NameSpellingLawTest` checks.
  * scala-library holds `NameTransformer` on the JVM and on Scala.js alike, so
  * the player decodes a name as the JVM encoded it.
  */
object NameSpelling:

  /** Whether a name may start with the code point. */
  def isStart(codePoint: Int): Boolean =
    codePoint == '_' || codePoint == '$' || (Character.isLetter(
      codePoint
    ) && codePoint != 'λ')

  /** Whether a name may go on with the code point. */
  def isContinuation(codePoint: Int): Boolean =
    isStart(codePoint) || (codePoint >= '0' && codePoint <= '9')

  /** Whether the atom is spelled by the rule. */
  def isName(atom: String): Boolean =
    codePoints(atom) match
      case first +: rest => isStart(first) && rest.forall(isContinuation)
      case _             => false

  /** The code points of the text, walked by `codePointAt` rather than read from
    * `String.codePoints`, whose `java.util.stream.IntStream` Scala.js's Java
    * library lacks (the project `frontend-js`).
    */
  private def codePoints(text: String): Vector[Int] =
    Vector.unfold(0)(offset =>
      Option.when(offset < text.length) {
        val codePoint = text.codePointAt(offset)
        (codePoint, offset + Character.charCount(codePoint))
      }
    )

  /** The name that spells the text, one a text can refer to. Throws
    * `IllegalArgumentException` for the empty text, which no name spells.
    */
  def escaped(text: String): String =
    if text.isEmpty then
      throw IllegalArgumentException("no name spells the empty text")
    else if text == "_" then unicodeEscape('_')
    else
      text.toVector.zipWithIndex
        .map((character, index) => escapedCharacter(character, index == 0))
        .mkString

  /** The text the name spells: the inverse of `escaped`. */
  def unescaped(name: String): String = NameTransformer.decode(name)

  private def escapedCharacter(character: Char, first: Boolean): String =
    val transformed = NameTransformer.encode(character.toString)
    val admitted = if first then isStart(character.toInt)
    else isContinuation(character.toInt)
    if character == '$' then unicodeEscape(character)
    else if transformed != character.toString then transformed
    else if admitted then transformed
    else unicodeEscape(character)

  private def unicodeEscape(character: Char): String =
    f"$$u${character.toInt}%04X"

  /** The parts of the name of an instruction the printer shares
    * (`ReadableText`): the name of the head of its application spine when the
    * head has one, its content hash, and its ordinal among the distinct
    * instructions of one text that would otherwise take the same name, 1 for
    * the first.
    */
  final case class Shared(head: Option[String], hash: Int, ordinal: Int):
    require(head.forall(isEscape), s"$head is no name the escape writes")
    require(ordinal >= 1, s"ordinal $ordinal is below 1")

  /** The name of a shared instruction, in the JVM's convention for a name a
    * compiler synthesizes, its parts joined by `$` with a word that says their
    * kind (javac's `lambda$main$0`, scalac's `foo$default$2`): the head's name,
    * `$merkle$`, the hash as eight lower case hexadecimal digits, and from the
    * second ordinal on `$` and the ordinal: `cons$merkle$89abcdef`,
    * `$merkle$89abcdef` for a head with no name, `cons$merkle$89abcdef$2`.
    *
    * No other name the printer writes has this shape: every `$` that `escaped`
    * writes starts `$u` and four hexadecimal digits or `$` and one of
    * `NameTransformer`'s operator names (`$plus`, `$amp`, `$minus`, ...), none
    * of which is `merkle` or starts it, so no escaped name holds `$merkle$`;
    * the printer's other names (a suffix `_2`, a literal's bit
    * `number_42_digit_5`, a step's `beta`) are escaped texts. So `sharedParts`
    * finds the parts of exactly these names, which `NameSpellingLawTest`
    * checks. A name written by hand may have the shape, as in Scala, whose
    * specification reserves `$` for the compiler without rejecting it; the
    * printer keeps the names of one text distinct whatever their shape, and a
    * name decides nothing.
    */
  def shared(parts: Shared): String =
    val hashed =
      s"${parts.head.getOrElse("")}$hashMarker${f"${parts.hash}%08x"}"
    if parts.ordinal == 1 then hashed else s"$hashed$$${parts.ordinal}"

  /** The word, with the `$` on either side, between a shared instruction's head
    * and its hash.
    */
  private val hashMarker = "$merkle$"

  /** The parts of a name `shared` writes, none for any other name. */
  def sharedParts(name: String): Option[Shared] =
    def hashed(text: String, ordinal: Int): Option[Shared] =
      val cut = text.length - hashMarker.length - 8
      val digits = text.drop(cut + hashMarker.length)
      Option
        .when(
          cut >= 0 && text.startsWith(hashMarker, cut) && digits.forall(
            isLowerCaseHexadecimal
          )
        )(text.take(cut))
        .filter(head => head.isEmpty || isEscape(head))
        .map(head =>
          Shared(
            Option.when(head.nonEmpty)(head),
            java.lang.Long.parseLong(digits, 16).toInt,
            ordinal
          )
        )
    val last = name.lastIndexOf('$')
    val suffix = name.drop(last + 1)
    hashed(name, 1).orElse(
      Option
        .when(
          last >= 0 && suffix.nonEmpty && suffix.length <= 9 && suffix.head != '0' && suffix
            .forall(_.isDigit)
        )(suffix.toInt)
        .filter(_ >= 2)
        .flatMap(ordinal => hashed(name.take(last), ordinal))
    )

  private def isLowerCaseHexadecimal(character: Char): Boolean =
    (character >= '0' && character <= '9') || (character >= 'a' && character <= 'f')

  /** Whether the name is the escape of a text. */
  private def isEscape(name: String): Boolean =
    name.nonEmpty && escaped(unescaped(name)) == name
