package gezi.traceplayer

import gezi.frontend.NameSpelling

/** The key by which the URL hash names a shared instruction the printer
  * binds: the content
  * hash in its name (`NameSpelling.shared`), eight lower case hexadecimal
  * digits, followed by `-` and the ordinal from the second ordinal on,
  * `89abcdef` for `cons$merkle$89abcdef` and `89abcdef-2` for
  * `cons$merkle$89abcdef$2`.
  * The hash, not the whole name, so that the hash holds ASCII alone whatever
  * the head's name, and the key stays the instruction's from step to step,
  * its content being the same. Two instructions of one step whose hashes
  * collide under different heads have one key and are inlined together,
  * which changes only how the term is drawn: a key is display state and
  * chooses nothing in the term.
  */
object SharedKey:

  private val pattern: scala.util.matching.Regex = "[0-9a-f]{8}(-[1-9][0-9]*)?".r

  /** Whether the text is a key `of` writes. */
  def isKey(text: String): Boolean = pattern.matches(text) && !text.endsWith("-1")

  /** The key of the name, none for a name the printer did not synthesize
    * for a shared instruction, such as a known instruction's name.
    */
  def of(name: String): Option[String] =
    NameSpelling.sharedParts(name).map(parts =>
      if parts.ordinal == 1 then f"${parts.hash}%08x" else f"${parts.hash}%08x-${parts.ordinal}"
    )
