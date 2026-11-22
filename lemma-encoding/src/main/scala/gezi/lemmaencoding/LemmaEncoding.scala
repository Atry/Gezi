package gezi.lemmaencoding

import gezi.ir.LemmaIdentifier
import gezi.ir.Pattern
import gezi.standardlibrary.LemmaSides
import gezi.standardlibrary.StandardLibraryIndex

/** How an entry encodes a lemma's two closed terms as the patterns of its
  * orientations. The knowledge base gives a lemma its two closed terms only
  * (`LemmaSides`); the number of metavariables and the patterns are the
  * entry's encoding, not the framework's. The index is the one the lemma is in,
  * which an encoding may read, such as its defines.
  */
trait LemmaEncoding:
  def encoded(index: StandardLibraryIndex, sides: LemmaSides): EncodedLemma

/** A lemma as an encoding gives it: its identifier, the number of its
  * metavariables, numbered from 0, and the framework's patterns of its two
  * sides, what the orientation compiler takes and what an article states
  * and matches the lemma by.
  */
final case class EncodedLemma(lemma: LemmaIdentifier, metavariables: Int, left: Pattern, right: Pattern)
