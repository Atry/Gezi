package com.yang_bo.gezi.lemmaencoding

import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.NativeSpecializer
import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.standardlibrary.LemmaSides
import com.yang_bo.gezi.standardlibrary.StandardLibraryIndex

/** How an entry encodes a lemma's two closed terms as the patterns of its
  * orientations. The knowledge base gives a lemma its two closed terms only
  * (`LemmaSides`); the number of metavariables and the patterns are the entry's
  * encoding, not the framework's. The index is the one the lemma is in, which
  * an encoding may read, such as its defines.
  */
trait LemmaEncoding:
  def encoded[C <: NativeSpecializer & Singleton](
      index: StandardLibraryIndex[C],
      sides: LemmaSides[C]
  ): EncodedLemma[C]

/** A lemma as an encoding gives it: its identifier, the number of its
  * metavariables, numbered from 0, and the framework's patterns of its two
  * sides, what the orientation compiler takes and what an article states and
  * matches the lemma by.
  */
final case class EncodedLemma[C <: NativeSpecializer & Singleton](
    lemma: LemmaIdentifier,
    metavariables: Int,
    left: Pattern[C],
    right: Pattern[C]
)
