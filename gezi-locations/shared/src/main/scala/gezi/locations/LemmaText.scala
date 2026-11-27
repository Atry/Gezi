package gezi.locations

import gezi.ir.{Configured, NativeSpecializer}

/** A lemma as its knowledge file writes it, for a trace's debug information (a
  * trace shares its lemmas through β redexes, and turning the debug information
  * into lambdalattice loses everything but the variables' names, so a trace
  * writes each lemma's source location as CBOR literals): the file's URI, the
  * spans of its two sides in the file's code points, their text, and the names
  * the text uses that the file binds outside the declaration, each with its
  * value, so that a text that binds those names to their values and reads the
  * two sides reads the lemma's sides, terms of the configuration `C` the
  * lemma's sides are of. Nothing chooses by it; it is for people and tools.
  */
final case class LemmaText[C <: NativeSpecializer & Singleton](
    uri: java.net.URI,
    left: Span,
    right: Span,
    leftText: String,
    rightText: String,
    names: Vector[(String, Configured[C])]
)
