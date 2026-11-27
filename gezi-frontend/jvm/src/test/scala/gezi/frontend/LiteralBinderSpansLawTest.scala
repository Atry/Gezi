package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import scala.annotation.tailrec

/** The size of the spans the located reading gives a literal binder
  * (`Lambdalattice.located`, `SyntaxSpans`), on `λh'…' x. x` for generated
  * bytes: the paths its spans hold, summed over every node, grow linearly in
  * the literal's bits.
  *
  * Its purpose is to catch spans that write each bit's binders at its path from
  * the literal's root, Θ(b²) for b bits, which ran a reading of an exchange
  * line of 7,947 literal binders out of 5 GB.
  */
class LiteralBinderSpansLawTest extends GeneratedProperties:

  /** The length of every path the spans hold, the written subterms' and the
    * binders', summed over every node.
    */
  private def pathLengths(spans: SyntaxSpans): Long =
    @tailrec
    def summed(pending: List[SyntaxSpans], total: Long): Long = pending match
      case Nil                                            => total
      case SyntaxSpans.Written(_, _, children, _) :: rest =>
        summed(children.toList ++ rest, total)
      case SyntaxSpans.Generated(_, _, written, binders) :: rest =>
        summed(
          written.map(_._2).toList ++ rest,
          total + written.map(_._1.size).sum + binders.map(_._1.size).sum
        )
    summed(List(spans), 0L)

  property("a literal binder's spans hold paths linear in its bits") {
    for bytes <- Gen
        .byte(Range.linearFrom(0.toByte, Byte.MinValue, Byte.MaxValue))
        .list(Range.linear(0, 64))
        .forAll
    yield
      val hexadecimal = bytes.map(byte => f"${byte & 0xff}%02x").mkString
      val text = s"λh'$hexadecimal' x. x"
      val located = Lambdalattice.located(text, FreeNames.Rejected)
      // The CBOR byte string's head is one byte below 24 bytes and two up to 255.
      val bits = 8 * ((if bytes.size < 24 then 1 else 2) + bytes.size)
      val lengths = pathLengths(located.spans)
      // Each bit's level holds its binder at the empty path, the five binders
      // of its miss top at paths of four to six steps (25 in all) for a 0 and
      // three to five (20) for a 1, and the next level at two steps for a 0 and
      // three for a 1: at most 27 steps a bit.
      Result
        .assert(lengths <= 27L * bits)
        .log(s"$lengths steps of paths for $bits bits")
  }
