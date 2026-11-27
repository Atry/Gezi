package com.yang_bo.gezi.locations

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.LemmaIdentifier
import com.yang_bo.gezi.ir.TailRecFolds
import scala.util.control.TailCalls.TailRec
import scala.util.control.TailCalls.done
import scala.util.control.TailCalls.tailcall

/** A span of a text, from `start` included to `end` excluded, counted in code
  * points from 0, as the lambdalattice reader counts the offset of a syntax
  * error. Throws `IllegalArgumentException` for a negative start or an end
  * before the start.
  */
final case class Span(start: Int, end: Int):
  require(
    start >= 0 && end >= start,
    s"a span is no interval of a text: [$start, $end)"
  )

  /** Whether the other span lies within this one. */
  def contains(other: Span): Boolean = start <= other.start && other.end <= end

  /** The span's text in the text it is a span of, given as code points. */
  def of(codePoints: Vector[Int]): String =
    codePoints.slice(start, end).map(Character.toString(_)).mkString

/** Where a place of a term comes from.
  *
  *   - `Source`: a span of the file the URI names; written as the fragment URI
  *     `uri#char=start,end` (`written`), the notation of RFC 5147, which
  *     defines it for text/plain and counts a line ending as one character,
  *     borrowed here with offsets in code points, which agree with it on a file
  *     whose lines end in LF.
  *   - `Inlined`: a place of a β body, the place of the thunk's code it was
  *     built from, applied at the call: MLIR's CallSiteLoc, "a directed stack
  *     of location usages".
  *   - `Rewritten`: a place an instance of the lemma built, at the place of the
  *     class the instance matched.
  *
  * A place with several locations holds their set, as MLIR's FusedLoc groups
  * several.
  */
enum Location:
  case Source(uri: java.net.URI, span: Span)
  case Inlined(callee: Location, callSite: Location)
  case Rewritten(lemma: LemmaIdentifier, from: Location)

  /** The location written for a person: a fragment URI, `at` for a call,
    * `by lemma n from` for a rewrite.
    */
  def written: String = this match
    case Source(uri, span)         => s"$uri#char=${span.start},${span.end}"
    case Inlined(callee, callSite) =>
      s"${callee.written} at ${callSite.written}"
    case Rewritten(lemma, from) =>
      s"by lemma ${lemma.number} from ${from.written}"

/** Where a binder of a thunk comes from, from which a printer names its
  * variable.
  *
  *   - `Written`: a binder the text writes, its name and where the name is
  *     written.
  *   - `LiteralBit`: the binder of a bit of a literal's variable arguments
  *     partial function, the bit counted from 0, the high bit of the first
  *     byte, and the literal's bytes and where it is written.
  *   - `Enclosing`: a name a file of a directory tree is read under, which the
  *     text does not write.
  *   - `Made`: a binder a step of a trace makes, which no text wrote, by the
  *     kind of the step.
  */
enum BinderOrigin:
  case Written(name: String, location: Location)
  case LiteralBit(bytes: Vector[Byte], bit: Int, location: Location)
  case Enclosing(name: String)
  case Made(by: MadeBy)

/** The kind of a trace's step that makes a binder no text wrote: the β rule,
  * the body equation or a β conversion with a code no text the trace reads
  * holds, the η rule, a numbered equation, a lemma whose text the trace does
  * not hold, a native value's Scott constructors, the abstraction rule's
  * eigenvariables, and the abstraction of a reverse β conversion.
  */
enum MadeBy:
  case Beta, Eta, Equation, Lemma, Native, Eigenvariable, ReverseBeta

/** The locations of each place of one occurrence of an IR term, of the same
  * shape as the occurrence: the locations of the place itself; for a thunk, the
  * map of its code (`code`), whose places are the code's layers, a `Slot` a
  * leaf, or the map of the occurrence of the filling the slot reads at that
  * place, so that each occurrence of a filling keeps its own map; and the maps
  * of the places one layer below (`children`), a filling's the maps of its
  * occurrences merged, in the order of `Layer.children` or of a code layer's
  * parts (function then argument, left then right, an inner thunk's fillings in
  * order). A place no reader located has no location, and a place with no code
  * and no children locates nothing below it, as the place of a library's
  * instruction, whose layers the reader never saw. A thunk's place, an
  * instruction's or a code's, holds the origins of its binders in lambda order
  * (`binders`), one set for each binder, none where no reader gave them.
  */
final case class SourceMap(
    locations: Set[Location],
    code: Option[SourceMap],
    children: Vector[SourceMap],
    binders: Vector[Set[BinderOrigin]]
):

  /** Whether the map locates nothing below its place. */
  def bare: Boolean = code.isEmpty && children.isEmpty && binders.isEmpty

  /** The map of two occurrences of one term: every place holds the locations of
    * both, a bare place taking the other's places below it. Throws
    * `IllegalArgumentException` for maps of different shapes, which are no maps
    * of one term.
    */
  def merged(other: SourceMap): SourceMap = SourceMap.merged(this, other).result

object SourceMap:

  /** A place with no location and nothing below it. */
  val unlocated: SourceMap =
    SourceMap(Set.empty, None, Vector.empty, Vector.empty)

  /** A place with its locations and nothing below it. */
  def leaf(locations: Set[Location]): SourceMap =
    if locations.isEmpty then unlocated
    else SourceMap(locations, None, Vector.empty, Vector.empty)

  /** The map of a place with its parts, `unlocated` itself when neither the
    * place nor anything below it is located, since such a map locates nothing
    * below its place: a term read with no spans builds no map of its shape.
    */
  def of(
      locations: Set[Location],
      code: Option[SourceMap],
      children: Vector[SourceMap],
      binders: Vector[Set[BinderOrigin]]
  ): SourceMap =
    if locations.isEmpty && binders.isEmpty && code.forall(
        _ eq unlocated
      ) && children.forall(_ eq unlocated)
    then unlocated
    else SourceMap(locations, code, children, binders)

  /** `of` a place of two parts and no code. */
  def pair(
      locations: Set[Location],
      left: SourceMap,
      right: SourceMap
  ): SourceMap =
    if locations.isEmpty && (left eq unlocated) && (right eq unlocated) then
      unlocated
    else SourceMap(locations, None, Vector(left, right), Vector.empty)

  /** The map of the code alone: the map with each slot's place a leaf at its
    * locations, an inner thunk's code included. A slot's place may hold the map
    * of the occurrence of the filling it reads, which belongs to that thunk's
    * fillings; the code alone is what the map of another thunk of the code,
    * whatever its fillings, may take.
    */
  def codeAlone(code: Code, map: SourceMap): SourceMap =
    codeAloneWalked(code, map).result

  private def codeAloneWalked(code: Code, map: SourceMap): TailRec[SourceMap] =
    if map.bare then done(map)
    else
      code match
        case Code.Slot(_)                   => done(leaf(map.locations))
        case Code.Apply(function, argument) =>
          partsAlone(Vector(function, argument), map)
        case Code.Choice(left, right)   => partsAlone(Vector(left, right), map)
        case Code.Parallel(left, right) => partsAlone(Vector(left, right), map)
        case Code.Thunk(inner, _, fillings) =>
          for
            innerMap <- map.code.fold(done(Option.empty[SourceMap]))(innerMap =>
              tailcall(codeAloneWalked(inner, innerMap)).map(Some(_))
            )
            alone <- partsAlone(fillings, map)
          yield alone.copy(code = innerMap)

  private def partsAlone(
      parts: Vector[Code],
      map: SourceMap
  ): TailRec[SourceMap] =
    TailRecFolds
      .folded(parts.zip(map.children).toVector, Vector.empty[SourceMap])(
        (found, pair) => codeAloneWalked(pair._1, pair._2).map(found :+ _)
      )
      .map(children => map.copy(children = children))

  /** `merged`, with no JVM stack per level. A map merged with itself is itself,
    * returned without a walk: a printer merges the map of each occurrence of a
    * shared instruction, most of them one object (measured 2026-11-19 on
    * `contest-entries-wren`'s calls_1000_hot direct point in `EntryTracesTest`:
    * merging took 1,207 of the printer's 1,638 samples).
    */
  private def merged(left: SourceMap, right: SourceMap): TailRec[SourceMap] =
    val locations = left.locations ++ right.locations
    if left eq right then done(left)
    else if left.bare then done(right.copy(locations = locations))
    else if right.bare then done(left.copy(locations = locations))
    else
      require(
        left.code.isDefined == right.code.isDefined && left.children.size == right.children.size &&
          (left.binders.isEmpty || right.binders.isEmpty || left.binders.size == right.binders.size),
        "source maps of one term have one shape"
      )
      val binders =
        if left.binders.isEmpty then right.binders
        else if right.binders.isEmpty then left.binders
        else left.binders.lazyZip(right.binders).map(_ ++ _)
      for
        code <- left.code.zip(right.code) match
          case Some((leftCode, rightCode)) =>
            tailcall(merged(leftCode, rightCode)).map(Some(_))
          case None => done(None)
        children <- TailRecFolds.folded(
          left.children.zip(right.children).toVector,
          Vector.empty[SourceMap]
        )((found, pair) => merged(pair._1, pair._2).map(found :+ _))
      yield SourceMap(locations, code, children, binders)
