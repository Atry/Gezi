package gezi.traceplayer

import gezi.ir
import gezi.ir.Code
import gezi.locations.BinderOrigin
import gezi.locations.Location
import gezi.locations.SourceMap
import gezi.locations.Span

/** The source of a page's start, the text the start is written in
  * (`gezi.rewritetrace.TraceStart.written`): the start's text as code points,
  * the span of the start in it, and where the start's places come from
  * (`SourceMap`). The names it gives a binder are the source's own, taken from
  * the text of an occurrence of the binder's variable, and the place of a node
  * is its line and column counted from the start's first line.
  */
final case class StartSource(
    codePoints: Vector[Int],
    start: Span,
    map: SourceMap
):

  /** The names of the slots of a thunk's code that the source spells: each slot
    * to the text of an occurrence of it in the code, read through inner thunks,
    * whose slots the code fills with its own (`SourceNames`).
    */
  def slotNames(code: Code, codeMap: SourceMap): Map[Int, String] =
    SourceNames.slotNames(code, codeMap, codePoints)

  /** The names the source writes at a thunk's binders, in lambda order: the
    * names of the binders' written origins in the thunk's map
    * (`BinderOrigin.Written`, which the front end records for each binder it
    * reads, whether the text spells it `λa b.` or `λa. λb.`), the least where a
    * binder has several; none for a binder with no written origin.
    */
  def binderNames(map: SourceMap, holeCount: Int): Vector[Option[String]] =
    Vector.tabulate(holeCount)(position =>
      map.binders
        .lift(position)
        .flatMap(_.collect { case BinderOrigin.Written(name, _) =>
          name
        }.minOption)
    )

  /** The place of a node, `line:column` from the start's first line, both
    * counted from 1, of the first location the map gives it in the text; none
    * for a node the reader did not locate.
    */
  def place(map: SourceMap): Option[String] =
    map.locations.toVector
      .collect { case Location.Source(_, span) => span.start }
      .minOption
      .map(offset =>
        val before = codePoints.slice(start.start, offset)
        val line = before.count(_ == '\n') + 1
        val column = before.length - (before.lastIndexOf('\n') + 1) + 1
        s"$line:$column"
      )

object SourceNames:

  /** The text of each slot of the code that an occurrence of it spells: walking
    * the code and its map together, a slot leaf located in the text names its
    * slot; under an inner thunk, the names its code gives its own slots name
    * the slots of this code that fill them. A slot with no located occurrence
    * has no name. Recursive on the code's depth, as the player's drawing of a
    * code is (`CodeDisplay`).
    */
  def slotNames(
      code: Code,
      codeMap: SourceMap,
      codePoints: Vector[Int]
  ): Map[Int, String] =
    def located(map: SourceMap): Option[String] =
      map.locations.toVector.collectFirst { case Location.Source(_, span) =>
        span.of(codePoints)
      }
    def walked(
        at: Code,
        map: SourceMap,
        found: Map[Int, String]
    ): Map[Int, String] =
      at.layer match
        case ir.Slot(index) =>
          if found.contains(index) then found
          else located(map).fold(found)(name => found.updated(index, name))
        case ir.Apply(function, argument) =>
          walkedParts(Vector(function, argument), map, found)
        case ir.Parallel(left, right) =>
          walkedParts(Vector(left, right), map, found)
        case ir.Choice(left, right) =>
          walkedParts(Vector(left, right), map, found)
        case ir.Thunk(inner, holes, fillings) =>
          val innerNames = map.code.fold(Map.empty[Int, String])(innerMap =>
            slotNames(inner, innerMap, codePoints)
          )
          val boundSlots = holes.collect { case ir.Hole.Bound(slot) =>
            slot
          }.toSet
          val fillingSlots = (0 until boundSlots.size + fillings.size)
            .filterNot(boundSlots.contains)
          val throughInner = fillingSlots.zip(fillings).foldLeft(found) {
            case (current, (innerSlot, filling)) =>
              (filling.layer, innerNames.get(innerSlot)) match
                case (ir.Slot(outer), Some(name)) if !current.contains(outer) =>
                  current.updated(outer, name)
                case _ => current
          }
          walkedParts(fillings, map, throughInner)
    def walkedParts(
        parts: Vector[Code],
        map: SourceMap,
        found: Map[Int, String]
    ): Map[Int, String] =
      parts.zipWithIndex.foldLeft(found) { case (current, (part, index)) =>
        walked(
          part,
          map.children.lift(index).getOrElse(SourceMap.unlocated),
          current
        )
      }
    walked(code, codeMap, Map.empty)
