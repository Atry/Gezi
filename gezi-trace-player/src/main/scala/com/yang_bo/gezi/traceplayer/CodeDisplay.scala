package com.yang_bo.gezi.traceplayer

import com.yang_bo.gezi.ir.Code
import com.yang_bo.gezi.ir.CodeLayer
import com.yang_bo.gezi.ir.Hole
import com.yang_bo.gezi.locations.SourceMap
import com.yang_bo.gezi.ir

/** A thunk's code as the player draws it inside the thunk's node: a tree whose
  * leaves are the variables of the thunk's binders and references to its
  * fillings, which the player draws as nodes of their own beside the code. An
  * inner thunk of the code is a `Lambda`, its fillings (codes read with the
  * enclosing code's slots) written in place of the inner code's slots that they
  * fill.
  *
  * A binder's variable is named as the source names it, when the page's start
  * was written from its source and the place is one the source locates
  * (`StartSource`); otherwise by the depth of its thunk, `x` for the thunk of
  * the node, `y` for a thunk inside its code, `z` below, then `x3`, `x4`, and
  * so on, followed by the binder's position in lambda order. An ignored binder
  * is `_`.
  */
enum CodeDisplay:
  case Variable(name: String)

  /** The filling of the node's thunk at the index, in slot order. */
  case Filling(index: Int)

  case Apply(function: CodeDisplay, argument: CodeDisplay)
  case Parallel(left: CodeDisplay, right: CodeDisplay)
  case Choice(left: CodeDisplay, right: CodeDisplay)
  case Lambda(binders: Vector[String], body: CodeDisplay)

  /** The display in one line: `λ x0 _. …` for a lambda, `#k` for a filling,
    * application by juxtaposition in parentheses, `+` and `∥` as in a
    * lambdalattice text.
    */
  def text: String = this match
    case Variable(name)            => name
    case Filling(index)            => s"#$index"
    case Apply(function, argument) => s"(${function.text} ${argument.text})"
    case Parallel(left, right)     => s"(${left.text} ∥ ${right.text})"
    case Choice(left, right)       => s"(${right.text} + ${left.text})"
    case Lambda(binders, body) => s"(λ ${binders.mkString(" ")}. ${body.text})"

object CodeDisplay:

  /** The variable names of the binders of a thunk at the depth: the name the
    * source gives the slot a binder binds, or one made of the depth and the
    * binder's position.
    */
  def binders(
      holes: Vector[Hole],
      depth: Int,
      names: Map[Int, String]
  ): Vector[String] =
    binders(holes, depth, names, Vector.empty)

  /** `binders` with the names the source writes at the binders themselves
    * (`StartSource.binderNames`), which name an ignored binder too and come
    * before the names of the slots' occurrences.
    */
  def binders(
      holes: Vector[Hole],
      depth: Int,
      names: Map[Int, String],
      written: Vector[Option[String]]
  ): Vector[String] =
    holes.zipWithIndex.map((hole, position) =>
      written
        .lift(position)
        .flatten
        .getOrElse(
          hole match
            case Hole.Bound(slot) =>
              names.getOrElse(slot, s"${letter(depth)}$position")
            case Hole.Ignored => "_"
        )
    )

  /** The names the source writes at the binders of a thunk of the place's map,
    * none without a source or a map.
    */
  def writtenBinders(
      map: Option[SourceMap],
      holeCount: Int,
      source: Option[StartSource]
  ): Vector[Option[String]] =
    (map, source) match
      case (Some(located), Some(start)) => start.binderNames(located, holeCount)
      case _                            => Vector.empty

  /** The names the source gives the slots of the code, none without a source or
    * a map of the code.
    */
  def slotNames(
      code: Code,
      codeMap: Option[SourceMap],
      source: Option[StartSource]
  ): Map[Int, String] =
    (codeMap, source) match
      case (Some(map), Some(start)) => start.slotNames(code, map)
      case _                        => Map.empty

  private def letter(depth: Int): String = depth match
    case 0 => "x"
    case 1 => "y"
    case 2 => "z"
    case _ => s"x${depth}_"

  /** The display of the code of the node's thunk, whose binders have the holes:
    * a slot a hole binds is that binder's variable, any other slot the filling
    * at its position among the slots no hole binds.
    */
  def of(
      code: Code,
      holes: Vector[Hole],
      written: Vector[Option[String]],
      codeMap: Option[SourceMap],
      source: Option[StartSource]
  ): CodeDisplay =
    val bound = binders(holes, 0, slotNames(code, codeMap, source), written)
    val boundSlots = holes.zipWithIndex.collect {
      case (Hole.Bound(slot), position) => (slot, Variable(bound(position)))
    }.toMap
    displayed(
      code,
      codeMap,
      source,
      slot => boundSlots.getOrElse(slot, Filling(fillingPosition(holes, slot))),
      0
    )

  /** The position of the slot among those no hole binds. */
  private def fillingPosition(holes: Vector[Hole], slot: Int): Int =
    (0 until slot).count(candidate => !holes.contains(Hole.Bound(candidate)))

  /** The display of a code at the depth, each slot shown as `slots` says.
    * Recursive on the code's depth: a thunk's code is a term's one layer, and
    * the player draws small terms.
    */
  private def displayed(
      code: Code,
      codeMap: Option[SourceMap],
      source: Option[StartSource],
      slots: Int => CodeDisplay,
      depth: Int
  ): CodeDisplay =
    def part(index: Int): Option[SourceMap] =
      codeMap.map(_.children.lift(index).getOrElse(SourceMap.unlocated))
    code.layer match
      case ir.Slot(index)               => slots(index)
      case ir.Apply(function, argument) =>
        Apply(
          displayed(function, part(0), source, slots, depth),
          displayed(argument, part(1), source, slots, depth)
        )
      case ir.Parallel(left, right) =>
        Parallel(
          displayed(left, part(0), source, slots, depth),
          displayed(right, part(1), source, slots, depth)
        )
      case ir.Choice(left, right) =>
        Choice(
          displayed(left, part(0), source, slots, depth),
          displayed(right, part(1), source, slots, depth)
        )
      case ir.Thunk(inner, holes, fillings) =>
        val innerMap = codeMap.flatMap(_.code)
        val innerBinders = binders(
          holes,
          depth + 1,
          slotNames(inner, innerMap, source),
          writtenBinders(codeMap, holes.size, source)
        )
        val innerBound = holes.zipWithIndex.collect {
          case (Hole.Bound(slot), position) =>
            (slot, Variable(innerBinders(position)))
        }.toMap
        val innerFillings = fillings.zipWithIndex.map((filling, index) =>
          displayed(filling, part(index), source, slots, depth)
        )
        def innerSlots(slot: Int): CodeDisplay =
          innerBound.getOrElse(
            slot, {
              val position = fillingPosition(holes, slot)
              require(
                innerFillings.indices.contains(position),
                s"the inner thunk reads its slot $slot, the filling $position of ${innerFillings.size}"
              )
              innerFillings(position)
            }
          )
        Lambda(
          innerBinders,
          displayed(inner, innerMap, source, innerSlots, depth + 1)
        )
