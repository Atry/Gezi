package gezi.narrowblocks.groups

import gezi.ir.{Configured, NativeSpecializer}
import gezi.ir.{Apply, Choice, Opaque, Parallel, Thunk, UriNode}

/** The narrow kind of every subterm of some roots, by [[GroupGrammar]]. */
object GroupScan:

  /** The kind of every subterm of the roots, a name's (`names`) its own. */
  def kinds[C <: NativeSpecializer & Singleton](
      roots: Vector[Configured[C]],
      names: Map[Configured[C], GroupKind]
  ): Map[Configured[C], GroupKind] =
    @scala.annotation.tailrec
    def visited(
        pending: List[(Configured[C], Boolean)],
        found: Map[Configured[C], GroupKind]
    ): Map[Configured[C], GroupKind] =
      pending match
        case Nil                                                     => found
        case (instruction, _) :: rest if found.contains(instruction) =>
          visited(rest, found)
        case (instruction, _) :: rest if names.contains(instruction) =>
          visited(rest, found.updated(instruction, names(instruction)))
        case (instruction, _) :: rest if instruction.heldAsLeaf =>
          visited(rest, found.updated(instruction, GroupKind.Closed))
        case (instruction, false) :: rest =>
          visited(
            instruction.layer.children.toList
              .map((_, false)) ::: (instruction, true) :: rest,
            found
          )
        case (instruction, true) :: rest =>
          val kind = instruction.layer match
            case Apply(function, argument) =>
              GroupGrammar.applicationKind(found(function), found(argument))
            case Parallel(left, right) =>
              GroupGrammar.parallelKind(found(left), found(right))
            case Choice(left, right) =>
              GroupGrammar.choiceKind(Vector(found(left), found(right)))
            case Thunk(code, holes, fillings) =>
              GroupGrammar.thunkKind(
                code,
                holes,
                fillings.map(filling =>
                  GroupItem.Known(found(filling), filling)
                )
              )
            case UriNode(_) | Opaque(_) => GroupKind.Closed
            // A storage is a closed value, its view not read.
            case _: gezi.ir.NativeStorage => GroupKind.Closed
          visited(rest, found.updated(instruction, kind))
    visited(roots.toList.map((_, false)), Map.empty)
