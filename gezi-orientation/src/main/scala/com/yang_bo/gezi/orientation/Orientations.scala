package com.yang_bo.gezi.orientation

import com.yang_bo.gezi.ir.Pattern
import com.yang_bo.gezi.ir.Spine
import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}

/** What is computed from orientations alone, as the Prolog baseline computes it
  * when it files them (`orientation_filed/4`).
  */
object Orientations:

  /** The orientation only unites: its added side is a metavariable, or a
    * subpattern of its matched side below the matched side's root (the
    * baseline's `contains/2`). Its seeds are tried before the others'.
    */
  def onlyUnites[C <: NativeSpecializer & Singleton](
      orientation: Orientation[C]
  ): Boolean =
    orientation.added match
      case Pattern.Metavariable(_) => true
      case added                   => contains(orientation.matched, added)

  /** The part occurs in the pattern below its root. */
  def contains[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      part: Pattern[C]
  ): Boolean =
    pattern.children.exists(child => child == part || contains(child, part))

  /** The instruction at the head of the pattern's spine and the number of
    * arguments applied to it (the baseline's `pattern_spine_head/2`).
    */
  def spineHead[C <: NativeSpecializer & Singleton](pattern: Pattern[C])(using
      C
  ): Option[(Configured[C], Int)] =
    val (head, arguments) = Spine.of(pattern)
    head match
      case Pattern.InstructionReference(instruction) =>
        Some((instruction, arguments.size))
      case _ => None

  /** The subpatterns of the pattern with their paths, in pre-order: the pattern
    * itself, then the subpatterns of each child in child order (the baseline's
    * `pattern_position/4`).
    */
  def positions[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C]
  ): Vector[(Vector[Int], Pattern[C])] =
    positionsBelow(pattern, Vector.empty)

  private def positionsBelow[C <: NativeSpecializer & Singleton](
      pattern: Pattern[C],
      path: Vector[Int]
  ): Vector[(Vector[Int], Pattern[C])] =
    (path, pattern) +: pattern.children.zipWithIndex.flatMap(
      (child, position) => positionsBelow(child, path :+ position)
    )

  /** The largest number of arguments a matched side of the orientations applies
    * each instruction to, over every application of every matched side whose
    * spine an instruction heads (the baseline's `head_arity_bounded/2`, whose
    * bounds hold per instruction over the whole set).
    */
  def headArityBounds[C <: NativeSpecializer & Singleton](
      orientations: Vector[Orientation[C]]
  )(using C): Map[Configured[C], Int] =
    orientations
      .flatMap(orientation => positions(orientation.matched))
      .collect { case (_, application @ Pattern.Apply(_, _)) =>
        spineHead(application)
      }
      .flatten
      .foldLeft(Map.empty[Configured[C], Int]) {
        case (bounds, (instruction, arity)) =>
          bounds.updated(
            instruction,
            bounds.get(instruction).fold(arity)(_ max arity)
          )
      }
