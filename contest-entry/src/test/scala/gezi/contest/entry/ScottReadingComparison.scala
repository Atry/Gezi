package gezi.contest.entry

import gezi.ir.NativeSpecializer
import gezi.ir.StorageAccess
import gezi.weakhead.ScottADTChoices

/** How the group block laws compare two readings of programs: by their Scott
  * ADT values (`ScottADTChoices`), the observation an entry makes of a program,
  * never by the terms' spellings.
  */
object ScottReadingComparison:

  /** Two readings alike: both stopped, or both finished with the same Scott ADT
    * values and the same flags.
    */
  def sameReadings[C <: NativeSpecializer & Singleton](
      left: Option[ScottADTChoices.Read[C]],
      right: Option[ScottADTChoices.Read[C]]
  )(using C, StorageAccess): Boolean = (left, right) match
    case (None, None)                => true
    case (Some(first), Some(second)) =>
      ScottADTChoices.same(first.choices, second.choices) &&
      first.nothingDropped == second.nothingDropped && first.noChoiceSplit == second.noChoiceSplit
    case _ => false

  /** The reading is the union of the parts: it stopped exactly when one of the
    * parts did, and otherwise its Scott ADT values are the parts' together
    * (each member of one is a member of the other side).
    */
  def sameAsUnion[C <: NativeSpecializer & Singleton](
      actual: Option[ScottADTChoices.Read[C]],
      parts: Vector[Option[ScottADTChoices.Read[C]]]
  )(using C, StorageAccess): Boolean =
    if parts.exists(_.isEmpty) then actual.isEmpty
    else
      actual.exists { read =>
        val found = ScottADTChoices.members(read.choices)
        val expected =
          parts.flatten.flatMap(part => ScottADTChoices.members(part.choices))
        found.forall(member =>
          expected.exists(ScottADTChoices.same(member, _))
        ) &&
        expected.forall(member => found.exists(ScottADTChoices.same(member, _)))
      }

  /** The number of Scott ADT values of a finished reading. */
  def memberCount[C <: NativeSpecializer & Singleton](
      read: Option[ScottADTChoices.Read[C]]
  )(using C, StorageAccess): Option[Int] =
    read.map(found => ScottADTChoices.members(found.choices).size)
