package com.yang_bo.gezi.jit

import com.yang_bo.gezi.ir.{Configured, NativeSpecializer}
import com.yang_bo.gezi.weakhead.AnswerSet

/** Whether the instance table's answers outlive the version of the contents the
  * URI nodes expand to (`com.yang_bo.gezi.hotspot.ExpansionSource`): a choice of the
  * entry's data, whose cost it changes and never an answer.
  *
  * An instance's reading is a pure function of its key and of what it read: the
  * expansions of URI nodes and the answers of other instances. So a table read
  * under an earlier version still holds when each of those reads gives what it
  * gave then, checked in the order they were made, each instance read being
  * checked the same way or read again. A read whose answer is unchanged stops
  * the change from reaching the tables that read it, however much changed below
  * it: the verifying trace with early cutoff of build systems (A. Mokhov, N.
  * Mitchell, S. Peyton Jones, Build Systems à la Carte, ICFP 2018).
  */
enum InstanceReuse:

  /** Every answer dropped under a new version. */
  case WithinVersion

  /** The answers kept with what they read, and verified before they are used
    * under a new version (`JitRunState.earlierVerifiable`).
    */
  case VerifiedAcrossVersions

/** One thing an instance's reading read, as it is noted while the reading runs
  * (`JitRunState.readNoted`).
  */
enum InstanceRead[C <: NativeSpecializer & Singleton]:

  /** The answers of the instance of the key. */
  case Table(key: TabledInstance[C])

  /** The expansion of the URI node. */
  case Expansion(node: Configured[C], expansion: Configured[C])

/** What the readings of an instance read so far, each once, in the order first
  * read. Readings run again by their component's iteration add to it, so it
  * holds at least what the last iteration read.
  *
  * @param opaque
  *   whether a reading also took an answer from a memo that records no read (a
  *   decode point's), so that the trace does not say all it depends on
  */
final case class ReadTrace[C <: NativeSpecializer & Singleton](
    reads: Vector[InstanceRead[C]],
    seen: Set[InstanceRead[C]],
    opaque: Boolean
):

  /** The trace with the read added, unless it holds it. */
  def read(instanceRead: InstanceRead[C]): ReadTrace[C] =
    if seen.contains(instanceRead) then this
    else copy(reads :+ instanceRead, seen + instanceRead)

  /** The trace of the readings of both. */
  def joined(other: ReadTrace[C]): ReadTrace[C] =
    other.reads.foldLeft(if other.opaque then copy(opaque = true) else this)(
      _.read(_)
    )

object ReadTrace:

  /** Nothing read. */
  def empty[C <: NativeSpecializer & Singleton]: ReadTrace[C] =
    ReadTrace[C](Vector.empty, Set.empty, false)

/** A read of a completed component with what it gave. */
enum HeldRead[C <: NativeSpecializer & Singleton]:

  /** The instance of the key, whose complete table held the answers. */
  case Table(key: TabledInstance[C], answers: AnswerSet[JitHead[C]])

  /** The URI node, which expanded to the expansion. */
  case Expansion(node: Configured[C], expansion: Configured[C])

/** A complete table with the reads outside its component that its answers are a
  * function of, in the order they were made.
  */
final case class VerifiableTable[C <: NativeSpecializer & Singleton](
    answers: AnswerSet[JitHead[C]],
    reads: Vector[HeldRead[C]]
)
