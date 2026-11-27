package gezi.narrowblocks

import gezi.ir.{Closed, Configured, NativeSpecializer}
import gezi.jit.{JitValue, RepresentedStorage, StorageOf}

/** The terms a native storage holds, which the check's walks go on into: the walks never read a storage's view, one
  * layer or recursively, but ask the storage what it holds (a list's items, a declared value's fields, a field held
  * as written), and a storage that holds none, a natural or a word or an array list, is skipped whole at the cost of
  * one question.
  */
object StorageHeldTerms:

  /** The terms the storage holds, read off its own data with no view: none for a term that is no storage; a group's
    * are those of its members. A held object that is no term of the IR (a value holding a suspension) is left out:
    * the narrow grammar reads no such term.
    */
  def of[C <: NativeSpecializer & Singleton](storage: Configured[C])(using C): Vector[Configured[C]] =
    val closed = Closed.of(storage)
    StorageOf.read(closed) match
      case Some(single) => heldBy(single)
      case None =>
        StorageOf.group(closed) match
          case Some(group) => group.members.flatMap(heldBy[C])
          case None        => Vector.empty

  private def heldBy[C <: NativeSpecializer & Singleton](storage: RepresentedStorage[JitValue[C]])(using C): Vector[Configured[C]] =
    val terms = StorageOf.constructed(storage) match
      case Some(constructed) => constructed.fields
      case None              => StorageOf.nativeValue(storage).heldTerms
    terms.flatMap(term => Closed.configured(term))
