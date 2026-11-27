package gezi.generatedinputs

import gezi.ir.Closed
import gezi.ir.Configured
import gezi.ir.NativeStorage
import gezi.ir.ScottReading
import gezi.ir.StorageAccess
import gezi.ir.StorageView

/** The native specializer of the tests' stand-in storages (storages whose view throws, or that hold a test's own data): it
  * converts no parallel, and makes a stand-in's term, the only way a storage enters the pool. The generated terms of the
  * tests (`StoreGenerators`) are terms of this configuration, so that they mix with the stand-ins.
  */
object StandInStorages extends gezi.ir.NativeSpecializer:

  /** A term of the stand-in configuration. */
  type Term = Configured[StandInStorages.type]

  protected def specialized(left: Closed[this.type], right: Closed[this.type]): Option[Closed[this.type]] = None

  protected def storageCriterion(storage: NativeStorage): Configured[this.type] = storage match
    case standIn: StandInStorage => standIn.standInCriterion
    case other                   => throw IllegalStateException(s"a storage that is no stand-in has no criterion here: $other")

  protected def storageView(storage: NativeStorage)(using StorageAccess): StorageView[Configured[this.type]] =
    throw IllegalStateException(s"a stand-in storage has no view: $storage")

  protected def storageScottReading(storage: NativeStorage)(using StorageAccess): ScottReading[Configured[this.type]] =
    throw IllegalStateException(s"a stand-in storage has no Scott reading: $storage")

  /** The pool's term of the stand-in. */
  def stored(storage: NativeStorage): Term = storedTerm(storage)

/** A native storage of the tests that names the criterion of its stand-in configuration, which `StandInStorages` answers
  * as the storage's `criterionOf`; its view is never read.
  */
trait StandInStorage extends NativeStorage:

  /** The criterion T of the term `v ∥ T` this storage stands for. */
  def standInCriterion: StandInStorages.Term
