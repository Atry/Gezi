package com.yang_bo.gezi.egraph

import com.yang_bo.gezi.ir.{Configured, LayerWith, NativeSpecializer}
import com.yang_bo.gezi.ir.NativeStorage
import com.yang_bo.gezi.ir.NoinlineLeaf

/** What a class's storage leaves give under one criterion: the one storage the
  * class holds as a leaf, or `Conflict` when it holds two distinct ones, two
  * distinct values united, an unsound union. A flat lattice: nothing below a
  * storage below `Conflict`.
  */
enum StorageLeafState:
  case Held(storage: NativeStorage)
  case Conflict

/** The storage leaves of a class, by their criterion (the specializer's
  * `criterionOf` the storage, as the object the term is): a member node of the
  * class read as a hint, never a verdict about a value's type.
  */
final case class StorageLeaves[C <: NativeSpecializer & Singleton](
    byCriterion: Map[Configured[C], StorageLeafState]
):

  /** The storages the class holds as leaves, those of a criterion in `Conflict`
    * left out.
    */
  def storages: Vector[NativeStorage] = byCriterion.values.toVector.collect {
    case StorageLeafState.Held(storage) => storage
  }

  /** Whether two distinct storages of one criterion are in the class. */
  def conflicting: Boolean =
    byCriterion.values.exists(_ == StorageLeafState.Conflict)

/** The analysis of which native storages a class holds as leaves
  * (`NativeStorage.leafInEGraph`), the storage analysis of the e-graph: a leaf
  * of a storage gives that storage under its own criterion, every other layer
  * nothing; it reads no child's value, so it is a function of the class's
  * leaves alone. Two distinct storages of one criterion in a class are two
  * distinct values united, which `joined` makes `Conflict`. The flat lattice
  * per criterion makes `joined` commutative, associative and idempotent, `made`
  * monotone (it reads no child), and every chain finite. It is a hint for a
  * rule that reads a class's storages: folding, the construction of a storage
  * one layer up, the cost of a class.
  */
final class StorageLeafAnalysis[C <: NativeSpecializer & Singleton](
    specializer: C
) extends ClassAnalysis[C, StorageLeaves[C]]:

  val identity: StorageLeaves[C] = StorageLeaves(Map.empty)

  def made(
      layer: LayerWith[StorageLeaves[C], Configured[C]]
  ): StorageLeaves[C] =
    layer match
      case NoinlineLeaf(instruction) =>
        instruction.layer match
          case storage: NativeStorage if storage.leafInEGraph =>
            StorageLeaves(
              Map(
                specializer.criterionOf(storage) -> StorageLeafState.Held(
                  storage
                )
              )
            )
          case _ => identity
      case _ => identity

  def joined(
      left: StorageLeaves[C],
      right: StorageLeaves[C]
  ): StorageLeaves[C] =
    StorageLeaves(right.byCriterion.foldLeft(left.byCriterion) {
      case (found, (criterion, state)) =>
        found.get(criterion) match
          case None => found.updated(criterion, state)
          case Some(existing) if existing == state => found
          case Some(_) => found.updated(criterion, StorageLeafState.Conflict)
    })
