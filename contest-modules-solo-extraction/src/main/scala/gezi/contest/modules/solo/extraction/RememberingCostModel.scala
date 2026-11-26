package gezi.contest.modules.solo.extraction

import gezi.extraction.CostModel
import gezi.ir.NativeSpecializer
import gezi.extraction.Entry
import gezi.extraction.Shape
import gezi.extraction.StatelessCostModel
import gezi.saturation.StopSignal

/** A call of a cost model's candidates, the key of `RememberingCostModel`'s
  * memo: the production's shape, the entries of each child it was read over,
  * and which of the two calls it is. Two calls are one when their shapes are
  * equal, they are the same call, and their options are the same entry
  * objects position by position, compared by reference: a candidate's child
  * entries are the objects of the options it was made over, and the
  * extraction's pass at cost finds a child entry in its list by reference
  * (`CountedExtraction`'s `consistent`), so a call answered with the
  * candidates of an equal call over other objects would have them dropped.
  * The hash reads the entries' identities, never their structure.
  */
final class RememberedCall[C <: NativeSpecializer & Singleton, Cost](val shape: Shape[C], val options: Vector[Vector[Entry[C, Cost]]], val least: Boolean):

  override def equals(other: Any): Boolean = other match
    case call: RememberedCall[?, ?] =>
      call.least == least && call.shape == shape && call.options.size == options.size &&
      call.options.lazyZip(options).forall((theirs, ours) =>
        theirs.size == ours.size && theirs.lazyZip(ours).forall((their, our) => their eq our)
      )
    case _ => false

  override val hashCode: Int =
    options.foldLeft(scala.util.hashing.MurmurHash3.mix(shape.##, if least then 1 else 0)) { (hash, entries) =>
      entries.foldLeft(scala.util.hashing.MurmurHash3.mix(hash, entries.size))((within, entry) =>
        scala.util.hashing.MurmurHash3.mix(within, System.identityHashCode(entry))
      )
    }

/** The stateless model `base` with its candidates remembered within one
  * extraction (`CostModel.Memo`): a call with the arguments of an earlier one
  * is answered from the memo, every other is `base`'s and is remembered: when
  * CountedExtraction prices a production again, its options are most often
  * the ones of its previous call. The memo is a pure function's table: its
  * key holds every input of the call, the options by identity
  * (`RememberedCall`), and a call made once a stop is requested is not
  * remembered, since a base that reads `stop` (`ModuleCostModel`) may give
  * the candidates found so far.
  */
final case class RememberingCostModel[C <: NativeSpecializer & Singleton, Cost](base: StatelessCostModel[C, Cost], stop: StopSignal) extends CostModel[C, Cost]:

  type Memo = Map[RememberedCall[C, Cost], Vector[Entry[C, Cost]]]

  def emptyMemo: Memo = Map.empty

  def cost(shape: Shape[C], childCosts: Vector[Cost]): Cost = base.cost(shape, childCosts)

  def ordering: Ordering[Cost] = base.ordering

  override def sameReading(left: Cost, right: Cost): Boolean = base.sameReading(left, right)

  override def candidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]]): Vector[Entry[C, Cost]] = base.candidates(shape, options)

  /** The base's, as `candidates` is: which children the base's candidates
    * settle is a function of the same arguments, so nothing of it is
    * remembered.
    */
  override def settledChildren(shape: Shape[C], entryCounts: Vector[Int]): Vector[Boolean] = base.settledChildren(shape, entryCounts)

  def pricedChildren(shape: Shape[C]): Vector[Boolean] = base.pricedChildren(shape)

  override def droppedChildren(shape: Shape[C], childCosts: Vector[Cost]): Vector[Boolean] = base.droppedChildren(shape, childCosts)

  override def mayDropChildren(shape: Shape[C]): Vector[Boolean] = base.mayDropChildren(shape)

  override def leastCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]]): Vector[Entry[C, Cost]] =
    base.leastCandidates(shape, options)

  def memoizedCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Memo): (Vector[Entry[C, Cost]], Memo) =
    val call = RememberedCall[C, Cost](shape, options, false)
    memo.get(call) match
      case Some(found) => (found, memo)
      case None =>
        val found = base.candidates(shape, options)
        (found, if stop.stopRequested then memo else memo.updated(call, found))

  def memoizedLeastCandidates(shape: Shape[C], options: Vector[Vector[Entry[C, Cost]]], memo: Memo): (Vector[Entry[C, Cost]], Memo) =
    val call = RememberedCall[C, Cost](shape, options, true)
    memo.get(call) match
      case Some(found) => (found, memo)
      case None =>
        val found = base.leastCandidates(shape, options)
        (found, if stop.stopRequested then memo else memo.updated(call, found))
