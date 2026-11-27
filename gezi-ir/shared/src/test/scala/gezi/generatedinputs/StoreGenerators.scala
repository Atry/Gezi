package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.NonEmptyHoles
import gezi.ir.TermConstruction
import gezi.ir.Hole
import gezi.ir.Store
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** A generated store, with its instructions in the order they were generated
  * (the noinline ones first) and the codes its thunks may name.
  */
final case class GeneratedStore(store: Store[StandInStorages.type], instructions: Vector[StandInStorages.Term], codes: Set[Code])

/** Generators of well-formed stores of generic layers, no Gezi data:
  * opaque noinline instructions, then instructions each over instructions generated before
  * it (so the instructions are acyclic), every thunk's code reading the slots 0
  * to n - 1 exactly, its holes bound to distinct slots of them, and its
  * fillings as many as its slots that are no hole.
  */
object StoreGenerators:


  private val slot0 = Code(Slot(0))
  private val slot1 = Code(Slot(1))
  private val slot2 = Code(Slot(2))
  private val application = Code(Apply(slot0, slot1))
  private val innerChoice = Code(Choice(slot1, slot2))

  /** The codes a thunk may name, each with the number of slots it reads:
    * `slot 0`, `slot 0 slot 1`, `slot 1 ∥ slot 0`, `(slot 0 slot 1) slot
    * 2`, the right-nested choice `slot 0 + (slot 1 + slot 2)` and a code
    * that holds an inner thunk.
    */
  private val slotCounts: Vector[(Code, Int)] = Vector(
    slot0 -> 1,
    application -> 2,
    Code(Parallel(slot1, slot0)) -> 2,
    Code(Apply(application, slot2)) -> 3,
    Code(Choice(slot0, innerChoice)) -> 3,
    Code(Thunk(application, Vector(Hole.Bound(1)), Vector(slot0))) -> 1
  )

  /** Every code a generated store holds: the codes of `slotCounts` and
    * their subcodes.
    */
  val codes: Set[Code] =
    slotCounts.map(_._1).toSet ++ Set(slot0, slot1, slot2, application, innerChoice)

  /** A store of `leaves` noinline instructions (1 to 4), followed by 0 to a third
    * of Hedgehog's size of layered instructions. Each layer is an application, a
    * parallel, a binary choice or a thunk, off any instruction; one layer in five
    * repeats an earlier layer, which interning makes the earlier instruction again.
    */
  val store: Gen[GeneratedStore] =
    for
      leaves <- Gen.int(Range.linear(1, 4))
      count <- Gen.sized(size => Gen.int(Range.linear(0, size.value / 3)))
      noinline = (0 until leaves).toVector.map(position => StandInStorages.opaque(s"leaf $position"))
      layers <- layered(noinline, count, thunks = true)
    yield GeneratedStore(Store(noinline.toSet, TermConstruction(StandInStorages)), (noinline ++ layers).distinct, codes)

  /** The stores of `store` with no thunk among their layers, so that no β
    * redex is in them: applications, parallels and choices over the
    * noinline instructions and earlier layers, at most 4 + 33 distinct
    * instructions under Hedgehog's largest size, 99.
    */
  val storeWithoutThunks: Gen[GeneratedStore] =
    for
      leaves <- Gen.int(Range.linear(1, 4))
      count <- Gen.sized(size => Gen.int(Range.linear(0, size.value / 3)))
      noinline = (0 until leaves).toVector.map(position => StandInStorages.opaque(s"leaf $position"))
      layers <- layered(noinline, count, thunks = false)
    yield GeneratedStore(Store(noinline.toSet, TermConstruction(StandInStorages)), (noinline ++ layers).distinct, codes)

  private def layered(atoms: Vector[StandInStorages.Term], count: Int, thunks: Boolean): Gen[Vector[StandInStorages.Term]] =
    (0 until count).foldLeft(Gen.constant(Vector.empty[StandInStorages.Term])) { (gathered, _) =>
      for
        earlier <- gathered
        next <- layer(atoms ++ earlier, earlier, thunks)
      yield earlier :+ next
    }

  /** A layer over the given instructions, or a repeat of an earlier layer;
    * a thunk among them when `thunks`.
    */
  private def layer(instructions: Vector[StandInStorages.Term], earlier: Vector[StandInStorages.Term], thunks: Boolean): Gen[StandInStorages.Term] =
    val child = Gen.element(instructions.head, instructions.tail.toList)
    // The stand-in specializer converts no parallel.
    val kinds = List(
      4 -> (for function <- child; argument <- child yield StandInStorages.application(function, argument)),
      1 -> (for left <- child; right <- child yield StandInStorages.parallel(left, right)),
      1 -> (for left <- child; right <- child yield StandInStorages.choice(left, right))
    ) ++ (if thunks then List(3 -> thunk(child)) else Nil)
    val fresh = Gen.frequency1(kinds.head, kinds.tail*)
    if earlier.isEmpty then fresh
    else Gen.frequency1(4 -> fresh, 1 -> Gen.element(earlier.head, earlier.tail.toList))

  /** A thunk: a code of `slotCounts`, one to three binders, the first k
    * bound to the slots k - 1 down to 0 and the rest ignored, and a filling
    * for every slot from k up.
    */
  private def thunk(child: Gen[StandInStorages.Term]): Gen[StandInStorages.Term] =
    for
      (code, slots) <- Gen.element(slotCounts.head, slotCounts.tail.toList)
      binders <- Gen.int(Range.linear(1, 3))
      bound <- Gen.int(Range.constant(0, math.min(binders, slots)))
      fillings <- child.list(Range.singleton(slots - bound))
    yield
      val holes = (0 until binders).toVector.map(position =>
        if position < bound then Hole.Bound(bound - 1 - position) else Hole.Ignored
      )
      StandInStorages.thunk(code, NonEmptyHoles(holes.head, holes.tail), fillings.toVector)
