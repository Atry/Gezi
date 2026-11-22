package gezi.generatedinputs

import hedgehog.Gen
import hedgehog.Range
import gezi.ir.CodeLayer
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Hole
import gezi.ir.Layer
import gezi.ir.Store
import gezi.ir.{Apply, Choice, Parallel, Slot, Thunk}

/** A generated store, with its instructions in the order they were generated
  * (the noinline ones first) and the codes its thunks may name.
  */
final case class GeneratedStore(store: Store, instructions: Vector[Instruction], codes: Set[Code])

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
      noinline = (0 until leaves).toVector.map(position => Instruction.opaque(s"leaf $position"))
      layers <- layered(noinline, count)
    yield GeneratedStore(Store(noinline.toSet), (noinline ++ layers.map(Instruction(_))).distinct, codes)

  private def layered(atoms: Vector[Instruction], count: Int): Gen[Vector[Layer[Instruction]]] =
    (0 until count).foldLeft(Gen.constant(Vector.empty[Layer[Instruction]])) { (gathered, _) =>
      for
        earlier <- gathered
        next <- layer(atoms ++ earlier.map(Instruction(_)), earlier)
      yield earlier :+ next
    }

  /** A layer over the given instructions, or a repeat of an earlier layer. */
  private def layer(instructions: Vector[Instruction], earlier: Vector[Layer[Instruction]]): Gen[Layer[Instruction]] =
    val child = Gen.element(instructions.head, instructions.tail.toList)
    val kinds = List(
      4 -> (for function <- child; argument <- child yield Apply(function, argument)),
      1 -> (for left <- child; right <- child yield Parallel(left, right)),
      1 -> (for left <- child; right <- child yield Choice(left, right)),
      3 -> thunk(child)
    )
    val fresh = Gen.frequency1(kinds.head, kinds.tail*)
    if earlier.isEmpty then fresh
    else Gen.frequency1(4 -> fresh, 1 -> Gen.element(earlier.head, earlier.tail.toList))

  /** A thunk: a code of `slotCounts`, one to three binders, the first k
    * bound to the slots k - 1 down to 0 and the rest ignored, and a filling
    * for every slot from k up.
    */
  private def thunk(child: Gen[Instruction]): Gen[Layer[Instruction]] =
    for
      (code, slots) <- Gen.element(slotCounts.head, slotCounts.tail.toList)
      binders <- Gen.int(Range.linear(1, 3))
      bound <- Gen.int(Range.constant(0, math.min(binders, slots)))
      fillings <- child.list(Range.singleton(slots - bound))
    yield Thunk(
      code,
      (0 until binders).toVector.map(position =>
        if position < bound then Hole.Bound(bound - 1 - position) else Hole.Ignored
      ),
      fillings.toVector
    )
