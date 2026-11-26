package gezi.jit

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.ir.Code
import gezi.ir.Instruction
import gezi.ir.Slot

/** The law of the readback's sharing (`JitValues`, SHARING): on a generated
  * value built as a chain of nodes each of which uses the node below it
  * twice or more (a graph of d + 1 nodes whose tree has about 2^d), and
  * holds no represented or `Evaluated` value, `encoded` followed by `plain`
  * and `fromValue`, read back to a plain value, is the same term as the
  * input read back, the same interned object. Its purpose is to catch a
  * conversion that walks a shared subvalue once per occurrence, which the
  * program of `ReductionMeaningsRepeated` at seed 568201625 turned into a
  * tree of 1.93e10 nodes and an exhausted heap (2026-11-01): every value
  * being interned, such a walk no longer builds the tree, but it still takes
  * time exponential in the chain's length, which the suite's time limit
  * catches at a chain of 80.
  */
class JitValuesSharingLawTest extends GeneratedProperties:

  /** One layer over the node below, which it uses at least twice, and a
    * leaf, by its kind: an application, a parallel, a choice or a thunk.
    */
  private def layer(kind: Int, below: JitValue, leaf: JitValue): JitValue = kind match
    case 0 => JitValue.Apply(below, below)
    case 1 => JitValue.Parallel(below, JitValue.Apply(below, leaf))
    case 2 => JitValue.Choice(Vector(below, JitValue.Choice(Vector(leaf, below))))
    case _ => JitValue.Thunk(Code(Slot(0)), Vector.empty, Vector(below, below, leaf))

  /** The chain of the layers of the kinds, bottom first, over an instruction. The
    * kinds are what the property draws and logs: the value's text is its
    * tree, too large to write.
    */
  private def chain(kinds: List[Int]): JitValue =
    val leaf: JitValue = Instruction.opaque("leaf")
    kinds.foldLeft(leaf: JitValue)((below, kind) => layer(kind, below, leaf))

  private def kinds(most: Int): Gen[List[Int]] = Gen.list(Gen.int(Range.constant(0, 3)), Range.linear(1, most))

  private def readBack(value: JitValue): gezi.weakhead.Value =
    JitValues.plain(JitValues.encoded(value, JitTesting.noFacts))

  property("the readback of a shared value read back again is the same term") {
    for drawn <- kinds(80).forAll
    yield
      val value = chain(drawn)
      val once = readBack(value)
      Result.assert(readBack(JitValues.fromValue(once)) eq once)
  }
