package gezi.ir

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The flat spine an application stores (`Apply.spineHead`,
  * `Apply.spineArguments`, read by `Spine`) on generated spines: a head that
  * is no application applied to 0 to 2,000 arguments, each argument itself
  * an opaque instruction or an application of one to another, so that
  * arguments that are applications are not taken into the spine.
  *
  * Purpose: catch a flat copy that differs from the spine the nested
  * applications spell (an argument lost, doubled, out of order, or taken
  * from inside an argument), and one made by recursing once per argument.
  */
class SpineLawTest extends GeneratedProperties:

  private val names: Gen[Instruction] = Gen.int(Range.linear(0, 50)).map(index => Instruction.opaque(s"name$index"))

  private val arguments: Gen[Instruction] =
    Gen.choice1(names, for function <- names; argument <- names yield Instruction.Apply(function, argument))

  private val heads: Gen[Instruction] =
    Gen.choice1(names, for left <- names; right <- names yield Instruction.Choice(left, right))

  property("an application's spine is its head and its arguments in order") {
    for
      head <- heads.forAll
      applied <- arguments.list(Range.linear(0, 2000)).forAll
    yield
      val term = applied.foldLeft(head)(Instruction.Apply(_, _))
      val (foundHead, foundArguments) = Spine.of(term)
      Result.all(List(
        Result.assert(foundHead eq head).log("the head"),
        Result.assert(foundArguments.size == applied.size && foundArguments.lazyZip(applied).forall(_ eq _)).log("the arguments"),
        Result.assert(Spine.unapplySeq(term).isDefined == applied.nonEmpty).log("an application, and only one, has a spine")
      ))
  }
