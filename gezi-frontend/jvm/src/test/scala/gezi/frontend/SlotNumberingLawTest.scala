package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The conversion on bodies around the number of slots at which it starts
  * indexing them. Its purpose is to catch a slot numbered wrongly below that
  * number, above it, or by an inner chain whose sources cross it: the
  * readback of the instruction would differ from the term.
  */
class SlotNumberingLawTest extends GeneratedProperties:

  given gezi.ir.NoFacts.type = gezi.ir.NoFacts

  /** The binders of the chain, the variables an inner chain reads (every
    * binder, from a generated one on, then some again) and the variables its
    * application reads, as indices of the outer chain's binders.
    */
  private val shapes =
    for
      binders <- Gen.int(Range.linear(24, 48))
      rotation <- Gen.int(Range.linear(0, binders - 1))
      again <- Gen.int(Range.linear(0, binders - 1)).list(Range.linear(0, binders))
      applied <- Gen.int(Range.linear(0, binders - 1)).list(Range.linear(0, binders))
    yield
      val every = (0 until binders).toList
      (binders, every.drop(rotation) ++ every.take(rotation) ++ again, applied)

  private def term(binders: Int, innerReads: List[Int], applied: List[Int]): DeBruijnTerm =
    val innerBody = innerReads.foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)((function, read) =>
      DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(read + 1))
    )
    val body = applied.foldLeft(DeBruijnTerm.Lambda(innerBody): DeBruijnTerm)((function, read) =>
      DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(read))
    )
    (0 until binders).foldLeft(body)((inner, _) => DeBruijnTerm.Lambda(inner))

  property("a term with an inner chain around the indexed size reads back as itself") {
    for shape <- shapes.forAll
    yield
      val written = term(shape._1, shape._2, shape._3)
      Result.diff(Defunctionalization.instructionTerm(Defunctionalization.thunkInstruction[gezi.ir.NoFacts.type](written)), written)(_ == _)
  }
