package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties

/** The law that the conversion reads a closed subterm once, however many places
  * of a body write it. Its purpose is to catch the annotation walking a shared
  * closed subterm again at each occurrence, which made the `top` at every bit
  * of a literal binder the largest part of converting a directory entry.
  */
class ClosedSubtermAnnotationLawTest extends GeneratedProperties:

  /** A closed term of about `size` nodes: `λf. λx. f (f (… x))`. */
  private def closedTerm(size: Int): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      DeBruijnTerm.Lambda(
        (1 to size).foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)(
          (argument, _) =>
            DeBruijnTerm.Apply(DeBruijnTerm.Variable(1), argument)
        )
      )
    )

  /** `λy. y C … C`, the closed term written at each of the places. */
  private def written(closed: DeBruijnTerm, places: Int): DeBruijnTerm =
    DeBruijnTerm.Lambda(
      (1 to places).foldLeft(DeBruijnTerm.Variable(0): DeBruijnTerm)(
        (function, _) => DeBruijnTerm.Apply(function, closed)
      )
    )

  private def operations(term: DeBruijnTerm): Long = Defunctionalization
    .thunkInstructionCounted(term)(using gezi.ir.NoFacts)
    .operations

  /** What a larger closed subterm adds to the conversion at the places. */
  private def addedBySize(size: Int, places: Int): Long =
    operations(written(closedTerm(size), places)) - operations(
      written(closedTerm(1), places)
    )

  property("a larger closed subterm adds as much at many places as at one") {
    for
      size <- Gen.int(Range.linear(2, 40)).forAll
      places <- Gen.int(Range.linear(2, 12)).forAll
    yield Result.diff(addedBySize(size, places), addedBySize(size, 1))(_ == _)
  }
