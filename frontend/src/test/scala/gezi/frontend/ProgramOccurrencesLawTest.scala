package gezi.frontend

import hedgehog.Gen
import hedgehog.Range
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.ir.Configured
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir.StorageAccess

/** The laws of the occurrence tagging of a program given as an instruction
  * (`ProgramOccurrences.tagged`), on generated instructions with shared parts
  * and on generic markers.
  */
class ProgramOccurrencesLawTest extends GeneratedProperties:

  given NoFacts.type = NoFacts
  given StorageAccess = StorageAccess.granted()

  private type NoFactsTerm = Configured[NoFacts.type]

  /** Four distinct closed terms standing for the markers and the tags. */
  private val Vector(namePure, closurePure, firstTagPure, nextTagPure) =
    Vector(
      "λa b c d e. e d c b a",
      "λa b c d e. d e c b a",
      "λa b c d e. c e d b a",
      "λa b c d e. b e d c a"
    )
      .map(text =>
        Defunctionalization.pure(Lambdalattice.term(text))
      ): @unchecked

  private val markers: OccurrenceMarkers =
    OccurrenceMarkers(namePure, closurePure, firstTagPure, nextTagPure)

  private val Vector(name, closure, firstTag, nextTag): Vector[NoFactsTerm] =
    Vector(namePure, closurePure, firstTagPure, nextTagPure).map(
      Configured.fromPure(NoFacts)
    )

  private val markerInstructions: Set[NoFactsTerm] =
    Set(name, closure, firstTag, nextTag)

  /** The term with each tagging `M T x`, M the name or the closure marker,
    * replaced by x.
    */
  private def erased(
      term: DeBruijnTermOf[NoFactsTerm]
  ): DeBruijnTermOf[NoFactsTerm] = term match
    case DeBruijnTerm.Apply(
          DeBruijnTerm.Apply(DeBruijnTerm.Constant(marker), _),
          tagged
        )
        if Configured.same(marker, name) || Configured.same(marker, closure) =>
      erased(tagged)
    case DeBruijnTerm.Lambda(body) => DeBruijnTerm.Lambda(erased(body))
    case DeBruijnTerm.Apply(function, argument) =>
      DeBruijnTerm.Apply(erased(function), erased(argument))
    case DeBruijnTerm.Parallel(left, right) =>
      DeBruijnTerm.Parallel(erased(left), erased(right))
    case DeBruijnTerm.Choice(left, right) =>
      DeBruijnTerm.Choice(erased(left), erased(right))
    case other => other

  /** The program's full readback, the markers and the kept parts left as
    * constants.
    */
  private def readback(
      program: NoFactsTerm,
      kept: Set[NoFactsTerm]
  ): DeBruijnTermOf[NoFactsTerm] =
    Defunctionalization.instructionTerm(program, markerInstructions ++ kept)

  /** The distinct instructions under the root, the root included. */
  private def nodes(root: NoFactsTerm): Int = ReadableText.counted(root)._2.size

  /** The kept parts drawn from the program's own instructions. */
  private def keptParts(program: NoFactsTerm): Gen[Set[NoFactsTerm]] =
    val parts =
      ReadableText.counted(program)._2.filterNot(Configured.same(_, program))
    parts match
      case first +: rest =>
        Gen.element(first, rest.toList).list(Range.linear(0, 3)).map(_.toSet)
      case _ => Gen.constant(Set.empty)

  /** Catches a tagging that changes the program rather than marking it: a
    * shared part read back wrongly, a tagged part put in place of another, a
    * kept part tagged inside.
    */
  property("the tagging erased is the program") {
    for
      program <- HoasGenerators.instruction.forAll
      kept <- keptParts(program).forAll
    yield
      val tagged = ProgramOccurrences.tagged(program, kept, markers)
      Result.diff(
        erased(readback(tagged, kept)),
        erased(readback(program, kept))
      )(_ == _)
  }

  /** Catches a tagging that reads a shared part back at each of its references:
    * on a chain of d applications of a part to itself, whose full readback has
    * 2^d leaves, the tagged program keeps a number of instructions linear in
    * the program's.
    */
  property("the tagged program is linear in the program's instruction graph") {
    for
      start <- HoasGenerators.instruction.forAll
      depth <- Gen.int(Range.linear(1, 40)).forAll
    yield
      val program = (1 to depth).foldLeft(start)((part, _) =>
        NoFacts.application(part, part)
      )
      val tagged = ProgramOccurrences.tagged(program, Set.empty, markers)
      Result
        .assert(nodes(tagged) <= 12 * nodes(program) + 12)
        .log(
          s"${nodes(program)} instructions, ${nodes(tagged)} tagged, depth $depth"
        )
  }
