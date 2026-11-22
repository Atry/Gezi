package gezi.frontend

import gezi.ir.Instruction
import gezi.ir.Layer
import gezi.ir

/** The occurrence tagging of `Occurrences.tagged` (the module comment
  * of `gezi/prolog/gezi/surface.pl`, OCCURRENCES), on
  * hand-written generic markers.
  */
class OccurrencesTest extends gezi.generatedinputs.FailFastSuite:

  import DeBruijnTerm.*

  /** Five distinct closed terms interned, standing for the four markers and
    * one library name.
    */
  private val instructions =
    Vector(
      "λx.x",
      "λx.λy.x",
      "λx.λy.y",
      "λx.x x",
      "λx.λy.x y"
    ).map(text =>
      Defunctionalization.thunkInstruction(Lambdalattice.term(text))
    )

  private val Vector(name, closure, firstTag, nextTag, library) = instructions: @unchecked

  private val markers: OccurrenceMarkers = OccurrenceMarkers(name, closure, firstTag, nextTag)

  private def marked(marker: Instruction, tag: Instruction, term: DeBruijnTerm): DeBruijnTerm =
    Apply(Apply(Constant(marker), Constant(tag)), term)

  test("eachNameAndEachChainIsTaggedInPreorder") {
    // `f (λx. λy. x f)`, f the library name.
    val tagged = Occurrences.tagged(
      Apply(Constant(library), Lambda(Lambda(Apply(Variable(1), Constant(library))))),
      markers
    )
    val secondTag = Instruction(ir.Apply(nextTag, firstTag))
    val thirdTag = Instruction(ir.Apply(nextTag, secondTag))
    assertEquals(
      tagged,
      Apply(
        marked(name, firstTag, Constant(library)),
        marked(
          closure,
          secondTag,
          Lambda(Lambda(Apply(Variable(1), marked(name, thirdTag, Constant(library)))))
        )
      )
    )
  }
