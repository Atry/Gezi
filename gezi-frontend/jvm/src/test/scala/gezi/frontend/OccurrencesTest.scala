package gezi.frontend

import gezi.ir.Configured
import gezi.ir.Layer
import gezi.ir.NativeSpecializer.*
import gezi.ir.NoFacts
import gezi.ir

/** The occurrence tagging of `Occurrences.tagged` (the module comment of
  * `gezi/prolog/gezi/surface.pl`, OCCURRENCES), on hand-written generic
  * markers.
  */
class OccurrencesTest extends gezi.generatedinputs.FailFastSuite:

  given NoFacts.type = NoFacts

  private type NoFactsTerm = Configured[NoFacts.type]

  import DeBruijnTerm.*

  /** Five distinct closed terms interned, standing for the four markers and one
    * library name.
    */
  private val pures =
    Vector(
      "λx.x",
      "λx.λy.x",
      "λx.λy.y",
      "λx.x x",
      "λx.λy.x y"
    ).map(text => Defunctionalization.pure(Lambdalattice.term(text)))

  private val Vector(name, closure, firstTag, nextTag, library)
      : Vector[NoFactsTerm] =
    pures.map(Configured.fromPure(NoFacts))

  private val markers: OccurrenceMarkers =
    OccurrenceMarkers(pures(0), pures(1), pures(2), pures(3))

  private def marked(
      marker: NoFactsTerm,
      tag: NoFactsTerm,
      term: DeBruijnTermOf[NoFactsTerm]
  ): DeBruijnTermOf[NoFactsTerm] =
    Apply(Apply(Constant(marker), Constant(tag)), term)

  test("eachNameAndEachChainIsTaggedInPreorder") {
    // `f (λx. λy. x f)`, f the library name.
    val tagged = Occurrences.tagged(
      Apply(
        Constant(library),
        Lambda(Lambda(Apply(Variable(1), Constant(library))))
      ),
      markers
    )
    val secondTag = NoFacts.application(nextTag, firstTag)
    val thirdTag = NoFacts.application(nextTag, secondTag)
    assertEquals(
      tagged,
      Apply(
        marked(name, firstTag, Constant(library)),
        marked(
          closure,
          secondTag,
          Lambda(
            Lambda(
              Apply(Variable(1), marked(name, thirdTag, Constant(library)))
            )
          )
        )
      )
    )
  }
