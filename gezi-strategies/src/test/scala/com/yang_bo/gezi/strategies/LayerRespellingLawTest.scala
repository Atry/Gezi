package com.yang_bo.gezi.strategies

import hedgehog.Result
import com.yang_bo.gezi.egraph.Respelling
import com.yang_bo.gezi.generatedinputs.GeneratedProperties
import com.yang_bo.gezi.generatedinputs.HoasGenerators
import com.yang_bo.gezi.ir.Configured
import com.yang_bo.gezi.ir.NoFacts
import com.yang_bo.gezi.ir.Thunk

/** The law that the e-graph's respelling of a thunk layer
  * (`com.yang_bo.gezi.egraph.Respelling`, called by `EGraph.layerMade`) leaves every thunk
  * the front end spells as it is: each thunk layer with holes of the front
  * end's instruction of a generated closed term, its fillings standing as
  * placeholders, is `Respelling.Canonical`.
  *
  * Purpose: catch a respelling that changes a layer of an input program or of a
  * library term, which come from the front end whole: the graph would then hold
  * another spelling of a program than the program, and a trace would start from
  * a term the graph has no node of. A lemma's side is not covered: its encoding
  * splits a thunk into its metavariables' fillings and the holes left, which
  * need not be the front end's spelling
  * (`com.yang_bo.gezi.rewritetrace.Conversions.instanceBindings`).
  */
class LayerRespellingLawTest extends GeneratedProperties:

  private def thunkLayers(
      instruction: Configured[NoFacts.type]
  ): Vector[Thunk[Configured[NoFacts.type]]] =
    if instruction.opaque then Vector.empty
    else
      val own = instruction.layer match
        case thunk @ Thunk(_, holes, _) if holes.nonEmpty => Vector(thunk)
        case _                                            => Vector.empty
      own ++ instruction.layer.children.flatMap(thunkLayers)

  property("every thunk layer the front end spells is its own respelling") {
    for root <- HoasGenerators.instruction.forAll
    yield
      val changed = thunkLayers(root).filter(thunk =>
        Respelling.of(
          Respelling.Key(thunk.code, thunk.holes, thunk.fillings.size)
        ) != Respelling.Canonical
      )
      Result
        .assert(changed.isEmpty)
        .log(
          s"${changed.size} of ${thunkLayers(root).size} thunk layers respelled: $changed"
        )
  }
