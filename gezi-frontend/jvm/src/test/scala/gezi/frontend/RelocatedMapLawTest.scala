package gezi.frontend

import hedgehog.Gen
import hedgehog.Result
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators
import gezi.generatedinputs.LambdalatticeText
import gezi.ir.Hole
import gezi.ir.Instruction
import gezi.locations.BinderOrigin
import gezi.locations.SourceMap

/** The law of `Defunctionalization.relocatedMap` on the residue of a β step:
  * a located text `(λx …. B) A` is read, the thunk the defunctionalized β
  * rule leaves (`Thunk(code, rest, fillings + A)`, as
  * `gezi.rewritetrace.Statements.fill` states it) is built with its map, the
  * thunk's own minus the first binder and the argument's added, and the map
  * is relocated onto the front end's spelling of the residue's readback,
  * which hoists the parts the argument made closed into fillings. Every
  * abstraction of the readback keeps the origins it had under the residue's
  * map, with any that equal subterms merged into one filling add.
  *
  * Purpose: catch a relocation that gives a binder another binder's origins
  * or none, that loses the origins of a filling the spelling hoists, or that
  * fails on a spelling whose fillings differ from the source's.
  */
class RelocatedMapLawTest extends GeneratedProperties:

  private val uri: java.net.URI = java.net.URI.create("file:///generated.lambdalattice")

  /** A closed abstraction applied to a closed term. */
  private val redexes: Gen[Term] =
    for
      body <- Gen.sized(size => HoasGenerators.openTerm(1, size.value / 2))
      argument <- HoasGenerators.closedTerm
    yield Term.Abstraction(bound => body(Vector(bound)))(argument)

  /** The origins of every abstraction of the map, by its path. */
  private def abstractionOrigins(map: TermMap): Vector[(Vector[Int], Set[BinderOrigin])] =
    def walked(current: TermMap, path: Vector[Int]): Vector[(Vector[Int], Set[BinderOrigin])] = current match
      case TermMap.Abstraction(_, origins, body) => (path, origins) +: walked(body, path :+ 0)
      case TermMap.Pair(_, left, right)          => walked(left, path :+ 0) ++ walked(right, path :+ 1)
      case _                                     => Vector.empty
    walked(map, Vector.empty)

  property("a β residue's map relocated onto its front end spelling keeps every binder's origins") {
    redexes.forAllWithLog(LambdalatticeText.text).map(redex =>
      val text = LambdalatticeText.text(redex)
      val read = Lambdalattice.located(text, FreeNames.Rejected)
      Defunctionalization.locatedThunkInstruction(read.term, read.spans, uri) match
        case (Instruction.Apply(Instruction.Thunk(code, hole +: rest, fillings), argument), map) =>
          val functionMap = map.children(0)
          val position = hole match
            case Hole.Bound(slot) => Some(Defunctionalization.fillingPosition(rest, slot))
            case Hole.Ignored     => None
          val residue = Instruction.Thunk(code, rest, position.fold(fillings)(at => fillings.patch(at, Vector(argument), 0)))
          val residueMap = SourceMap(
            functionMap.locations,
            functionMap.code,
            position.fold(functionMap.children)(at => functionMap.children.patch(at, Vector(map.children(1)), 0)),
            functionMap.binders.drop(1)
          )
          val (term, residueTermMap, _) = Defunctionalization.locatedInstructionTerm(residue, residueMap, Set.empty)
          val spelled = Defunctionalization.thunkInstruction(term)
          val (_, spelledTermMap, _) =
            Defunctionalization.locatedInstructionTerm(spelled, Defunctionalization.relocatedMap(residue, residueMap, spelled), Set.empty)
          val expected = abstractionOrigins(residueTermMap)
          val found = abstractionOrigins(spelledTermMap).toMap
          val lost = expected.filterNot((path, origins) => found.get(path).exists(origins.subsetOf))
          Result.assert(lost.isEmpty).log(s"residue $residue, spelled $spelled, lost $lost")
        case (other, _) => Result.failure.log(s"the redex read as no application of a thunk with a hole: $other")
    )
  }
