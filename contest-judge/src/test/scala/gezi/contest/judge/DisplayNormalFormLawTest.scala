package gezi.contest.judge

import hedgehog.Gen
import hedgehog.Result
import gezi.frontend.DeBruijnTerm
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.GeneratedProperties
import gezi.generatedinputs.HoasGenerators

/** The law of the judge's normal form test on instructions
  * (`Display.normalForm`): an instruction is a normal form exactly when its
  * readback is a closed pure βη normal form, of variables, abstractions and
  * applications only, with no β redex and no η redex. The inputs are
  * generated closed terms of every construct, βη normal forms, terms with
  * an η redex, and each of them in a diamond `λf. f t t`, so that a filling
  * is read twice. Its purpose is to catch a test on the IR that reads
  * another term than the readback: a slot taken for a variable or for a
  * filling it is not, a β redex through a filling in head position missed,
  * an η redex whose binder an inner thunk reads through its fillings taken
  * for one, which would turn a remainder into a false positive or the
  * reverse.
  */
class DisplayNormalFormLawTest extends GeneratedProperties:

  /** The definition on the readback, recursive on its depth: for generated
    * terms of at most 50 nodes.
    */
  private def normalFormTerm(term: DeBruijnTerm): Boolean = term match
    case DeBruijnTerm.Variable(_) => true
    case DeBruijnTerm.Lambda(DeBruijnTerm.Apply(function, DeBruijnTerm.Variable(0))) if !occurs(function, 0) => false
    case DeBruijnTerm.Lambda(body)                       => normalFormTerm(body)
    case DeBruijnTerm.Apply(DeBruijnTerm.Lambda(_), _)   => false
    case DeBruijnTerm.Apply(function, argument)          => normalFormTerm(function) && normalFormTerm(argument)
    case _                                               => false

  private def occurs(term: DeBruijnTerm, index: Int): Boolean = term match
    case DeBruijnTerm.Variable(found)           => found == index
    case DeBruijnTerm.Lambda(body)              => occurs(body, index + 1)
    case DeBruijnTerm.Apply(function, argument) => occurs(function, index) || occurs(argument, index)
    case DeBruijnTerm.Choice(left, right)       => occurs(left, index) || occurs(right, index)
    case DeBruijnTerm.Parallel(left, right)     => occurs(left, index) || occurs(right, index)
    case _                                      => false

  private val terms: Gen[Term] =
    for
      term <- Gen.choice1(HoasGenerators.closedTerm, HoasGenerators.normalForm, HoasGenerators.etaRedexTerm)
      diamond <- Gen.boolean
    yield if diamond then Term.λ(function => function(term)(term)) else term

  property("an instruction is a normal form exactly when its readback is") {
    terms.forAll
      .cover(20, "a normal form", term => normalFormTerm(term.deBruijnTerm(Map.empty)))
      .cover(20, "no normal form", term => !normalFormTerm(term.deBruijnTerm(Map.empty)))
      .map(term =>
        val instruction = Defunctionalization.thunkInstruction(term.deBruijnTerm(Map.empty))
        Result
          .diff(Display.normalForm(instruction), normalFormTerm(Defunctionalization.instructionTerm(instruction)))(_ == _)
          .log(gezi.frontend.Lambdalattice.closedText(instruction))
      )
  }
