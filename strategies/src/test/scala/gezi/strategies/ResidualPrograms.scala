package gezi.strategies

import hedgehog.Gen
import hedgehog.Range
import gezi.frontend.Defunctionalization
import gezi.frontend.Term
import gezi.generatedinputs.HoasGenerators
import gezi.ir.BindingNormalForm
import gezi.ir.Instruction
import gezi.rewritetrace.Statements

/** Programs whose β residuals are not their own spelling, shared by the
  * replay spelling and trace laws (`ReplaySpellingLawTest`, `RewriteTraceLawTest`).
  */
object ResidualPrograms:

  /** A lambda of two or three binders whose body is the choice of `z (x C)`
    * (x the first binder, z the last, C a generated closed term) and a
    * generated term under the binders: filling the first hole of its thunk
    * leaves `x C` inline though it reads no binder once x is filled, which
    * the front end makes one filling.
    */
  val lambdas: Gen[Term] =
    for
      count <- Gen.int(Range.linear(2, 3))
      body <- Gen.sized(size => HoasGenerators.openTerm(count, size.value / 2))
      constant <- HoasGenerators.closedTerm
    yield
      def under(outer: Vector[Term]): Term =
        if outer.size == count then Term.choice(outer.last(outer.head(constant)), body(outer))
        else Term.λ(bound => under(outer :+ bound))
      under(Vector.empty)

  /** The front end's thunks of `lambdas`. */
  val thunks: Gen[Instruction] =
    lambdas.map(lambda => Defunctionalization.thunkInstruction(lambda.deBruijnTerm(Map.empty)))

  /** The thunk the defunctionalized β rule leaves when the argument fills
    * the thunk's first hole (`Statements.fill`), as the rule states it, not
    * respelled.
    */
  def residual(thunk: Instruction, argument: Instruction): Instruction = thunk match
    case Instruction.Thunk(code, holes, _) =>
      val equation = Statements.fill(code, holes)
      Statements.instance(equation.right, Statements.bindings(equation.left, Instruction.Apply(thunk, argument)))
    case other => throw IllegalArgumentException(s"no thunk: $other")

  /** The thunks with holes of the term that are not their own respelling
    * (`gezi.ir.BindingNormalForm.respelled`), each distinct subterm
    * once.
    */
  def respellable(term: Instruction): Set[Instruction] =
    @scala.annotation.tailrec
    def found(pending: List[Instruction], seen: Set[Instruction], gathered: Set[Instruction]): Set[Instruction] =
      pending match
        case Nil                                              => gathered
        case next :: rest if seen(next) || next.opaque        => found(rest, seen, gathered)
        case next :: rest =>
          val here = next.layered match
            case gezi.ir.Thunk(code, holes, fillings) =>
              holes.nonEmpty && BindingNormalForm.respelled(code, holes, fillings.size).isDefined
            case _ => false
          found(next.layered.children.toList ::: rest, seen + next, if here then gathered + next else gathered)
    found(List(term), Set.empty, Set.empty)
